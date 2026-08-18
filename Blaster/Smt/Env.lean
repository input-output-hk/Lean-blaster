import Lean
import Blaster.Command.Options
import Blaster.Optimize.Env
import Blaster.Smt.EmitCommand
import Blaster.Smt.Model

open Lean Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

/-- Normalize solver output line endings: strip any `\r` so that downstream
    code only sees Unix-style `\n` terminators, regardless of platform. -/
private def normalizeLine (s : String) : String :=
  s.replace "\r" ""

/-- One executable launch candidate. `cmd` is exactly one executable name;
    wrapper subcommands such as WSL's solver name belong in `prefixArgs`. -/
structure SolverCandidate where
  cmd : String
  prefixArgs : Array String := #[]
deriving Repr, BEq, Inhabited

/-- Human-readable candidate spelling used only in diagnostics. -/
def SolverCandidate.display (candidate : SolverCandidate) : String :=
  String.intercalate " " (candidate.cmd :: candidate.prefixArgs.toList)

/-- Static description of a supported backend solver executable. -/
structure SolverDescriptor where
  /-- Display name of the solver. -/
  name : String
  /-- Launch candidates probed in order (Windows support goes through WSL). -/
  candidates : Array SolverCandidate
  /-- Arguments used to probe the executable and query its version. -/
  versionArgs : Array String
  /-- Minimal version of the solver we support. -/
  minVersion : String
  /-- Arguments used to spawn the solver reading SMT-LIB commands from stdin. -/
  spawnArgs : Array String

/-- Exact executable and argv used to probe a candidate's version. -/
def SolverDescriptor.probeInvocation (desc : SolverDescriptor) (candidate : SolverCandidate) :
    String × Array String :=
  (candidate.cmd, candidate.prefixArgs ++ desc.versionArgs)

/-- Exact executable and argv used to start a candidate as an SMT process. -/
def SolverDescriptor.spawnInvocation (desc : SolverDescriptor) (candidate : SolverCandidate) :
    String × Array String :=
  (candidate.cmd, candidate.prefixArgs ++ desc.spawnArgs)

/-- Per-solver executable description.
    NOTE: cvc5 is spawned with `--parsing-mode=lenient` because Blaster emits
    `@`-prefixed symbols (e.g. `@isNat`), which strict SMT-LIB parsing reserves
    for solver-internal use. `--incremental` is required for `check-sat-assuming`
    based strategies (BMC/K-Induction). `--dt-nested-rec` enables (experimental)
    support for nested recursive datatypes (e.g. a constructor taking a
    `(List Term)` argument), which cvc5 rejects by default whereas z3 accepts.
    NOTE: Blaster enforces and smoke-tests cvc5 1.2.1 as the minimum supported
    version; the required spawn arguments and SMT-LIB options work there. -/
def _root_.Blaster.Options.SmtSolver.descriptor : SmtSolver → SolverDescriptor
  | .z3 =>
     { name := "z3",
       candidates := #[{ cmd := "z3" }, { cmd := "wsl", prefixArgs := #["z3"] }],
       versionArgs := #["-version"],
       minVersion := "4.15.2",
       spawnArgs := #["-in", "-smt2"] }
  | .cvc5 =>
     { name := "cvc5",
       candidates := #[{ cmd := "cvc5" }, { cmd := "wsl", prefixArgs := #["cvc5"] }],
       versionArgs := #["--version"],
       minVersion := "1.2.1",
       spawnArgs := #["--lang", "smt2", "--incremental", "--parsing-mode=lenient", "--dt-nested-rec"] }

/-- Result of an Smt query. -/
inductive Result where
  | Valid  : Result
  | Falsified (cex : List String) : Result
  | Undetermined : Result
deriving Repr

def toResult (e : Expr) : Result :=
 match e with
 | Expr.const ``True _  => Result.Valid
 | Expr.const ``False _  => Result.Falsified []
 | _ => Result.Undetermined


def isValidResult (r : Result) : Bool :=
  match r with
  | .Valid => true
  | _ => false

def isFalsifiedResult (r : Result) : Bool :=
  match r with
  | .Falsified _ => true
  | _ => false

def isUndeterminedResult (r : Result) : Bool :=
  match r with
  | .Undetermined => true
  | _ => false

def falsifiedError (r : Result) : String :=
  s!"Falsified result expected but got {reprStr r}"


/-- Whether strict cvc5 test conformance was requested for this process. -/
def strictCvc5ResultCheckingRequested : IO Bool := do
  let some value ← IO.getEnv "BLASTER_STRICT_CVC5_RESULTS" | return false
  if value == "" || value == "0" then return false
  if value == "1" then return true
  throw <| IO.userError
    s!"❌ Invalid BLASTER_STRICT_CVC5_RESULTS value '{value}' (expected '0' or '1')."

/-- How a declared result contract handles an `Undetermined` outcome. -/
inductive UndeterminedAction where
  | expected
  | allowed
  | strictError
  | warning
deriving Repr, BEq, DecidableEq

/-- Decide `Undetermined` handling without logging or consulting process state. -/
def undeterminedAction
    (sOpts : BlasterOptions) (solver : SmtSolver) (strictRequested : Bool) :
    UndeterminedAction :=
  if isExpectedUndetermined sOpts.solveResult then .expected
  else if sOpts.allowCvc5Undetermined && solver == .cvc5 then .allowed
  else if strictRequested && solver == .cvc5 then .strictError
  else .warning

def blankRef : TranslateEnvT Syntax := getRef

def logResult (r : Result) (isCTI := false) (indLabel := "") (cexLabel := "Counterexample") : TranslateEnvT Unit := do
  let env ← get
  let sOpts := env.optEnv.options.solverOptions
  let action := undeterminedAction sOpts env.smtEnv.solver
    (← strictCvc5ResultCheckingRequested)
  let ref ← blankRef
  match r with
  | .Valid =>
      if isExpectedValid sOpts.solveResult
      then logInfoAt ref "✅ Valid"
      else logErrorAt ref "❌ Unexpected Valid"
  | .Falsified cex =>
      if isCTI
      then dumpCex (logInfoAt ref) indLabel cex
      else if isExpectedFalsified sOpts.solveResult
           then dumpCex (logInfoAt ref) "✅ Expected Falsified" cex
           else dumpCex (logErrorAt ref) "❌ Falsified" cex
  | .Undetermined =>
      match action with
      | .expected => logInfoAt ref "✅ Expected Undetermined"
      | .allowed => logInfoAt ref "✅ Allowed cvc5 Undetermined"
      | .strictError => logErrorAt ref "❌ Unexpected Undetermined"
      | .warning => logWarningAt ref "⚠️ Undetermined"

  where
    dumpCex (f : MessageData -> MetaM Unit) (failure : String) (cex : List String) : TranslateEnvT Unit := do
      if (← get).optEnv.options.solverOptions.generateCex then
         f failure
         f s!"{cexLabel}:"
         cex.forM (λ s => f s!" - {s.trimRight}")
      else f failure

/-- Numeric components of the first dotted version number (e.g. `4.15.2`)
    occurring in a solver's version banner; `none` when no such token exists. -/
def parseVersionNumbers (banner : String) : Option (List Nat) :=
  ((banner.split Char.isWhitespace).filterMap versionToken).head?
 where
  versionToken (tok : String) : Option (List Nat) :=
    let tok := tok.takeWhile (λ c => c.isDigit || c == '.')
    if tok.isEmpty || !tok.contains '.' then none
    else (tok.split (· == '.')).mapM String.toNat?

/-- `a` is at least `b` where both are dotted-version components; missing
    components count as zero (so `1.2` and `1.2.0` compare equal). -/
def versionAtLeast : (a b : List Nat) → Bool
  | _, [] => true
  | [], b => b.all (· == 0)
  | x :: xs, y :: ys => x > y || (x == y && versionAtLeast xs ys)

/-- Verdict of checking a solver's version banner against the minimal
    supported version. -/
inductive VersionCheck where
  | ok
  /-- The banner parsed but the version is below the minimal supported one. -/
  | tooOld (found : List Nat)
  /-- No dotted version number could be found in the banner. -/
  | unparseable
deriving Repr, DecidableEq

/-- Check a solver's version `banner` against `minVersion`.
    Fails closed: a banner without a parseable version is rejected
    (`.unparseable`) rather than accepted as an unknown solver build, since
    accepting an executable whose version cannot be established risks
    silently wrong solver behavior. Official z3/cvc5 banners — including dev
    builds, whose `1.3.5-dev.105` style tokens parse up to the suffix — all
    carry a parseable version.
    An unparseable `minVersion` (a Blaster bug, not a user error) imposes no
    lower bound instead of rejecting every solver. -/
def checkVersionBanner (minVersion : String) (banner : String) : VersionCheck :=
  let required := (parseVersionNumbers minVersion).getD []
  match parseVersionNumbers banner with
  | none => .unparseable
  | some found => if versionAtLeast found required then .ok else .tooOld found

/-- Outcome of probing one solver-executable candidate with its version
    arguments. Pure data so that the acceptance policy can be unit-tested
    without spawning processes (see `evalCandidateProbe`). -/
inductive ProbeOutcome where
  /-- The probe ran and exited with `exitCode`, producing `stdout`. -/
  | ran (exitCode : UInt32) (stdout : String)
  /-- The probe could not run at all (e.g. executable not found). -/
  | failed (error : String)
deriving Repr

/-- First line of the probe's stdout (the solver's version banner). -/
def ProbeOutcome.banner : ProbeOutcome → String
  | .ran _ stdout => ((stdout.splitOn "\n").headD "").trimRight
  | .failed _ => ""

/-- Verdict for one candidate probe: accept the candidate, or produce the
    human-readable rejection reason (one line of the discovery report).
    This is the single acceptance-policy point shared by solver discovery
    (`findSolverCandidateAndVersion`) and the `solvercheck` executable. -/
def evalCandidateProbe (desc : SolverDescriptor) (candidate : SolverCandidate) :
    ProbeOutcome → Except String Unit
  | .failed err => .error s!"Candidate '{candidate.display}': IO error => {err}"
  | outcome@(.ran exitCode _) =>
      if exitCode != 0 then
        .error s!"Candidate '{candidate.display}': exit code {exitCode}"
      else
        match checkVersionBanner desc.minVersion outcome.banner with
        | .ok => .ok ()
        | .tooOld found =>
            .error s!"Candidate '{candidate.display}': version {String.intercalate "." (found.map toString)} is older than the minimal supported {desc.minVersion}"
        | .unparseable =>
            .error s!"Candidate '{candidate.display}': could not parse a version from '{outcome.banner}' (unrecognized {desc.name} builds are rejected; version ≥ {desc.minVersion} is required)"

/-- Run one candidate's version probe, capturing failures to spawn (e.g.
    executable not found) as data. -/
def probeSolverCandidate (desc : SolverDescriptor) (candidate : SolverCandidate) : IO ProbeOutcome := do
  let (cmd, args) := desc.probeInvocation candidate
  try
    let out ← IO.Process.output { cmd := cmd, args := args }
    return .ran out.exitCode out.stdout
  catch e =>
    return .failed (toString e)

/-- Find a usable solver launch specification: candidates are probed in order
    (native executable first, then a best-effort WSL fallback) and the first
    one passing the version policy (see `evalCandidateProbe`) wins. -/
private def findSolverCandidateAndVersion (solver : SmtSolver) : IO SolverCandidate := do
  let desc := solver.descriptor
  let mut attemptLogs := #[]
  for candidate in desc.candidates do
    match evalCandidateProbe desc candidate (← probeSolverCandidate desc candidate) with
    | .ok () => return candidate
    | .error log => attemptLogs := attemptLogs.push log
  -- If we get here, no candidate succeeded
  let attemptsReport := String.join (attemptLogs.toList.map (fun x => x ++ "\n"))
  throw <| IO.userError s!"❌ Could not find a working {desc.name} ≥ {desc.minVersion}.\n\nTried:\n{attemptsReport}"

/-- Resolve a solver from an explicit option and a supplied environment value.
    Surrounding whitespace is ignored, but solver names are case-sensitive. -/
def resolveSolverConfig
    (sOpts : BlasterOptions) (envValue : Option String) : Except String SmtSolver := do
  if let some solver := sOpts.solver then return solver
  let some str := envValue | return .z3
  let some solver := SmtSolver.ofString? str.trim
    | throw s!"❌ Unknown BLASTER_SOLVER value '{str}' (expected 'z3' or 'cvc5')."
  return solver

/-- Resolve the backend solver to be used from the explicit option, then the
    process environment, then the Z3 default. -/
def resolveSolver (sOpts : BlasterOptions) : IO SmtSolver := do
  match resolveSolverConfig sOpts (← IO.getEnv "BLASTER_SOLVER") with
  | .ok solver => return solver
  | .error message => throw <| IO.userError message

/-- Resolve a timeout from an explicit option and a supplied environment value.
    Surrounding whitespace is ignored; an unset or whitespace-only value means
    no timeout, while any other value must be a natural number of seconds. -/
def resolveTimeoutConfig
    (sOpts : BlasterOptions) (envValue : Option String) : Except String (Option Nat) := do
  if let some timeout := sOpts.timeout then return some timeout
  let some str := envValue | return none
  let value := str.trim
  if value.isEmpty then return none
  let some timeout := value.toNat?
    | throw s!"❌ Invalid BLASTER_TIMEOUT value '{str}' (expected a number of seconds)."
  return some timeout

/-- Resolve the solving timeout from the explicit option, then the process
    environment, then the unlimited default. -/
def resolveTimeout (sOpts : BlasterOptions) : IO (Option Nat) := do
  match resolveTimeoutConfig sOpts (← IO.getEnv "BLASTER_TIMEOUT") with
  | .ok timeout => return timeout
  | .error message => throw <| IO.userError message

/-- Spawn a solver process w.r.t. the provided backend solver. -/
def createBlasterProcess (solver : SmtSolver) : IO (IO.Process.Child ⟨.piped, .piped, .piped⟩) := do
  let desc := solver.descriptor
  let candidate ← findSolverCandidateAndVersion solver  -- ensures version is OK
  let (cmd, args) := desc.spawnInvocation candidate
  IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := cmd
    args   := args
  }

/-- Return the backend solver in use (see `resolveSolver` and `setBlasterProcess`). -/
def getSolver : TranslateEnvT SmtSolver :=
  return (← get).smtEnv.solver

/-- Update translation cache with `a := b`.
-/
def updateTranslateCache (a : Expr) (b : SmtTerm) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.translateCache := env.smtEnv.translateCache.insert a b})


/-- Return `b` if `a := b` is already in the translation cache.
    Otherwise, the following actions are performed:
      - execute `b ← fun ()`
      - update cache with `a := b`
      - return b
-/
def withTranslateEnvCache (a : Expr) (f : Unit → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let env ← get
  match env.smtEnv.translateCache.get? a with
  | some b => return b
  | none => do
     let b ← f ()
     updateTranslateCache a b
     return b

/-- Check if cancel token has been triggered and kill corresponding running
    Solver instance (if necessary).
-/
def checkCancelTk? : TranslateEnvT Unit := do
  let some p := (← get).smtEnv.smtProc | return ()
  if let some tk := (← readThe Core.Context).cancelTk? then
    if ← tk.isSet then
      p.kill
      discard $ p.wait
      throwInterruptException

/-- Retire the solver process and drain whatever it wrote to stderr. This error
    path owns process cleanup: clearing `smtProc` before raising the contextual
    error prevents `throwEnvError` from killing or waiting for
    the same child again. An exited child needs neither operation; if it exits
    between `tryWait` and `kill`, the failed kill is harmless and one wait
    still reaps it. -/
private def killAndDrainStderr : TranslateEnvT String := do
  let some p := (← get).smtEnv.smtProc | return ""
  modify fun env => { env with smtEnv.smtProc := none }
  let shouldTerminate ←
    try pure (← p.tryWait).isNone
    catch _ => pure false
  if shouldTerminate then
    try p.kill catch _ => pure ()
    try discard p.wait catch _ => pure ()
  return (← p.stderr.readToEnd).trim

/-- Render drained stderr for inclusion in an error message (empty when the
    solver wrote nothing). -/
private def stderrNote (stderr : String) : String :=
  if stderr.isEmpty then "" else s!"\nSolver stderr:\n{stderr}"

/-- State used when scanning a solver response for balanced parentheses.
    Parentheses occurring inside string literals (`"…"`) and quoted symbols
    (`|…|`) are not counted.
-/
private structure SexpScanState where
  depth : Int := 0
  seenParen : Bool := false
  inString : Bool := false
  inQuotedSym : Bool := false

/-- Feed one line of solver output to the parenthesis scanner.
    NOTE: SMT-LIB escapes a quote inside a string literal by doubling it (`""`).
    Treating the doubled quote as close-then-reopen leaves the scanner in the
    correct state without lookahead.
-/
private def scanSexpLine (st : SexpScanState) (s : String) : SexpScanState :=
  s.foldl (λ st c =>
    if st.inString then
      if c == '"' then { st with inString := false } else st
    else if st.inQuotedSym then
      if c == '|' then { st with inQuotedSym := false } else st
    else match c with
      | '"' => { st with inString := true }
      | '|' => { st with inQuotedSym := true }
      | '(' => { st with depth := st.depth + 1, seenParen := true }
      | ')' => { st with depth := st.depth - 1 }
      | _ => st) st

private def SexpScanState.isBalanced (st : SexpScanState) : Bool :=
  st.seenParen && st.depth == 0

/-- Retrieve a model (or proof) response from `h`.
    A model response (`(get-model)`) is a single S-expression, possibly
    spanning several lines: reading stops when parentheses tally to zero
    (parentheses inside string literals and quoted symbols are not counted),
    so single-line responses — including `(error "…")` reports — terminate
    instead of waiting for closing lines that will never come.
    A proof response (z3) is terminated by an empty line instead.
    Line endings are normalized to handle both Unix (LF) and Windows (CRLF).
    NOTE: `getLine` returning the empty string means the solver closed its
    output stream (e.g. it crashed mid-response): fail — surfacing the
    solver's stderr — instead of spinning on a response that can never
    complete.
-/
partial def getOutputModel (h : IO.FS.Handle) (proof := false) : TranslateEnvT String := do
  let rec loop (acc : String) (st : SexpScanState) : TranslateEnvT String := do
    checkCancelTk?
    let line := normalizeLine (← h.getLine)
    if line.isEmpty then
      let stderr ← killAndDrainStderr
      throwEnvError s!"The solver closed its output stream while a model/proof response was pending.{stderrNote stderr}"
    if proof then
      if line == "\n" then return acc else loop (acc ++ line) st
    else
      let st := scanSexpLine st line
      let acc := acc ++ line
      if st.isBalanced then return acc else loop acc st
  loop "" {}

/-- Retrieve proof output for an `unsat` result.
    NOTE: A proof output starts with "(proof" and ends with ")\n\n".
    Line endings are normalized to handle both Unix (LF) and Windows (CRLF).
-/
def getOutputProof := λ h => getOutputModel h true

/-- Retrieve error msg from 'h'.
    NOTE: An error msg starts with "(error" and ends with ")\n".
    Line endings are normalized to handle both Unix (LF) and Windows (CRLF).
-/
partial def getErrorMsg (h : IO.FS.Handle) : IO String := normalizeLine <$> h.getLine


/-- Retrieve a `get-value` response from `h` after executing `(get-value (t))`.
    The response has the form `((t v))` and may span several lines when `v` is
    an inductive datatype value. Reading stops when parentheses tally to zero.
    NOTE: `getLine` returning the empty string means the solver closed its
    output stream (e.g. it crashed mid-response): fail instead of spinning on
    a response that can never complete.
-/
partial def getOutputGetValue (h : IO.FS.Handle) : IO String := do
  let line := normalizeLine (← h.getLine)
  if line.isEmpty then throw eofError
  if line.get! 0 != '(' then return line
  loop line (scanSexpLine {} line)

 where
  eofError : IO.Error := .userError
    "❌ The solver closed its output stream while a get-value response was pending."

  loop (acc : String) (st : SexpScanState) : IO String := do
    if st.isBalanced then return acc
    else
      let line := normalizeLine (← h.getLine)
      if line.isEmpty then throw eofError
      loop (acc ++ line) (scanSexpLine st line)

/-- Drop one S-expression (atom, string literal, quoted symbol or
    parenthesized expression) from the front of `cs`.
-/
private partial def dropSexp (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '(' :: rest => dropParen rest 1
  | '"' :: rest => dropDelimited rest '"'
  | '|' :: rest => dropDelimited rest '|'
  | _ :: _ => cs.dropWhile (λ c => !c.isWhitespace && c != '(' && c != ')')

 where
  dropParen (cs : List Char) (depth : Nat) : List Char :=
    match cs with
    | [] => []
    | '"' :: rest => dropParen (dropDelimited rest '"') depth
    | '|' :: rest => dropParen (dropDelimited rest '|') depth
    | '(' :: rest => dropParen rest (depth + 1)
    | ')' :: rest => if depth == 1 then rest else dropParen rest (depth - 1)
    | _ :: rest => dropParen rest depth
  dropDelimited (cs : List Char) (delim : Char) : List Char :=
    match cs with
    | [] => []
    | c :: rest => if c == delim then rest else dropDelimited rest delim

/-- Extract the value `v` from a `get-value` response of the form `((t v))`.
    The result is trimmed. When the response does not have the expected shape
    (e.g. an error), it is returned unchanged (trimmed) so that it can be
    reported as-is.
-/
partial def unwrapGetValueOutput (s : String) : String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  match cs with
  | '(' :: rest =>
      match rest.dropWhile Char.isWhitespace with
      | '(' :: inner =>
          -- drop the echoed term, the remainder up to the innermost closing
          -- parenthesis is the value
          let afterTerm := dropSexp (inner.dropWhile Char.isWhitespace)
          let value := takeValue afterTerm 0 []
          String.mk value |>.trim
      | _ => s.trim
  | _ => s.trim

 where
  takeValue (cs : List Char) (depth : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '(' :: rest => takeValue rest (depth + 1) ('(' :: acc)
    | ')' :: rest =>
        if depth == 0 then acc.reverse else takeValue rest (depth - 1) (')' :: acc)
    | '"' :: rest =>
        let (chunk, rest) := takeDelimited rest '"' ['"']
        takeValue rest depth (chunk ++ acc)
    | '|' :: rest =>
        let (chunk, rest) := takeDelimited rest '|' ['|']
        takeValue rest depth (chunk ++ acc)
    | c :: rest => takeValue rest depth (c :: acc)
  -- returns the delimited chunk in reverse order together with the remainder
  takeDelimited (cs : List Char) (delim : Char) (acc : List Char) : List Char × List Char :=
    match cs with
    | [] => (acc, [])
    | c :: rest =>
        if c == delim then (c :: acc, rest)
        else takeDelimited rest delim (c :: acc)

/-- Push smt command `c` in the translation environment only when sOpts.dumpSmtLib is set -/
def storeCommand (c : SmtCommand) : TranslateEnvT Unit := do
  if (← get).optEnv.options.solverOptions.dumpSmtLib then
    modify (fun env => { env with smtEnv.smtCommands := env.smtEnv.smtCommands.push c })
  else pure ()

/-- Return `true` when the smtProc has been initialized -/
def isSmtProcSet : TranslateEnvT Bool :=
  return (← get).smtEnv.smtProc.isSome

/-- Push smt command `c` in the translation environment only when sOpts.dumpSmtLib is set.
    The command is piped to the backend solver if the corresponding process has been created.
    An error is triggered when the `checkSuccess` flag is set and
    not `success` output is produced.
    NOTE: The `checkSuccess` is to be set only for Smt command that
    are NOT expected to produce any output.
-/
partial def trySubmitCommand! (c : SmtCommand) (checkSuccess := true) : TranslateEnvT Unit := do
  storeCommand c
  if !(← isSmtProcSet) then return ()
  c.emit
  let h ← getProcStdOut
  if !checkSuccess then return ()
  let out := normalizeLine (← h.getLine)
  match out with
  | "success\n" => return ()
  | "" =>
      let stderr ← killAndDrainStderr
      throwEnvError s!"The solver closed its output stream while executing {c}.{stderrNote stderr}"
  | err => throwEnvError s!"Unexpected smt error: {err} for {c}"

/-- Same as trySubmitCommand! but with flag `checkSuccess` set to `false`.
-/
def submitCommand (c : SmtCommand) : TranslateEnvT Unit := do
  trySubmitCommand! c (checkSuccess := false)


/-- Declare a free variable with name `id` and sort `t`. -/
def declareConst (id : SmtSymbol) (t : SortExpr) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareConst id t)

/-- Declare an inductive datatype in Smt lib with name `nm` and body `decl`. -/
def declareDataType (nm : SmtSymbol) (decl : SmtDatatypeDecl) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareDataType nm decl)

/-- Declare mutual inductive datatypes in Smt lib with names `nms` and bodies `decls`.
    An error is triggered if nms.size ≠ decls.size.
-/
def declareMutualDataTypes (nms : Array SmtSortDecl) (decls : Array SmtDatatypeDecl) : TranslateEnvT Unit := do
  if nms.size != decls.size then
    throwEnvError s!"declareMutualDataTypes: names and declarations mismatched: {nms} ≠ {decls}"
  trySubmitCommand! (.declareMutualDataTypes nms decls)

/-- Declare an uninterpreted function with name `nm`, arguments `args` and return type `rt`. -/
def declareFun (nm : SmtSymbol) (args: Array SortExpr) (rt : SortExpr) : TranslateEnvT Unit :=
   trySubmitCommand! (.declareFun nm args rt)


/-- Define a function with name `nm`, parameters `args`, return type `rt`, body `b` with
    `isRec` flag set to `false` by default.
-/
def defineFun (nm : SmtSymbol) (args : SortedVars) (rt : SortExpr) (b : SmtTerm) (isRec := false) : TranslateEnvT Unit :=
  trySubmitCommand! (.defineFun isRec nm args rt b)

/-- Define mutually recursive functions with declarations `decls` and bodies `bs`.
    An error is triggered if decls.size ≠ bs.size.
-/
def defineMutualFuns (decls : Array SmtFunDecl) (bs : Array SmtTerm) : TranslateEnvT Unit := do
  if decls.size != bs.size then
    throwEnvError s!"defineMutualFuns: declarations and bodies mismatched: {decls} ≠ {bs}"
  trySubmitCommand! (.defineFunsRec decls bs)


/-- Declare a sort with name `nm` and arity `n`. -/
def declareSort (nm : SmtSymbol) (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareSort nm n)

/-- Define a sort with name `nm`, optional parameters `args` and body `b`. -/
def defineSort (nm : SmtSymbol) (args : Option (Array SmtSymbol)) (b : SortExpr) : TranslateEnvT Unit :=
  trySubmitCommand! (.defineSort nm args b)

/-- Assert a proposition `p`. -/
def assertTerm (p : SmtTerm) : TranslateEnvT Unit := trySubmitCommand! (.assertTerm p)

/-- Create an Smt symbol from a free variable `v`.
    If `v` already exists in the free variables cache return the same smt symbol.
    Otherwise:
      - Increment the free variable index
      - Insert `v` in cache
      - return the smt symbol corresponding to the new index
-/
def fvarIdToSmtSymbol (v : FVarId) : TranslateEnvT SmtSymbol := do
  let env ← get
  match env.smtEnv.fvarsCache.get? v with
  | some idx => return (mkNormalSymbol s!"${idx}")
  | none =>
     let idx := env.smtEnv.fvarsCache.size
     modify (fun env => { env with smtEnv.fvarsCache := env.smtEnv.fvarsCache.insert v idx } )
     return (mkNormalSymbol s!"${idx}")

/-! Create an Smt term from a free variable. -/
def fvarIdToSmtTerm (v : FVarId) : TranslateEnvT SmtTerm :=
  return smtSimpleVarId (← fvarIdToSmtSymbol v)

/-- Given `s` an smt symbol, `t₀ ... tₙ` an array of smt sorts and optional `assertFlag` boolean value, perform the following:
     - When `assertFlag = some b`:
        - define smt predicate `(define-fun s ((@x₀ t₀) ..(@xₙ tₙ)) Bool b)`
     - Otherwise:
        - declare smt predicate `(define-fun s ((t₀) ..(tₙ)) Bool)`
   Assume that `s` is defined as `@is{xxx}`
-/
def definePredQualifier (s : SmtSymbol) (t : Array SortExpr) (assertFlag : Option Bool) : TranslateEnvT Unit := do
 match assertFlag with
 | some b =>
     let args := Array.ofFn (λ f : Fin t.size => (mkReservedSymbol s!"@x{f.val}", t[f]))
     let boolSmt := if b then trueSmt else falseSmt
     defineFun s args boolSort boolSmt
 | none =>  declareFun s t boolSort


/-- Perform the following actions:
     - Declare smt universal sort `(declare-sort typeSym 0)`
     - Declare smt instance sort `(declare-sort instSym 0)`
     - let instSort := .SymbolSort instSym
     - Declare smt predicate `(declare-fun decl.instName ((instSort) (decl.instSort)) Bool)`
-/
def defineTypeSort (typeSym : SmtSymbol) (instSym : SmtSymbol) (decl: IndTypeDeclaration) : TranslateEnvT Unit := do
  declareSort typeSym 0
  declareSort instSym 0
  declareFun decl.instName #[.SymbolSort instSym, decl.instSort] boolSort


/-- Perform the following actions:
     - Declare Empty sort in Smt Lib
     - Define smt predicate `(define-fun @isEmpty ((@x Empty)) Bool false)`
    Assume `isEmptySym := @isEmpty`
-/
def defineEmptySort (isEmptySym : SmtSymbol) : TranslateEnvT Unit := do
  declareSort emptySymbol 0
  definePredQualifier isEmptySym #[emptySort] (some false)

/-- Perform the following actions:
     - Declare PEmpty sort in Smt Lib
     - Define smt predicate `(define-fun @isPEmpty ((@x PEmpty)) Bool false)`
    Assume `isPEmptySym := @isPEmpty`
-/
def definePEmptySort (isPEmptySym : SmtSymbol) : TranslateEnvT Unit := do
  declareSort pemptySymbol 0
  definePredQualifier isPEmptySym #[pemptySort] (some false)


/-- Perform the following actions:
     - Define Prop sort in Smt Lib, which is an alias to Bool Smt Sort
     - Define smt predicate `(define-fun @isProp ((@x Prop)) Bool true)`
    Assume `isPropSym := @isProp`
-/
def definePropSort (isPropSym : SmtSymbol) : TranslateEnvT Unit := do
  defineSort propSymbol none boolSort
  definePredQualifier isPropSym #[propSort] (some true)

/-- Perform the following actions:
     - Define Nat sort in Smt Lib, which is an alias to Int Smt Sort
     - Define smt predicate `(define-fun @isNat ((@x Nat)) Bool (<= 0 @x))`
       to qualify quantifiers on Nat
    Assume `isNatSym := @isNat`
-/
def defineNatSort (isNatSym : SmtSymbol) : TranslateEnvT Unit := do
  defineSort natSymbol none intSort
  let psym := mkReservedSymbol "@x"
  let xId := smtSimpleVarId psym
  let zeroSym := natLitSmt 0
  defineFun isNatSym #[(psym, natSort)] boolSort (leqSmt zeroSym xId)


private def defineBinFun
  (fname : SmtSymbol) (top1 : SortExpr) (top2 : SortExpr)
  (ret : SortExpr) (fdef : SmtTerm → SmtTerm → SmtTerm) (isRec := false) :=
  let xsym := mkReservedSymbol "@x"
  let ysym := mkReservedSymbol "@y"
  let xId := smtSimpleVarId xsym
  let yId := smtSimpleVarId ysym
  defineFun fname #[(xsym, top1), (ysym, top2)] ret (fdef xId yId) isRec

/-- Define Nat.sub Smt function, i.e.,
     @Nat.sub x y := (ite (< x y) 0 (- x y))
-/
def defineNatSub : TranslateEnvT Unit := do
  let fdef := λ xId yId => iteSmt (ltSmt xId yId) (natLitSmt 0) (subSmt xId yId)
  defineBinFun natSubSymbol natSort natSort natSort fdef

/-- Define Int.ediv Smt function, i.e.,
      @Int.ediv x y := (ite (= 0 y) 0 (div x y))
 -/
def defineIntEDiv : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let fdef := λ xId yId => iteSmt (eqSmt natZero yId) natZero (divSmt xId yId)
  defineBinFun edivSymbol intSort intSort intSort fdef

/-- Define Int.emod Smt function, i.e.,
      @Int.emod x y := (ite (= 0 y) x (mod x y))
 -/
def defineIntEMod : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let fdef := λ xId yId => iteSmt (eqSmt natZero yId) xId (modSmt xId yId)
  defineBinFun emodSymbol intSort intSort intSort fdef


/-- Define Int.tdiv Smt function, i.e.,
      @Int.tdiv x y :=
         (ite (= 0 y) 0 (ite (<= 0 x) (div x y) (- (div (- x) y))))
-/
def defineIntTDiv : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let fdef := λ xId yId =>
      iteSmt
        (eqSmt natZero yId) natZero
        (iteSmt (leqSmt natZero xId)
          (divSmt xId yId) (negSmt (divSmt (negSmt xId) yId)))
  defineBinFun tdivSymbol intSort intSort intSort fdef

/-- Define Int.tmod Smt function, i.e.,
     @Int.tmod x y :=
       (ite (= 0 y) x (ite (<= 0 x) (mod x y) (- (mod (- x) y))))
-/
def defineIntTMod : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let fdef := λ xId yId =>
      iteSmt (eqSmt natZero yId) xId
        (iteSmt (leqSmt natZero xId)
          (modSmt xId yId) (negSmt (modSmt (negSmt xId) yId)))
  defineBinFun tmodSymbol intSort intSort intSort fdef

/-- Define Int.fdiv Smt function, i.e.,
      @Int.fdiv x y :=
        (ite (= 0 y) 0 (ite (< y 0) (div (-x) (- y)) (div x y)))
 -/
def defineIntFDiv : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let innerIte := λ xId yId =>
      iteSmt (ltSmt yId natZero) (divSmt (negSmt xId) (negSmt yId)) (divSmt xId yId)
  let fdef := λ xId yId => iteSmt (eqSmt natZero yId) natZero (innerIte xId yId)
  defineBinFun fdivSymbol intSort intSort intSort fdef

/-- Define Int.fmod Smt function, i.e.,
     @Int.fmod x y :=
       (ite (= 0 y) x (ite (< y 0) (- (mod (- x) y)) (mod x y)))
-/
def defineIntFMod : TranslateEnvT Unit := do
  let natZero := natLitSmt 0
  let fdef := λ xId yId =>
      iteSmt (eqSmt natZero yId) xId
      (iteSmt (ltSmt yId natZero) (negSmt (modSmt (negSmt xId) yId)) (modSmt xId yId))
  defineBinFun fmodSymbol intSort intSort intSort fdef


/-- Define Int.pow Smt function as follows:
    (define-fun-rec @Int.pow ((@x Int)(@y Nat)) Int
      (ite (= 0 @y) 1 (* @x (@Int.pow @x (@Nat.sub @y 1)))))
-/
def defineIntPow : TranslateEnvT Unit := do
  let natOne := natLitSmt 1
  let yEqZero := λ yId => eqSmt (natLitSmt 0) yId
  let fdef := λ xId yId => iteSmt (yEqZero yId) natOne (mulSmt xId (intPowSmt xId (natSubSmt yId natOne)))
  defineBinFun intPowSymbol intSort natSort intSort fdef (isRec := true)

/-- Define Nat.pow Smt function as follows:
    (define-fun-rec @Nat.pow ((@x Nat)(@y Nat)) Nat
      (ite (= 0 @y) 1 (* @x (@Nat.pow @x (@Nat.sub @y 1)))))
-/
def defineNatPow : TranslateEnvT Unit := do
  let natOne := natLitSmt 1
  let yEqZero := λ yId => eqSmt (natLitSmt 0) yId
  let fdef := λ xId yId => iteSmt (yEqZero yId) natOne (mulSmt xId (natPowSmt xId (natSubSmt yId natOne)))
  defineBinFun natPowSymbol natSort natSort natSort fdef (isRec := true)


/-- Define Int.toNat Smt function, i.e.,
     Int.toNat x := (ite (<= 0 x) x else 0)
-/
def defineInttoNat : TranslateEnvT Unit := do
  let xsym := mkReservedSymbol "@x"
  let xId := smtSimpleVarId xsym
  let natZero := natLitSmt 0
  let xGeqZero := leqSmt natZero xId
  let fdef := iteSmt xGeqZero xId natZero
  defineFun toNatSymbol #[(xsym, intSort)] natSort fdef

/-- Try to retrieve the value of term `t` when a `sat` result is obtained, using the
    standard `(get-value (t))` command, and return the reconstructed value
    (see `Blaster.Smt.reconstructGetValue?`): solver-specific formatting —
    cvc5's `as` constructor qualifiers and `let`-shared subterms, z3's line
    wrapping, `(- n)` negatives, SMT-LIB string escapes — is normalized to a
    Lean-flavored rendering.
    When the solver reports an error instead of a value (e.g. a partial model
    for an unsupported construct), an informative `<no value: …>` marker is
    produced; any other unrecognized response is returned unwrapped and
    trimmed, so it can be reported as-is.
    Do nothing if the Smt process is not defined.
-/
def evalTerm (t : SmtTerm) : TranslateEnvT String := do
  let env ← get
  let some p := env.smtEnv.smtProc | return ""
  checkCancelTk?
  submitCommand (.getValue t)
  let response ←
    try getOutputGetValue p.stdout
    catch e =>
      -- e.g. the solver closed its stdout mid-response: surface its stderr,
      -- which typically carries the actual failure reason.
      let stderr ← killAndDrainStderr
      throwEnvError m!"{e.toMessageData}{stderrNote stderr}"
  match reconstructGetValue? response with
  | some v => return v
  | none =>
      match solverErrorMsg? response with
      | some msg => return s!"<no value: {msg}>"
      | none => return unwrapGetValueOutput response

/-- Try to retrieve the model when a `sat` result is obtained and dump result to stdout.
    Do nothing when:
      - No solver instance is defined
      - Option solverOptions.generateCex is set to `false`
    NOTE: Values retrieved through `evalTerm` are reconstructed into a
    Lean-flavored rendering; the raw `(get-model)` dump used when no top-level
    variable exists is displayed as produced by the solver.
-/
def getModel : TranslateEnvT (List String) := do
  let env ← get
  let some p := env.smtEnv.smtProc | return []
  let topVars := env.smtEnv.topLevelVars
  if !env.optEnv.options.solverOptions.generateCex then return []
  checkCancelTk?
  if topVars.isEmpty
  then
    submitCommand (.getModel)
    let s ← getOutputModel p.stdout
    -- A solver may report an error instead of a model (e.g. a construct it
    -- cannot model): surface the failure inline rather than displaying the
    -- error report as if it were a model.
    match solverErrorMsg? s with
    | some msg => return [s!"<no model available: {msg}>"]
    | none => return [s]
  else
    -- Note: List is append when adding top level variables
    -- We therefore need to traverse the list in reverse order to
    -- properly display cex in the right order
    let cexArray ← Array.foldlM (λ acc vars => genCexAtStep acc vars) #[] topVars
    return cexArray.toList

  where
    genCexAtStep (cex : Array String) (vars : List (SmtSymbol × Name)) : TranslateEnvT (Array String) := do
      List.foldrM (λ v acc => return acc.push (← getVarValue v)) cex vars

    getVarValue (v : SmtSymbol × Name) : TranslateEnvT String := do
      return s!"{v.2}: {← evalTerm (smtSimpleVarId v.1)}"

/-- Retrieve sat result from `h`.
    An error is triggered when an unexpected check-sat result is obtained.
    Function can be called only after a check-sat
-/
partial def getSatResult (p : IO.Process.Child ⟨.piped, .piped, .piped⟩) : TranslateEnvT Result := do
  let res ← IO.asTask p.stdout.getLine -- only one line expected for checkSat result
  waitForResult res

 where
   waitForResult (res : Task (Except IO.Error String)) : TranslateEnvT Result := do
     checkCancelTk?
     if ← IO.hasFinished res then
       match normalizeLine (← IO.ofExcept res.get) with
       | "sat\n"     => return (.Falsified (← getModel))
       | "unsat\n"   => return .Valid
       -- also returned when the per-check time limit is hit; a model MUST NOT
       -- be queried in this state (SMT-LIB only allows it after `sat`)
       | "unknown\n" => return .Undetermined
       | "" =>
           let stderr ← killAndDrainStderr
           throwEnvError s!"checkSat: The solver closed its output stream before reporting a result (it may have crashed or run out of memory).{stderrNote stderr}"
       | err => throwEnvError s!"checkSat: Unexpected check-sat result: {err}"
     else
       let sleepTimeMs := (20 : UInt32)
       IO.sleep sleepTimeMs
       waitForResult res

/-- Check satisfiability of current Smt query and return the result.
    An error is triggered when an unexpected check-sat result is obtained.
    Return `Undetermined` when the Smt process is not defined.
-/
def checkSat : TranslateEnvT Result := do
  let env ← get
  let some p := env.smtEnv.smtProc | return .Undetermined
  submitCommand (.checkSat)
  getSatResult p

/-- Check satisfiability of current Smt query by assuming the provided terms
    and return the result.
    An error is triggered when an unexpected check-sat result is obtained.
    Return `Undetermined` when the Smt process is not defined.
-/
def checkSatAssuming (args : Array SmtTerm) : TranslateEnvT Result := do
  let env ← get
  let some p := env.smtEnv.smtProc | return .Undetermined
  submitCommand (.checkSatAssuming args)
  getSatResult p


/-- Try to retrieve the proof artifact when a `unsat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elaborator to parse and reconstruct
    the proof in Lean.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the Smt process is not defined.
-/
def getProof : TranslateEnvT String := do
  let env ← get
  let some p := env.smtEnv.smtProc | return ""
  submitCommand (.getProof)
  getOutputProof p.stdout



/-- Try to terminate the Smt process.
    Do nothing if Smt process is not defined.
-/
def exitSmt : TranslateEnvT UInt32 := do
 let env ← get
 let some p := env.smtEnv.smtProc | return 0
 submitCommand (.exitSmt)
 let (_, p) ← p.takeStdin
 p.wait


/-- Set the Smt logic to `ALL`. -/
def setLogicAll : TranslateEnvT Unit :=
  trySubmitCommand! (.setLogic "ALL")

/-- Set Smt `produce-proofs` option to `b`. -/
def setProduceProofs (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":produce-proofs" (toString b))

/-- Set Smt `produce-models` option to `b`. -/
def setProduceModels (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":produce-models" (toString b))

/-- Set model-based quantifier instantiation to `b`
    (z3: `smt.mbqi`, cvc5: `mbqi`; the underlying algorithms differ). -/
def setMbqi (b : Bool) : TranslateEnvT Unit := do
  match ← getSolver with
  | .z3 => trySubmitCommand! (.setOption ":smt.mbqi" (toString b))
  | .cvc5 => trySubmitCommand! (.setOption ":mbqi" (toString b))

/-- Set Smt `smt.pull-nested-quantifiers` option to `b`.
    NOTE: z3-only option, no-op for other solvers. -/
def setPullNestedQuantifiers (b : Bool) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":smt.pull-nested-quantifiers" (toString b))

/-- Set Smt `print-success` option to `b`. -/
def setPrintSuccess (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":print-success" (toString b))

/-- Set the random seed to `n` or none (z3: `smt.random-seed`, cvc5: `seed`). -/
def setRandomSeed (n : Option Nat) : TranslateEnvT Unit := do
  let some n := n | return ()
  match ← getSolver with
  | .z3 => trySubmitCommand! (.setOption ":smt.random-seed" (toString n))
  | .cvc5 => trySubmitCommand! (.setOption ":seed" (toString n))

/-- Set Smt `auto_config` option to `b`.
    NOTE: z3-only option, no-op for other solvers. -/
def setAutoConfig (b : Bool) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":auto_config" (toString b))

/-- Set Smt `smt.case_split` to `n`, with n ∈ [0..6].
    NOTE: z3-only option, no-op for other solvers. -/
def setCaseSplit (n : Nat) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":smt.case_split" (toString n))

/-- Set Smt `smt.qi.eager_threshold` to `n`.
    NOTE: z3-only option, no-op for other solvers. -/
def setQiEagerThreshold (n : Nat) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":smt.qi.eager_threshold" (toString n))


/-- Set Smt `smt.delay_units` to `b`.
    NOTE: z3-only option, no-op for other solvers. -/
def setDelayUnits (b : Bool) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":smt.delay_units" (toString b))

/-- Set macro elimination to `b` (z3: `smt.macro_finder`, cvc5: `macros-quant`). -/
def setMacroFinder (b : Bool) : TranslateEnvT Unit := do
  match ← getSolver with
  | .z3 => trySubmitCommand! (.setOption ":smt.macro_finder" (toString b))
  | .cvc5 => trySubmitCommand! (.setOption ":macros-quant" (toString b))

/-- Set Smt `smt.relevancy` option to `i`.
    NOTE: z3-only option, no-op for other solvers. -/
def setRelevancy (n : Nat) : TranslateEnvT Unit := do
  let .z3 ← getSolver | return ()
  trySubmitCommand! (.setOption ":smt.relevancy" (toString n))

/-- Set the solving timeout when the option is specified.
    NOTE: z3's `timeout` applies per context whereas cvc5's `tlimit-per`
    applies to each `check-sat` individually (cvc5's `tlimit` is a no-op
    when set via `set-option`). Both are expressed in milliseconds.
-/
def setTimeout : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let some n := sOpts.timeout | return ()
  -- need to convert timeout to milliseconds
  match ← getSolver with
  | .z3 => trySubmitCommand! (.setOption ":timeout" (toString (n * 1000)))
  | .cvc5 => trySubmitCommand! (.setOption ":tlimit-per" (toString (n * 1000)))

/-- Set the default Smt options, i.e., for every solver:
     - (set-option :print-success true)
     - (set-option :produce-models true)
     - (set-option :produce-proofs true)
    for z3:
     - (set-option :smt.pull-nested-quantifiers true)
     - (set-option :smt.mbqi true)
     - (set-option :auto_config false)
     - (set-option :smt.random-seed n) when `n` is provided in solver options
     - (set-option :smt.macro_finder true)
     - (set-option :timeout n) when a timeout is provided in solver options
    for cvc5:
     - (set-option :mbqi true)
     - (set-option :seed n) when `n` is provided in solver options
     - (set-option :macros-quant true)
     - (set-option :tlimit-per n) when a timeout is provided in solver options
     - (set-logic ALL) — cvc5 requires the logic to be set before any
       declaration (`ALL` matches z3's behavior when no logic is set)
-/
def setDefaultSmtOptions (sOpts : BlasterOptions) : TranslateEnvT Unit := do
 setPrintSuccess true
 setProduceModels true
 setProduceProofs true
 setPullNestedQuantifiers true
 setMbqi true
 setAutoConfig false
 setRandomSeed sOpts.randomSeed
 setMacroFinder true
 setTimeout
 if (← getSolver) == .cvc5 then
   setLogicAll

/-- Perform the following actions:
     - resolve the backend solver (see `resolveSolver`) and record it in the
       translation environment
     - when option `only-smt-lib` is set to `false`:
       - Spawn the backend solver process and update TranslateEnv
       - set the default smt solver options by emitting the corresponding commands
     - when option `only-smt-lib` is set to `true`:
       - only add the solver options to the list of smt commands.
-/
def setBlasterProcess : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let solver ← resolveSolver sOpts
  let timeout ← resolveTimeout sOpts
  modify fun env =>
    { env with
        smtEnv.solver := solver,
        optEnv.options.solverOptions.timeout := timeout }
  unless sOpts.onlySmtLib do
    let proc ← createBlasterProcess solver
    modify fun env => { env with smtEnv.smtProc := proc }
  setDefaultSmtOptions { sOpts with timeout }


end Blaster.Smt
