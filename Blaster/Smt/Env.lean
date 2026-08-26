import Lean
import Blaster.Command.Options
import Blaster.Optimize.Env
import Blaster.Smt.EmitCommand
import Blaster.Smt.Model

open Lean Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

private initialize agreementArtifactCounter : IO.Ref Nat ← IO.mkRef 0

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

/-- Solver truth value, independent of protocol, process, and model handling. -/
inductive SolverVerdict where
  | valid
  | falsified
  | undetermined
deriving Repr, BEq, DecidableEq, Inhabited

def SolverVerdict.isDecisive : SolverVerdict → Bool
  | .valid | .falsified => true
  | .undetermined => false

/-- Lifecycle/protocol status for one solver check. A model failure is distinct
    because the already-observed `sat` verdict remains authoritative. -/
inductive SolverRunStatus where
  | completed
  | timedOut
  | processFailed
  | protocolFailed
  | modelFailed
deriving Repr, BEq, DecidableEq, Inhabited

/-- Complete result of one backend check. Verdict, evidence, and
    infrastructure state intentionally occupy separate fields. -/
structure SolverOutcome where
  solver : SmtSolver
  verdict : Option SolverVerdict
  status : SolverRunStatus
  counterexample : Option (List String) := none
  elapsedMs : Nat := 0
  diagnostic : Option String := none
deriving Repr

inductive AgreementFailureKind where
  | hardDisagreement
  | incompleteDisagreement
  | infrastructureFailure
deriving Repr, BEq, DecidableEq

structure AgreementFailure where
  kind : AgreementFailureKind
  diagnostic : String
deriving Repr

/-- Deterministic aggregate of two compatible solver outcomes. -/
structure AgreementDecision where
  verdict : SolverVerdict
  status : SolverRunStatus
  counterexample : Option (List String)
  elapsedMs : Nat
  diagnostic : Option String
deriving Repr

private def orderOutcomes (outcomes : List SolverOutcome) : List SolverOutcome :=
  [SmtSolver.z3, SmtSolver.cvc5].filterMap fun solver =>
    outcomes.find? (·.solver == solver)

private def combineDiagnostics (outcomes : List SolverOutcome) : Option String :=
  let lines := (orderOutcomes outcomes).filterMap fun outcome =>
    outcome.diagnostic.map fun diagnostic => s!"{outcome.solver}: {diagnostic}"
  if lines.isEmpty then none else some (String.intercalate "\n" lines)

private def evidenceQuality (outcome : SolverOutcome) : Nat :=
  match outcome.counterexample with
  | some counterexample =>
      if counterexample.isEmpty then 0
      else if outcome.status == .completed then 2
      else if outcome.status == .modelFailed then 1
      else 0
  | none => 0

private def bestEvidence (outcomes : List SolverOutcome) : Option SolverOutcome :=
  (orderOutcomes outcomes).foldl (init := none) fun best candidate =>
    match best with
    | none => some candidate
    | some current =>
        if evidenceQuality candidate > evidenceQuality current then some candidate
        else some current

/-- Compare verdicts independently from evidence. Infrastructure failures are
    fatal; after matching `sat`, complete evidence outranks partial evidence,
    with fixed Z3-then-cvc5 order only breaking equal-quality ties. -/
def aggregateAgreement (a b : SolverOutcome) : Except AgreementFailure AgreementDecision := do
  let ordered := orderOutcomes [a, b]
  if let some failed := ordered.find? fun outcome =>
      outcome.status != .completed && outcome.status != .modelFailed then
    throw {
      kind := .infrastructureFailure
      diagnostic := s!"{failed.solver} ended with {reprStr failed.status}: {failed.diagnostic.getD "no diagnostic"}"
    }
  let some av := a.verdict
    | throw { kind := .infrastructureFailure, diagnostic := s!"{a.solver} produced no verdict" }
  let some bv := b.verdict
    | throw { kind := .infrastructureFailure, diagnostic := s!"{b.solver} produced no verdict" }
  let selected := bestEvidence ordered
  let selectedQuality := selected.map evidenceQuality |>.getD 0
  let decision (verdict : SolverVerdict) :=
    let counterexample :=
      if verdict == .falsified then selected.bind (·.counterexample) else none
    let status :=
      if verdict == .falsified && selectedQuality == 2 then .completed
      else if ordered.any (·.status == .modelFailed) then .modelFailed
      else .completed
    { verdict, status, counterexample, elapsedMs := max a.elapsedMs b.elapsedMs,
      diagnostic := combineDiagnostics ordered }
  match av, bv with
  | .valid, .valid => return decision .valid
  | .falsified, .falsified => return decision .falsified
  | .undetermined, .undetermined => return decision .undetermined
  | .valid, .falsified
  | .falsified, .valid =>
      throw {
        kind := .hardDisagreement
        diagnostic := s!"Hard solver disagreement: {a.solver}={reprStr av}, {b.solver}={reprStr bv}"
      }
  | _, _ =>
      throw {
        kind := .incompleteDisagreement
        diagnostic := s!"Incomplete solver disagreement: {a.solver}={reprStr av}, {b.solver}={reprStr bv}"
      }

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
    (sOpts : BlasterOptions) (solver : Option SmtSolver) (strictRequested : Bool) :
    UndeterminedAction :=
  if isExpectedUndetermined sOpts.solveResult then .expected
  else if sOpts.solverMode == .single && sOpts.allowCvc5Undetermined && solver == some .cvc5 then .allowed
  else if sOpts.solverMode == .single && strictRequested && solver == some .cvc5 then .strictError
  else if sOpts.solverMode == .agree then .strictError
  else .warning

def blankRef : TranslateEnvT Syntax := getRef

def logResult (r : Result) (isCTI := false) (indLabel := "") (cexLabel := "Counterexample") : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let policySolver := (← get).smtEnv.singleSolver
  let action := undeterminedAction sOpts policySolver
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

/-- Resolved executable, version banner, and spawn argv for one backend. -/
private structure SolverExecutable where
  candidate : SolverCandidate
  version : String

/-- Find a usable solver launch specification: candidates are probed in order
    (native executable first, then a best-effort WSL fallback) and the first
    one passing the version policy (see `evalCandidateProbe`) wins. -/
private def findSolverExecutable (solver : SmtSolver) : IO SolverExecutable := do
  let desc := solver.descriptor
  let mut attemptLogs := #[]
  for candidate in desc.candidates do
    let outcome ← probeSolverCandidate desc candidate
    match evalCandidateProbe desc candidate outcome with
    | .ok () => return { candidate, version := outcome.banner }
    | .error log => attemptLogs := attemptLogs.push log
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

/-- Spawn one independently owned solver session and retain enough launch
    metadata to reproduce the exact invocation. -/
def createSolverSession (solver : SmtSolver) : IO (SolverSession × SolverRecord) := do
  let desc := solver.descriptor
  let executable ← findSolverExecutable solver
  let (cmd, args) := desc.spawnInvocation executable.candidate
  let process ← IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := cmd
    args   := args
  }
  let commandLine := String.intercalate " " (cmd :: args.toList)
  return (
    { solver, process },
    { solver, version := executable.version, commandLine, setupCommands := #[] })

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

/-- Update persistent diagnostic data for one backend. -/
private def modifySolverRecord
    (solver : SmtSolver) (f : SolverRecord → SolverRecord) : TranslateEnvT Unit :=
  modify fun env =>
    { env with smtEnv.solverRecords := env.smtEnv.solverRecords.map fun record =>
        if record.solver == solver then f record else record }

private def getSession? (solver : SmtSolver) : TranslateEnvT (Option SolverSession) :=
  return (← get).smtEnv.sessions.find? (·.solver == solver)

/-- Remove a session from state before performing any cleanup operation. -/
private def retireSession? (solver : SmtSolver) : TranslateEnvT (Option SolverSession) := do
  let sessions := (← get).smtEnv.sessions
  let session := sessions.find? (·.solver == solver)
  if session.isSome then
    modify fun env =>
      { env with smtEnv := {
          env.smtEnv with
          sessions := env.smtEnv.sessions.filter (fun active => active.solver != solver)
          emitProc := none
        } }
  return session

/-- Terminate (when requested), reap exactly once, and drain stderr from an
    already-retired child. `tryWait = some` means the child was reaped there. -/
private def cleanupOwnedSession (session : SolverSession) (hard : Bool) : TranslateEnvT String := do
  let p := session.process
  let alreadyExited ←
    try p.tryWait
    catch _ => pure none
  if alreadyExited.isNone then
    if hard then
      try p.kill catch _ => pure ()
      try discard p.wait catch _ => pure ()
    else
      try
        p.stdin.putStr "(exit)\n"
        p.stdin.flush
        let (_, p) ← p.takeStdin
        discard p.wait
      catch _ =>
        try p.kill catch _ => pure ()
        try discard p.wait catch _ => pure ()
  let stderr ←
    try p.stderr.readToEnd
    catch _ => pure ""
  let stderr := stderr.trim
  unless stderr.isEmpty do
    modifySolverRecord session.solver fun record =>
      { record with stderr := record.stderr.push stderr }
  if (← get).optEnv.options.solverOptions.verbose ≥ 3 then
    try
      IO.println s!"[blaster diagnostic] solver={session.solver}; stage=session cleanup; stderr={if stderr.isEmpty then "<empty>" else stderr}"
    catch _ => pure ()
  return stderr

private def retireAndCleanup (solver : SmtSolver) (hard : Bool) : TranslateEnvT String := do
  let some session ← retireSession? solver | return ""
  cleanupOwnedSession session hard

private def retireAllSessions (hard : Bool) : TranslateEnvT Unit := do
  let sessions := (← get).smtEnv.sessions
  modify fun env => { env with smtEnv.sessions := #[], smtEnv.emitProc := none }
  for session in sessions do
    discard <| cleanupOwnedSession session hard

/-- Unconditional owner boundary for every session created by `action`.
    Cleanup is idempotent because ownership is retired before child handling;
    the finalizer cannot consume an exception or Lean interruption from `action`. -/
def withSmtSessionOwner (action : TranslateEnvT α) : TranslateEnvT α := do
  try action
  finally retireAllSessions true

/-- Lean cancellation owns both active children: retire state first, then kill
    and reap every session before raising the interrupt. -/
def checkCancelTk? : TranslateEnvT Unit := do
  if let some tk := (← readThe Core.Context).cancelTk? then
    if ← tk.isSet then
      retireAllSessions true
      throwInterruptException

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
partial def getOutputModel (h : IO.FS.Handle) (proof := false) : IO String := do
  let rec loop (acc : String) (st : SexpScanState) : IO String := do
    let line := normalizeLine (← h.getLine)
    if line.isEmpty then
      throw <| IO.userError
        "The solver closed its output stream while a model/proof response was pending."
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

/-- The canonical query is retained regardless of dumping, diagnostics, or
    process presence. This is the single translation replayed to every solver. -/
def storeCommand (c : SmtCommand) : TranslateEnvT Unit :=
  modify fun env => { env with smtEnv.smtCommands := env.smtEnv.smtCommands.push c }

private def orderedSolverRecords (records : Array SolverRecord) : List SolverRecord :=
  [SmtSolver.z3, SmtSolver.cvc5].filterMap fun solver =>
    records.find? (·.solver == solver)

private def solverTranscript (record : SolverRecord) (canonical : Array SmtCommand) : String :=
  let check :=
    match record.checkCommand with
    | some command => [toString command]
    | none => []
  String.intercalate "\n" <|
    record.setupCommands.toList.map toString ++
    canonical.toList.map toString ++ check ++ record.modelCommands.toList ++ ["(exit)"]

private def agreementSummary
    (reason : String) (outcomes : Array SolverOutcome) : TranslateEnvT String := do
  let env ← get
  let query := String.intercalate "\n" (env.smtEnv.smtCommands.toList.map toString)
  let records := String.intercalate "\n\n" <|
    (orderedSolverRecords env.smtEnv.solverRecords).map fun record =>
      let outcome := outcomes.find? (·.solver == record.solver)
      let verdict := outcome.bind (·.verdict) |>.map reprStr |>.getD "<none>"
      let status := outcome.map (reprStr ∘ (·.status)) |>.getD "<none>"
      let elapsed := outcome.map (toString ∘ (·.elapsedMs)) |>.getD
        (record.failureElapsedMs.map toString |>.getD "<none>")
      s!"solver: {record.solver}\nversion: {record.version}\ncommand line: {record.commandLine}\nverdict: {verdict}\nstatus: {status}\nelapsed ms: {elapsed}\nconfigured timeout ms: {record.timeoutMs.map toString |>.getD "<none>"}\nfailed stage: {record.failedStage.getD "<none>"}\nfailed command: {record.failedCommand.getD "<none>"}\nfailure response: {record.failureResponse.getD "<none>"}\ncheck command: {record.checkCommand.map toString |>.getD "<none>"}\nstdout:\n{String.join record.stdout.toList}\nstderr:\n{String.intercalate "\n" record.stderr.toList}\nmodel commands:\n{String.intercalate "\n" record.modelCommands.toList}\nraw model responses:\n{String.intercalate "\n" record.modelResponses.toList}"
  return s!"reason: {reason}\noutcomes: {reprStr (orderOutcomes outcomes.toList)}\n\nshared SMT query:\n{query}\n\n{records}\n"

private def saveAgreementArtifacts
    (reason : String) (outcomes : Array SolverOutcome) : TranslateEnvT (Option String) := do
  let stamp ← IO.monoMsNow
  let serial ← agreementArtifactCounter.modifyGet fun current => (current, current + 1)
  let directory := s!".blaster/agreement-{stamp}-{serial}"
  try
    IO.FS.createDirAll directory
    IO.FS.writeFile s!"{directory}/summary.txt" (← agreementSummary reason outcomes)
    let canonical := (← get).smtEnv.smtCommands
    for record in orderedSolverRecords (← get).smtEnv.solverRecords do
      IO.FS.writeFile s!"{directory}/{record.solver}.smt2"
        (solverTranscript record canonical ++ "\n")
    return some directory
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    logWarningAt (← blankRef) m!"Failed to save agreement artifacts: {error.toMessageData}"
    return none

private def recordSessionFailure
    (solver : SmtSolver) (stage : String) (command : SmtCommand)
    (response : String) (elapsedMs : Nat) : TranslateEnvT Unit :=
  modifySolverRecord solver fun record =>
    { record with
      failedStage := some stage
      failedCommand := some (toString command)
      failureResponse := some response
      failureElapsedMs := some elapsedMs }

private def retireFailedSession
    (session : SolverSession) (stage : String) (command : SmtCommand)
    (response : String) (startedMs : Nat) : TranslateEnvT String := do
  let elapsedMs := (← IO.monoMsNow) - startedMs
  recordSessionFailure session.solver stage command response elapsedMs
  let stderr ← retireAndCleanup session.solver true
  return s!"solver={session.solver}; stage={stage}; command={command}; response={response}; elapsed={elapsedMs}ms{stderrNote stderr}"

private def logDiagnostic (message : String) : TranslateEnvT Unit := do
  if (← get).optEnv.options.solverOptions.verbose ≥ 3 then
    IO.println s!"[blaster diagnostic] {message}"

private def cancellationRequested : TranslateEnvT Bool := do
  let some token := (← readThe Core.Context).cancelTk? | return false
  token.isSet

private partial def awaitTaskCancelable (task : Task α) : TranslateEnvT α := do
  if ← cancellationRequested then
    retireAllSessions true
    let _ := task.get
    throwInterruptException
  if ← IO.hasFinished task then return task.get
  IO.sleep 20
  awaitTaskCancelable task

private def withEmitProcess (process : PipedChild) (action : TranslateEnvT α) : TranslateEnvT α := do
  modify fun env => { env with smtEnv.emitProc := some process }
  try action
  finally modify fun env => { env with smtEnv.emitProc := none }

/-- Send one command to one session. Only I/O emission failures become data;
    Lean interruption and unexpected exceptions propagate to the owner. -/
private def sendCommandToSession
    (session : SolverSession) (c : SmtCommand) (checkSuccess : Bool) :
    TranslateEnvT (Except String Unit) := do
  let emitted ←
    try
      withEmitProcess session.process c.emit
      pure (.ok () : Except String Unit)
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      pure (.error s!"IO error while executing {c}: {← error.toMessageData.toString}")
  if let .error error := emitted then return .error error
  if !checkSuccess then return .ok ()
  let responseTask ← IO.asTask session.process.stdout.getLine Task.Priority.dedicated
  let response ← awaitTaskCancelable responseTask
  match response with
  | .error error => return .error s!"IO error while executing {c}: {error}"
  | .ok raw =>
      let out := normalizeLine raw
      modifySolverRecord session.solver fun record =>
        { record with stdout := record.stdout.push out }
      match out with
      | "success\n" => return .ok ()
      | "" => return .error s!"solver closed stdout while executing {c}"
      | err => return .error s!"unexpected response {err.trim} while executing {c}"

private def throwSessionCommandError
    (session : SolverSession) (stage : String) (command : SmtCommand)
    (error : String) : TranslateEnvT α := do
  let startedMs ← IO.monoMsNow
  throwEnvError (← retireFailedSession session stage command error startedMs)

private def beginCanonicalEpoch : TranslateEnvT Unit :=
  modify fun env =>
    { env with smtEnv.solverRecords := env.smtEnv.solverRecords.map fun record =>
        if record.checkCommand.isSome then
          { record with
            checkCommand := none
            stdout := #[]
            modelCommands := #[]
            modelResponses := #[]
            failedStage := none
            failedCommand := none
            failureResponse := none
            failureElapsedMs := none }
        else record }

/-- Broadcast a canonical declaration/assertion once. `first` retires a failed
    backend and continues with every healthy session; `agree` records an
    infrastructure artifact and fails immediately. -/
partial def trySubmitCommand! (c : SmtCommand) (checkSuccess := true) : TranslateEnvT Unit := do
  beginCanonicalEpoch
  storeCommand c
  let mode := (← get).optEnv.options.solverOptions.solverMode
  let sessions := (← get).smtEnv.sessions
  let mut failures : Array String := #[]
  for session in sessions do
    let startedMs ← IO.monoMsNow
    match ← sendCommandToSession session c checkSuccess with
    | .ok () => pure ()
    | .error error =>
        let diagnostic ← retireFailedSession session "command submission" c error startedMs
        failures := failures.push diagnostic
        match mode with
        | .single => throwEnvError diagnostic
        | .first =>
            modify fun env =>
              { env with smtEnv.deferredSessions :=
                  if env.smtEnv.deferredSessions.contains session.solver then
                    env.smtEnv.deferredSessions
                  else env.smtEnv.deferredSessions.push session.solver }
        | .agree =>
            retireAllSessions true
            let artifact ← saveAgreementArtifacts diagnostic #[]
            throwEnvError s!"Agreement infrastructure failure: {diagnostic}\nAgreement artifacts: {artifact.getD "unavailable"}"
  if mode == .first && !failures.isEmpty && (← get).smtEnv.sessions.isEmpty then
    throwEnvError s!"No usable solver session remains after command submission:\n{String.intercalate "\n" failures.toList}"



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

/-- Backend-specific setup transcript. Logical declarations and assertions are
    deliberately absent; they live in the canonical query. -/
def solverSetupCommands (solver : SmtSolver) (sOpts : BlasterOptions) : Array SmtCommand :=
  let common := #[
    .setOption ":print-success" "true",
    .setOption ":produce-models" "true",
    .setOption ":produce-proofs" "true"
  ]
  let withSeed (commands : Array SmtCommand) (name : String) :=
    match sOpts.randomSeed with
    | some seed => commands.push (.setOption name (toString seed))
    | none => commands
  let withTimeout (commands : Array SmtCommand) (name : String) :=
    match sOpts.timeout with
    | some timeout => commands.push (.setOption name (toString (timeout * 1000)))
    | none => commands
  match solver with
  | .z3 =>
      let commands := common ++ #[
        .setOption ":smt.pull-nested-quantifiers" "true",
        .setOption ":smt.mbqi" "true",
        .setOption ":auto_config" "false"
      ]
      let commands := withSeed commands ":smt.random-seed"
      let commands := commands.push (.setOption ":smt.macro_finder" "true")
      withTimeout commands ":timeout"
  | .cvc5 =>
      let commands := common.push (.setOption ":mbqi" "true")
      let commands := withSeed commands ":seed"
      let commands := commands.push (.setOption ":macros-quant" "true")
      let commands := withTimeout commands ":tlimit-per"
      commands.push (.setLogic "ALL")

private def upsertSolverRecord (record : SolverRecord) : TranslateEnvT Unit :=
  modify fun env =>
    let found := env.smtEnv.solverRecords.any (·.solver == record.solver)
    let records :=
      if found then
        env.smtEnv.solverRecords.map fun old =>
          if old.solver == record.solver then
            { old with
              version := record.version
              commandLine := record.commandLine
              setupCommands := record.setupCommands
              timeoutMs := record.timeoutMs }
          else old
      else env.smtEnv.solverRecords.push record
    { env with smtEnv.solverRecords := records }

/-- Spawn and initialize one missing backend. With `replay = true`, replay the
    retained canonical query so incremental state-machine checks still compare
    the same encoding after `first` retired a prior loser. -/
private def spawnAndInitializeSolver
    (solver : SmtSolver) (replay : Bool) : TranslateEnvT (Except String Unit) := do
  try
    let (session, record) ← createSolverSession solver
    let sOpts := (← get).optEnv.options.solverOptions
    let setup := solverSetupCommands solver sOpts
    modify fun env => { env with smtEnv.sessions := env.smtEnv.sessions.push session }
    upsertSolverRecord {
      record with
      setupCommands := setup
      timeoutMs := sOpts.timeout.map (· * 1000)
    }
    for command in setup do
      let startedMs ← IO.monoMsNow
      match ← sendCommandToSession session command true with
      | .ok () => pure ()
      | .error error =>
          return .error (← retireFailedSession session "solver setup" command error startedMs)
    if replay then
      for command in (← get).smtEnv.smtCommands do
        let startedMs ← IO.monoMsNow
        match ← sendCommandToSession session command true with
        | .ok () => pure ()
        | .error error =>
            return .error (← retireFailedSession session "canonical query replay" command error startedMs)
    logDiagnostic s!"solver={solver}; version={record.version}; command={record.commandLine}"
    return .ok ()
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    let stderr ← retireAndCleanup solver true
    return .error s!"solver={solver}; stage=process startup; response={← error.toMessageData.toString}{stderrNote stderr}"

/-- Counterexample evidence is allowed to fail without changing a `sat`
    verdict. The diagnostic retains stage and raw-response information. -/
private structure ModelEvidence where
  counterexample : List String := []
  diagnostic : Option String := none

private def requestModelResponse
    (session : SolverSession) (command : SmtCommand) (readResponse : IO String) :
    TranslateEnvT (Except String String) := do
  let startedMs ← IO.monoMsNow
  let commandText := toString command
  modifySolverRecord session.solver fun record =>
    { record with modelCommands := record.modelCommands.push commandText }
  logDiagnostic s!"solver={session.solver}; model-command={commandText}"
  match ← sendCommandToSession session command false with
  | .error error =>
      let diagnostic ←
        retireFailedSession session "model command submission" command error startedMs
      return .error diagnostic
  | .ok () =>
      let responseTask ← IO.asTask readResponse Task.Priority.dedicated
      match ← awaitTaskCancelable responseTask with
      | .error error =>
          let diagnostic ←
            retireFailedSession session "model response" command (toString error) startedMs
          return .error diagnostic
      | .ok response =>
          modifySolverRecord session.solver fun record =>
            { record with
              modelResponses := record.modelResponses.push response
              stdout := record.stdout.push response }
          logDiagnostic s!"solver={session.solver}; raw-model-response=\n{response}"
          return .ok response

private def evalTermFor
    (session : SolverSession) (t : SmtTerm) : TranslateEnvT (Option String × Option String) := do
  let command := SmtCommand.getValue t
  match ← requestModelResponse session command (getOutputGetValue session.process.stdout) with
  | .error diagnostic => return (none, some diagnostic)
  | .ok response =>
      match Sexp.parseMany response with
      | .error error =>
          let diagnostic :=
            s!"S-expression parsing failed for get-value response: {error}; raw response: {response.trim}"
          logDiagnostic s!"solver={session.solver}; parsed-smt-value=error: {error}"
          return (none, some diagnostic)
      | .ok parsed =>
          logDiagnostic s!"solver={session.solver}; parsed-smt-value={reprStr parsed}"
          match solverErrorMsg? response with
          | some error =>
              return (none, some s!"get-value returned an SMT error: {error}; raw response: {response.trim}")
          | none =>
              match reconstructGetValue? response with
              | some rendered =>
                  logDiagnostic s!"solver={session.solver}; lean-rendered-value={rendered}"
                  return (some rendered, none)
              | none =>
                  return (none, some s!"Response framing failed: expected ((term value)); raw response: {response.trim}")

private def getModelFor (solver : SmtSolver) : TranslateEnvT ModelEvidence := do
  let some session ← getSession? solver
    | return { diagnostic := some s!"Solver process failed during model retrieval: {solver} session is unavailable" }
  let topVars := (← get).smtEnv.topLevelVars
  let topVarsText := String.intercalate "; " <| topVars.toList.map fun vars =>
    s!"[{String.intercalate ", " (vars.map fun entry => s!"{entry.1}:{entry.2}")}]"
  logDiagnostic s!"solver={solver}; topLevelVars={topVarsText}"
  if topVars.isEmpty then
    match ← requestModelResponse session .getModel (getOutputModel session.process.stdout) with
    | .error diagnostic => return { diagnostic := some diagnostic }
    | .ok response =>
        match Sexp.parseMany response with
        | .error error =>
            return {
              diagnostic := some s!"S-expression parsing failed for get-model response: {error}; raw response: {response.trim}"
            }
        | .ok parsed =>
            logDiagnostic s!"solver={solver}; parsed-smt-model={reprStr parsed}"
            match solverErrorMsg? response with
            | some error =>
                return {
                  diagnostic := some s!"get-model returned an SMT error: {error}; raw response: {response.trim}"
                }
            | none => return { counterexample := [response] }
  else
    let mut counterexample : Array String := #[]
    let mut diagnostics : Array String := #[]
    for vars in topVars do
      for entry in vars.reverse do
        let (rendered, diagnostic) ← evalTermFor session (smtSimpleVarId entry.1)
        match rendered with
        | some value => counterexample := counterexample.push s!"{entry.2}: {value}"
        | none => counterexample := counterexample.push s!"{entry.2}: <counterexample unavailable>"
        if let some diagnostic := diagnostic then
          diagnostics := diagnostics.push s!"{entry.2}: {diagnostic}"
    return {
      counterexample := counterexample.toList
      diagnostic := if diagnostics.isEmpty then none else some (String.intercalate "\n" diagnostics.toList)
    }

private structure PendingCheck where
  solver : SmtSolver
  command : SmtCommand
  startedMs : Nat
  timeoutMs : Option Nat
  deadlineMs : Option Nat
  response : Task (Except IO.Error String)

private inductive CheckStart where
  | pending (check : PendingCheck)
  | failed (outcome : SolverOutcome)

private inductive PendingCompletion where
  | response (check : PendingCheck) (value : Except IO.Error String)
      (remaining : Array PendingCheck)
  | timedOut (check : PendingCheck) (remaining : Array PendingCheck)
/-- Native solvers receive the configured limit themselves. Give their
    terminal `unknown` response bounded scheduling and pipe-drain slack before
    enforcing Blaster's hard process deadline. -/
private def responseDeadlineGraceMs : Nat := 1000


private def startCheck (solver : SmtSolver) (command : SmtCommand) : TranslateEnvT CheckStart := do
  let submissionStartedMs ← IO.monoMsNow
  let some session ← getSession? solver
    | return .failed {
        solver, verdict := none, status := .processFailed,
        diagnostic := some s!"solver={solver}; stage=check startup; command={command}; solver session is unavailable"
      }
  let timeoutMs :=
    (← get).smtEnv.solverRecords.find? (·.solver == solver) |>.bind (·.timeoutMs)
  match ← sendCommandToSession session command false with
  | .ok () =>
      let startedMs ← IO.monoMsNow
      let response ← IO.asTask session.process.stdout.getLine Task.Priority.dedicated
      return .pending {
        solver, command, startedMs, timeoutMs,
        deadlineMs := timeoutMs.map (startedMs + · + responseDeadlineGraceMs), response
      }
  | .error error =>
      let diagnostic ←
        retireFailedSession session "check submission" command error submissionStartedMs
      return .failed {
        solver, verdict := none, status := .processFailed,
        elapsedMs := (← IO.monoMsNow) - submissionStartedMs, diagnostic := some diagnostic
      }

private def finishCheck
    (pending : PendingCheck) (response : Except IO.Error String) : TranslateEnvT SolverOutcome := do
  let elapsedMs := (← IO.monoMsNow) - pending.startedMs
  match response with
  | .error error =>
      let response := toString error
      recordSessionFailure pending.solver "check response" pending.command response elapsedMs
      let stderr ← retireAndCleanup pending.solver true
      return {
        solver := pending.solver, verdict := none, status := .processFailed, elapsedMs,
        diagnostic := some s!"solver={pending.solver}; stage=check response; command={pending.command}; response={response}; elapsed={elapsedMs}ms{stderrNote stderr}"
      }
  | .ok raw =>
      let response := normalizeLine raw
      modifySolverRecord pending.solver fun record =>
        { record with stdout := record.stdout.push response }
      logDiagnostic s!"solver={pending.solver}; check-sat-response={response.trim}"
      match response with
      | "sat\n" => return {
          solver := pending.solver, verdict := some .falsified,
          status := .completed, elapsedMs
        }
      | "unsat\n" => return {
          solver := pending.solver, verdict := some .valid,
          status := .completed, elapsedMs
        }
      | "unknown\n" => return {
          solver := pending.solver, verdict := some .undetermined,
          status := .completed, elapsedMs,
          diagnostic := some "solver returned unknown"
        }
      | "" =>
          recordSessionFailure pending.solver "check response" pending.command
            "solver closed stdout before reporting a verdict" elapsedMs
          let stderr ← retireAndCleanup pending.solver true
          return {
            solver := pending.solver, verdict := none, status := .processFailed, elapsedMs,
            diagnostic := some s!"solver={pending.solver}; stage=check response; command={pending.command}; solver closed stdout before reporting a verdict; elapsed={elapsedMs}ms{stderrNote stderr}"
          }
      | unexpected =>
          recordSessionFailure pending.solver "check protocol" pending.command unexpected.trim elapsedMs
          let stderr ← retireAndCleanup pending.solver true
          return {
            solver := pending.solver, verdict := none, status := .protocolFailed, elapsedMs,
            diagnostic := some s!"solver={pending.solver}; stage=check protocol; command={pending.command}; response={unexpected.trim}; elapsed={elapsedMs}ms{stderrNote stderr}"
          }

private def timeoutCheck (pending : PendingCheck) : TranslateEnvT SolverOutcome := do
  let elapsedMs := (← IO.monoMsNow) - pending.startedMs
  let configured := pending.timeoutMs.getD 0
  let diagnostic :=
    s!"solver={pending.solver}; stage=check timeout; command={pending.command}; configured timeout={configured}ms; elapsed={elapsedMs}ms"
  recordSessionFailure pending.solver "check timeout" pending.command diagnostic elapsedMs
  discard <| retireAndCleanup pending.solver true
  let _ := pending.response.get
  return {
    solver := pending.solver, verdict := none, status := .timedOut, elapsedMs,
    diagnostic := some diagnostic
  }

private def attachCounterexample (outcome : SolverOutcome) : TranslateEnvT SolverOutcome := do
  if outcome.verdict != some .falsified ||
      !(← get).optEnv.options.solverOptions.generateCex then
    return outcome
  let evidence ← getModelFor outcome.solver
  match evidence.diagnostic with
  | none => return { outcome with counterexample := some evidence.counterexample }
  | some diagnostic =>
      modifySolverRecord outcome.solver fun record =>
        { record with
          failedStage := some "model evidence"
          failedCommand := record.modelCommands.back?
          failureResponse := some diagnostic }
      logWarningAt (← blankRef)
        m!"Counterexample unavailable from {outcome.solver}; the Falsified verdict is preserved. {diagnostic}"
      return {
        solver := outcome.solver
        verdict := outcome.verdict
        status := .modelFailed
        counterexample := if evidence.counterexample.isEmpty then none else some evidence.counterexample
        elapsedMs := outcome.elapsedMs
        diagnostic := some diagnostic
      }

private partial def waitFirstPending
    (pending : Array PendingCheck) : TranslateEnvT PendingCompletion := do
  if pending.isEmpty then
    throwEnvError "internal error: attempted to wait for an empty solver set"
  if ← cancellationRequested then
    retireAllSessions true
    for check in pending do
      let _ := check.response.get
    throwInterruptException
  for check in pending do
    if ← IO.hasFinished check.response then
      return .response check check.response.get (pending.filter (·.solver != check.solver))
  let now ← IO.monoMsNow
  for check in pending do
    if check.deadlineMs.any (· ≤ now) then
      return .timedOut check (pending.filter (·.solver != check.solver))
  IO.sleep 10
  waitFirstPending pending

private def deferredFailureOutcome (solver : SmtSolver) : TranslateEnvT SolverOutcome := do
  let record := (← get).smtEnv.solverRecords.find? (·.solver == solver)
  let diagnostic := record.bind (·.failureResponse) |>.getD
    "session was retired after a command failure"
  return {
    solver, verdict := none, status := .processFailed,
    elapsedMs := record.bind (·.failureElapsedMs) |>.getD 0,
    diagnostic := some diagnostic
  }

private def ensureConfiguredSessions : TranslateEnvT (Array SolverOutcome) := do
  let deferred := (← get).smtEnv.deferredSessions
  let mut failures := #[]
  for solver in (← get).smtEnv.configuredSolvers do
    if (← getSession? solver).isNone then
      if deferred.contains solver then
        failures := failures.push (← deferredFailureOutcome solver)
      else
        let started ← IO.monoMsNow
        match ← spawnAndInitializeSolver solver true with
        | .ok () => pure ()
        | .error diagnostic =>
            failures := failures.push {
              solver, verdict := none, status := .processFailed,
              elapsedMs := (← IO.monoMsNow) - started, diagnostic := some diagnostic
            }
  modify fun env => { env with smtEnv.deferredSessions := #[] }
  return failures

private def beginConfiguredChecks
    (command : SmtCommand) : TranslateEnvT (Array PendingCheck × Array SolverOutcome) := do
  let mut failures ← ensureConfiguredSessions
  let mut pending := #[]
  for solver in (← get).smtEnv.configuredSolvers do
    if !(failures.any (·.solver == solver)) then
      match ← startCheck solver command with
      | .pending check => pending := pending.push check
      | .failed outcome => failures := failures.push outcome
  return (pending, failures)

private def outcomeToResult (outcome : SolverOutcome) : Result :=
  match outcome.verdict with
  | some .valid => .Valid
  | some .falsified => .Falsified (outcome.counterexample.getD [])
  | _ => .Undetermined

private def logInfrastructureOutcomes (outcomes : Array SolverOutcome) : TranslateEnvT Unit := do
  for outcome in orderOutcomes outcomes.toList do
    if outcome.status != .completed && outcome.status != .modelFailed then
      logErrorAt (← blankRef)
        m!"{outcome.solver} infrastructure failure ({reprStr outcome.status}): {outcome.diagnostic.getD "no diagnostic"}"

private def completedOutcome (completion : PendingCompletion) :
    TranslateEnvT (SolverOutcome × Array PendingCheck) := do
  match completion with
  | .response check response remaining =>
      return (← finishCheck check response, remaining)
  | .timedOut check remaining =>
      return (← timeoutCheck check, remaining)

private def runSingleCheck (command : SmtCommand) : TranslateEnvT Result := do
  let (pending, failures) ← beginConfiguredChecks command
  if let some failure := failures[0]? then
    throwEnvError s!"{failure.solver} solver failure: {failure.diagnostic.getD "no diagnostic"}"
  let some _ := pending[0]?
    | throwEnvError "single solver session produced no check task"
  let (outcome, _) ← completedOutcome (← waitFirstPending pending)
  if outcome.status != .completed then
    throwEnvError s!"{outcome.solver} solver failure: {outcome.diagnostic.getD "no diagnostic"}"
  outcomeToResult <$> attachCounterexample outcome

private partial def runFirstCheck (command : SmtCommand) : TranslateEnvT Result := do
  let (pending, initialOutcomes) ← beginConfiguredChecks command
  loop pending initialOutcomes
 where
  loop (pending : Array PendingCheck) (outcomes : Array SolverOutcome) : TranslateEnvT Result := do
    if pending.isEmpty then
      let ordered := orderOutcomes outcomes.toList
      let ordinaryUndetermined :=
        !ordered.isEmpty && ordered.all fun outcome =>
          outcome.status == .completed && outcome.verdict == some .undetermined
      if ordinaryUndetermined then return .Undetermined
      logInfrastructureOutcomes outcomes
      let diagnostics := combineDiagnostics ordered |>.getD "no solver produced a verdict"
      throwEnvError s!"First mode produced no decisive verdict because solver infrastructure failed:\n{diagnostics}"
    let (outcome, remaining) ← completedOutcome (← waitFirstPending pending)
    let outcomes := outcomes.push outcome
    if outcome.verdict.any SolverVerdict.isDecisive then
      -- The verdict wins immediately, but its evidence is secured before any
      -- loser is retired so model latency cannot change the winner.
      let outcome ← attachCounterexample outcome
      for session in (← get).smtEnv.sessions do
        if session.solver != outcome.solver then
          discard <| retireAndCleanup session.solver true
      for check in remaining do
        let _ := check.response.get
      if (← get).optEnv.options.solverOptions.verbose ≥ 2 then
        IO.println s!"[blaster] first winner: {outcome.solver} ({outcome.elapsedMs}ms)"
      return outcomeToResult outcome
    loop remaining outcomes


private def runAgreementCheck (command : SmtCommand) : TranslateEnvT Result := do
  let (initialPending, initialOutcomes) ← beginConfiguredChecks command
  let mut pending := initialPending
  let mut outcomes := initialOutcomes
  while !pending.isEmpty do
    let (outcome, remaining) ← completedOutcome (← waitFirstPending pending)
    outcomes := outcomes.push outcome
    pending := remaining
  if let some failed := (orderOutcomes outcomes.toList).find? fun outcome =>
      outcome.status != .completed && outcome.status != .modelFailed then
    let diagnostic :=
      s!"{failed.solver} ended with {reprStr failed.status}: {failed.diagnostic.getD "no diagnostic"}"
    retireAllSessions true
    let artifact ← saveAgreementArtifacts diagnostic outcomes
    throwEnvError s!"{diagnostic}\nAgreement artifacts: {artifact.getD "unavailable"}"
  let mut enriched := #[]
  for solver in [SmtSolver.z3, SmtSolver.cvc5] do
    if let some outcome := outcomes.find? (·.solver == solver) then
      enriched := enriched.push (← attachCounterexample outcome)
  let some z3 := enriched.find? (·.solver == .z3)
    | retireAllSessions true
      let artifact ← saveAgreementArtifacts "Z3 produced no outcome" enriched
      throwEnvError s!"Agreement infrastructure failure: Z3 produced no outcome. Artifacts: {artifact.getD "unavailable"}"
  let some cvc5 := enriched.find? (·.solver == .cvc5)
    | retireAllSessions true
      let artifact ← saveAgreementArtifacts "cvc5 produced no outcome" enriched
      throwEnvError s!"Agreement infrastructure failure: cvc5 produced no outcome. Artifacts: {artifact.getD "unavailable"}"
  match aggregateAgreement z3 cvc5 with
  | .error failure =>
      retireAllSessions true
      let artifact ← saveAgreementArtifacts failure.diagnostic enriched
      throwEnvError s!"{failure.diagnostic}\nAgreement artifacts: {artifact.getD "unavailable"}"
  | .ok decision =>
      let incompleteModel := enriched.any (·.status == .modelFailed)
      if decision.verdict == .undetermined || incompleteModel then
        retireAllSessions true
        let reason :=
          if incompleteModel then "one or more model-evidence steps failed"
          else "both solvers returned ordinary Undetermined"
        let artifact ← saveAgreementArtifacts reason enriched
        logWarningAt (← blankRef)
          m!"Agreement diagnostics saved: {artifact.getD "unavailable"}"
      return outcomeToResult {
        solver := .z3, verdict := some decision.verdict, status := decision.status,
        counterexample := decision.counterexample, elapsedMs := decision.elapsedMs,
        diagnostic := decision.diagnostic
      }

private def checkSatWith (command : SmtCommand) : TranslateEnvT Result := do
  let deferred := (← get).smtEnv.deferredSessions
  modify fun env =>
    { env with smtEnv.solverRecords := env.smtEnv.solverRecords.map fun record =>
        { record with
          checkCommand := some command
          stdout := if deferred.contains record.solver then record.stdout else #[]
          modelCommands := #[]
          modelResponses := #[]
          failedStage := if deferred.contains record.solver then record.failedStage else none
          failedCommand := if deferred.contains record.solver then record.failedCommand else none
          failureResponse := if deferred.contains record.solver then record.failureResponse else none
          failureElapsedMs := if deferred.contains record.solver then record.failureElapsedMs else none } }
  if (← get).optEnv.options.solverOptions.onlySmtLib then return .Undetermined
  match (← get).optEnv.options.solverOptions.solverMode with
  | .single => runSingleCheck command
  | .first => runFirstCheck command
  | .agree => runAgreementCheck command

/-- Check satisfiability of the shared canonical query. -/
def checkSat : TranslateEnvT Result :=
  checkSatWith .checkSat

/-- Incremental check over the same pair of sessions and shared assumptions. -/
def checkSatAssuming (args : Array SmtTerm) : TranslateEnvT Result :=
  checkSatWith (.checkSatAssuming args)

/-- Proof retrieval remains a single-session operation. -/
def getProof : TranslateEnvT String := do
  let some session := (← get).smtEnv.sessions[0]? | return ""
  match ← sendCommandToSession session .getProof false with
  | .error error => throwSessionCommandError session "proof retrieval" .getProof error
  | .ok () =>
      match ← awaitTaskCancelable
          (← IO.asTask (getOutputProof session.process.stdout) Task.Priority.dedicated) with
      | .ok proof => return proof
      | .error error =>
          throwSessionCommandError session "proof retrieval" .getProof (toString error)

/-- Gracefully retire and reap every remaining solver session. -/
def exitSmt : TranslateEnvT UInt32 := do
  retireAllSessions false
  return 0


/-- Validate option combinations before starting any child process. -/
def validateSolverOptions (sOpts : BlasterOptions) : Except String Unit := do
  if sOpts.solverMode != .single && sOpts.solver.isSome then
    throw "❌ `solver` conflicts with `solver-mode: first` and `solver-mode: agree`; concurrent modes always run both Z3 and cvc5."
  if sOpts.solverMode != .single && sOpts.onlySmtLib then
    throw "❌ `only-smt-lib` cannot be combined with concurrent solver modes."

private def configuredSolvers (sOpts : BlasterOptions) : IO (Array SmtSolver) := do
  match sOpts.solverMode with
  | .single => return #[← resolveSolver sOpts]
  | .first | .agree => return #[.z3, .cvc5]

/-- Resolve options, create independent sessions, and send only each backend's
    setup transcript. Subsequent translation commands are broadcast once from
    the canonical query path. -/
def setBlasterProcess : TranslateEnvT Unit := do
  let original := (← get).optEnv.options.solverOptions
  match validateSolverOptions original with
  | .error error => throwEnvError error
  | .ok () => pure ()
  let timeout ← resolveTimeout original
  let sOpts := { original with timeout }
  let solvers ← configuredSolvers sOpts
  modify fun env =>
    { env with
      smtEnv.configuredSolvers := solvers,
      smtEnv.singleSolver := if sOpts.solverMode == .single then solvers[0]? else none,
      optEnv.options.solverOptions := sOpts }
  if sOpts.onlySmtLib then
    for solver in solvers do
      let desc := solver.descriptor
      let candidate := desc.candidates[0]!
      let (cmd, args) := desc.spawnInvocation candidate
      upsertSolverRecord {
        solver,
        version := "not probed (only-smt-lib)",
        commandLine := String.intercalate " " (cmd :: args.toList),
        setupCommands := solverSetupCommands solver sOpts,
        timeoutMs := sOpts.timeout.map (· * 1000)
      }
  else
    for solver in solvers do
      match ← spawnAndInitializeSolver solver false with
      | .ok () => pure ()
      | .error error =>
          throwEnvError s!"❌ Failed to initialize required {solver} solver: {error}"


end Blaster.Smt
