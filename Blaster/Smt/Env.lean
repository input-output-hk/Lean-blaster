import Lean
import Blaster.Command.Options
import Blaster.Optimize.Env
import Blaster.Smt.EmitCommand
import Blaster.Smt.SolverConfig

open Lean Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

/-- Normalize solver output line endings: strip any `\r` so that downstream
    code only sees Unix-style `\n` terminators, regardless of platform. -/
private def normalizeLine (s : String) : String :=
  s.replace "\r" ""

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


def blankRef : TranslateEnvT Syntax := getRef

def logResult (r : Result) (isCTI := false) (indLabel := "") (cexLabel := "Counterexample") : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
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
      if isExpectedUndetermined sOpts.solveResult
      then logInfoAt ref "✅ Expected Undetermined"
      else logWarningAt ref "⚠️ Undetermined"

  where
    dumpCex (f : MessageData -> MetaM Unit) (failure : String) (cex : List String) : TranslateEnvT Unit := do
      if (← get).optEnv.options.solverOptions.generateCex then
         f failure
         f s!"{cexLabel}:"
         cex.forM (λ s => f s!" - {s.dropRight 1}")
      else f failure

/-- Tries to find the backend solver binary among `cfg.candidates`:
    natively in PATH first, then through WSL. -/
private def findSolverCmd (cfg : SolverConfig) : IO String := do
  -- We'll store a short log message for each candidate attempt
  let mut attemptLogs := #[]
  for candidate in cfg.candidates do
    try
      let out ← IO.Process.output { cmd := candidate, args := #[cfg.versionFlag] }
      if out.exitCode == 0 then
        -- Found a good candidate => Return immediately
        return candidate
      else
        attemptLogs := attemptLogs.push
          s!"Candidate '{candidate}': exit code {out.exitCode}"
    catch e =>
      -- “No such file or directory” or other IO error
      attemptLogs := attemptLogs.push
        s!"Candidate '{candidate}': IO error => {e}"

  -- If we get here, no candidate succeeded
  let attemptsReport := String.join (attemptLogs.toList.map (fun x => x ++ "\n"))
  throw <| IO.userError s!"❌ Could not find a working {cfg.displayName} ≥ {cfg.minVersion}.\n\nTried:\n{attemptsReport}"

/-- Spawn the backend solver process described by `cfg`. -/
def createBlasterProcess (cfg : SolverConfig) : IO (IO.Process.Child ⟨.piped, .piped, .piped⟩) := do
  let solverCmd ← findSolverCmd cfg  -- ensures the binary is present
  IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := solverCmd
    args   := cfg.spawnArgs
  }

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

/-- Check if cancel token has been triggered and kill all running
    Solver instances (if necessary).
-/
def checkCancelTk? : TranslateEnvT Unit := do
  let procs := (← get).smtEnv.smtProcs
  if procs.isEmpty then return ()
  if let some tk := (← readThe Core.Context).cancelTk? then
    if ← tk.isSet then
      for (_, p) in procs do
        p.kill
        discard $ p.wait
      throwInterruptException

/-- Retrieve model output from `h` when a counterexample is generated.
    NOTE: A model output starts with "(" and ends with ")\n".
    Line endings are normalized to handle both Unix (LF) and Windows (CRLF).
-/
partial def getOutputModel (h : IO.FS.Handle) (proof := false) : TranslateEnvT String := do
  let rec loop (acc : String) : TranslateEnvT String := do
    checkCancelTk?
    let line := normalizeLine (← h.getLine)
    if (line == ")\n" && !proof) || (line == "\n" && proof) then
      return acc
    else loop (acc ++ line)
  loop ""

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

/-- Retrieve an `eval` output from `h` after execution `(eval t)`
    NOTE: An eval output may either correspond to a scalar value
    or to an inductive datatype one. In the latter case it's provided
    within parenthesis. The number of opening and closing parenthesis
    should tally to stop reading from `h`.
-/
partial def getOutputEval (h : IO.FS.Handle) : IO String := do
  let line := normalizeLine (← h.getLine)
  if line.get! 0 != '(' then return line
  getIndValue line (tallyParenthesis line 0)

 where
  tallyParenthesis (s : String) (tally : Int) : Int :=
   s.foldr (λ c acc =>
              match c with
              | '(' => acc + 1
              | ')' => acc - 1
              | _ => acc) tally
  getIndValue (acc : String) (tally : Int) : IO String := do
    if tally == 0 then return acc
    else
      let line := normalizeLine (← h.getLine)
      getIndValue (acc ++ line) (tallyParenthesis line tally)

/-- Push smt command `c` in the translation environment only when sOpts.dumpSmtLib is set -/
def storeCommand (c : SmtCommand) : TranslateEnvT Unit := do
  if (← get).optEnv.options.solverOptions.dumpSmtLib then
    modify (fun env => { env with smtEnv.smtCommands := env.smtEnv.smtCommands.push c })
  else pure ()

/-- Return `true` when at least one solver process has been initialized -/
def isSmtProcSet : TranslateEnvT Bool :=
  return !(← get).smtEnv.smtProcs.isEmpty

/-- Set the process index used by the low-level emit/read functions. -/
@[always_inline, inline]
def setCurrentProcIdx (i : Nat) : TranslateEnvT Unit :=
  modify (fun env => { env with smtEnv.currentProcIdx := i })

/-- Push smt command `c` in the translation environment only when sOpts.dumpSmtLib is set.
    The command is piped to the backend solver processes if any have been created:
    to every process by default, or only to process `only` when provided.
    An error is triggered when the `checkSuccess` flag is set and
    no `success` output is produced by a receiving process.
    NOTE: The `checkSuccess` is to be set only for Smt command that
    are NOT expected to produce any output.
-/
partial def trySubmitCommand! (c : SmtCommand) (checkSuccess := true) (only : Option Nat := none) : TranslateEnvT Unit := do
  storeCommand c
  let procs := (← get).smtEnv.smtProcs
  if procs.isEmpty then return ()
  let indices := match only with
    | some i => #[i]
    | none => Array.ofFn (n := procs.size) (·.val)
  for i in indices do
    setCurrentProcIdx i
    c.emit
    if checkSuccess then
      let h ← getProcStdOut
      let out := normalizeLine (← h.getLine)
      match out with
      | "success\n" => pure ()
      | err =>
          let name := match procs[i]? with
            | some p => p.1.config.displayName
            | none => "?"
          throwEnvError s!"Unexpected smt error: {err} for {c} ({name})"

/-- Same as trySubmitCommand! but with flag `checkSuccess` set to `false`.
-/
def submitCommand (c : SmtCommand) (only : Option Nat := none) : TranslateEnvT Unit := do
  trySubmitCommand! c (checkSuccess := false) (only := only)


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

/-- Unwrap a `(get-value (t))` response of shape `((t value))` and return the
    bare value string followed by a newline — the same shape Z3's `(eval t)`
    produces, so downstream counterexample rendering is solver-independent.
    Assumes the queried term is a single symbol (which holds for the only
    caller, `getModel.getVarValue`; SMT symbols never contain spaces). -/
def unwrapGetValue (s : String) : String :=
  let inner := ((s.trim.drop 2).dropRight 2).trim
  let val := match inner.splitOn " " with
    | [] => inner
    | _ :: rest => String.intercalate " " rest
  val.trim ++ "\n"

/-- Try to retrieve to evaluate term `t` when a `sat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elaborator to parse produced value
    and generate the corresponding Lean representation.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the Smt process is not defined.
-/
def evalTerm (t : SmtTerm) : TranslateEnvT String := do
  let env ← get
  let idx := env.smtEnv.currentProcIdx
  let some (solver, p) := env.smtEnv.smtProcs[idx]? | return ""
  checkCancelTk?
  -- model values are queried only on the process that answered `sat`,
  -- using that solver's query style
  if solver.config.usesGetValue then
    submitCommand (.getValue t) (only := some idx)
    return unwrapGetValue (← getOutputEval p.stdout)
  else
    submitCommand (.evalTerm t) (only := some idx)
    getOutputEval p.stdout

/-- Try to retrieve the model when a `sat` result is obtained and dump result to stdout.
    Do nothing when:
      - No solver instance is defined
      - Option solverOptions.generateCex is set to `false`
    TODO: We need to define the Smt-lib syntax and term elaborator to parse produced model
    and generate the corresponding Lean representation.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
-/
def getModel : TranslateEnvT (List String) := do
  let env ← get
  let idx := env.smtEnv.currentProcIdx
  let some (_, p) := env.smtEnv.smtProcs[idx]? | return []
  let topVars := env.smtEnv.topLevelVars
  if !env.optEnv.options.solverOptions.generateCex then return []
  checkCancelTk?
  if topVars.isEmpty
  then
    submitCommand (.getModel) (only := some idx)
    let s ← getOutputModel p.stdout
    return [s]
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

/-- Raw check-sat answer of a single solver process. -/
private inductive SatAnswer where
  | sat
  | unsat
  | unknown
deriving Repr, DecidableEq, Inhabited

private def parseSatAnswer (solverName : String) (line : String) : TranslateEnvT SatAnswer := do
  match normalizeLine line with
  | "sat\n"     => return .sat
  | "unsat\n"   => return .unsat
  | "unknown\n" => return .unknown -- unknown is also returned when timeout is set to stdin
  | err => throwEnvError s!"checkSat: Unexpected check-sat result: {err} ({solverName})"

/-- Convert the answer of process `i` to a `Result`, pinning the current
    process index to `i` first so that model retrieval reads from the
    answering solver. -/
private def satAnswerToResult (i : Nat) (a : SatAnswer) : TranslateEnvT Result := do
  setCurrentProcIdx i
  match a with
  | .sat => return (.Falsified (← getModel))
  | .unsat => return .Valid
  | .unknown => return .Undetermined

/-- Retrieve and join the check-sat answers of all running solver processes
    according to the selected `SolverChoice`. Must be called right after a
    `check-sat`/`check-sat-assuming` has been submitted to every process.

     - `one`: single process, its answer is the result (historical behavior).
     - `any`: the first *definitive* answer (`sat`/`unsat`) wins; every other
       process is killed and dropped, and the run continues with the winner
       only. All-unknown → `Undetermined` (all processes kept).
     - `all`: wait for every answer. `sat` vs `unsat` disagreement is a hard
       error (soundness alarm). A definitive answer next to `unknown` stands,
       but a warning lists the per-solver verdicts (tracking signal for tests
       not discharged by every solver).
-/
partial def getSatResults : TranslateEnvT Result := do
  let env ← get
  let procs := env.smtEnv.smtProcs
  let choice := env.optEnv.options.solverOptions.solver
  let tasks ← procs.mapM (fun p => IO.asTask p.2.stdout.getLine)
  match choice, procs.size with
  | _, 0 => return .Undetermined
  | .any, n =>
      if n == 1 then waitSingle tasks[0]! else waitAny procs tasks
  | _, _ =>
      -- `.one` has a single process; `.all` joins all answers
      if procs.size == 1 then waitSingle tasks[0]!
      else waitAll procs tasks

 where
   solverNameAt (procs : Array (SmtSolver × IO.Process.Child ⟨.piped, .piped, .piped⟩)) (i : Nat) : String :=
     match procs[i]? with
     | some p => p.1.config.displayName
     | none => "?"

   waitSingle (t : Task (Except IO.Error String)) : TranslateEnvT Result := do
     checkCancelTk?
     if ← IO.hasFinished t then
       let procs := (← get).smtEnv.smtProcs
       let a ← parseSatAnswer (solverNameAt procs 0) (← IO.ofExcept t.get)
       satAnswerToResult 0 a
     else
       IO.sleep 20
       waitSingle t

   /-- `any` mode: poll until a process gives a definitive answer; kill the
       others and narrow `smtProcs` to the winner. -/
   waitAny (procs : Array (SmtSolver × IO.Process.Child ⟨.piped, .piped, .piped⟩))
       (tasks : Array (Task (Except IO.Error String))) : TranslateEnvT Result := do
     let rec loop (answers : Array (Option SatAnswer)) : TranslateEnvT Result := do
       checkCancelTk?
       let mut answers := answers
       for h : i in [0:procs.size] do
         if answers[i]!.isNone then
           if ← IO.hasFinished tasks[i]! then
             let a ← parseSatAnswer (solverNameAt procs i) (← IO.ofExcept (tasks[i]!).get)
             if a != .unknown then
               -- winner: kill and drop every other process
               for h' : j in [0:procs.size] do
                 if j != i then
                   procs[j].2.kill
                   discard $ procs[j].2.wait
               modify (fun env => { env with smtEnv.smtProcs := #[procs[i]] })
               return (← satAnswerToResult 0 a)
             answers := answers.set! i (some a)
       if answers.all (· == some .unknown) then
         return .Undetermined
       IO.sleep 20
       loop answers
     loop (Array.replicate procs.size none)

   /-- `all` mode: wait for every answer and cross-check. -/
   waitAll (procs : Array (SmtSolver × IO.Process.Child ⟨.piped, .piped, .piped⟩))
       (tasks : Array (Task (Except IO.Error String))) : TranslateEnvT Result := do
     let rec collect (answers : Array (Option SatAnswer)) : TranslateEnvT (Array SatAnswer) := do
       checkCancelTk?
       let mut answers := answers
       for h : i in [0:procs.size] do
         if answers[i]!.isNone then
           if ← IO.hasFinished tasks[i]! then
             answers := answers.set! i (some (← parseSatAnswer (solverNameAt procs i) (← IO.ofExcept (tasks[i]!).get)))
       if answers.all (·.isSome) then
         return answers.map (·.get!)
       IO.sleep 20
       collect answers
     let answers ← collect (Array.replicate procs.size none)
     let verdicts := String.intercalate ", " (List.ofFn (n := answers.size)
       fun i => s!"{solverNameAt procs i} → {satAnswerStr answers[i]!}")
     if answers.contains .sat && answers.contains .unsat then
       throwEnvError s!"Solver disagreement (soundness alarm): {verdicts}"
     if answers.contains .unknown && answers.any (· != .unknown) then
       logWarningAt (← getRef) s!"⚠️ Solvers disagree on decidability: {verdicts}"
     match answers.findIdx? (· == .sat) with
     | some i => satAnswerToResult i .sat
     | none =>
       match answers.findIdx? (· == .unsat) with
       | some i => satAnswerToResult i .unsat
       | none => return .Undetermined

   satAnswerStr : SatAnswer → String
     | .sat => "sat"
     | .unsat => "unsat"
     | .unknown => "unknown"

/-- Check satisfiability of current Smt query and return the result.
    An error is triggered when an unexpected check-sat result is obtained.
    Return `Undetermined` when no Smt process is defined.
-/
def checkSat : TranslateEnvT Result := do
  if (← get).smtEnv.smtProcs.isEmpty then return .Undetermined
  submitCommand (.checkSat)
  getSatResults

/-- Check satisfiability of current Smt query by assuming the provided terms
    and return the result.
    An error is triggered when an unexpected check-sat result is obtained.
    Return `Undetermined` when no Smt process is defined.
-/
def checkSatAssuming (args : Array SmtTerm) : TranslateEnvT Result := do
  if (← get).smtEnv.smtProcs.isEmpty then return .Undetermined
  submitCommand (.checkSatAssuming args)
  getSatResults


/-- Try to retrieve the proof artifact when a `unsat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elaborator to parse and reconstruct
    the proof in Lean.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the Smt process is not defined.
-/
def getProof : TranslateEnvT String := do
  let env ← get
  let idx := env.smtEnv.currentProcIdx
  let some (_, p) := env.smtEnv.smtProcs[idx]? | return ""
  submitCommand (.getProof) (only := some idx)
  getOutputProof p.stdout



/-- Try to terminate all Smt processes.
    Do nothing if no Smt process is defined.
-/
def exitSmt : TranslateEnvT UInt32 := do
 let env ← get
 if env.smtEnv.smtProcs.isEmpty then return 0
 submitCommand (.exitSmt)
 let mut code : UInt32 := 0
 for (_, p) in env.smtEnv.smtProcs do
   let (_, p) ← p.takeStdin
   code ← p.wait
 modify (fun env => { env with smtEnv.smtProcs := #[], smtEnv.currentProcIdx := 0 })
 return code


/-- Set the Smt logic to `ALL`. -/
def setLogicAll : TranslateEnvT Unit :=
  trySubmitCommand! (.setLogic "ALL")

/-- Set the Smt random seed option (solver-specific option name) to `n` or none. -/
def setRandomSeed (cfg : SolverConfig) (n : Option Nat) (only : Option Nat := none) : TranslateEnvT Unit := do
  match n with
  | some n => trySubmitCommand! (.setOption cfg.seedOption (toString n)) (only := only)
  | none => pure ()

/-- Set Smt `smt.case_split` to `n`, with n ∈ [0..6]. -/
def setCaseSplit (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.case_split" (toString n))

/-- Set Smt `smt.qi.eager_threshold` to `n`. -/
def setQiEagerThreshold (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.qi.eager_threshold" (toString n))


/-- Set Smt `smt.delay_units` to `b`. -/
def setDelayUnits (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.delay_units" (toString b))

/-- Set Smt `smt.relevancy` option to `i`. -/
def setRelevancy (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.relevancy" (toString n))

/-- Set the Smt timeout (solver-specific option name, in milliseconds)
    when the option is specified. -/
def setTimeout (cfg : SolverConfig) (only : Option Nat := none) : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let some n := sOpts.timeout | return ()
  -- need to convert timeout to milliseconds
  trySubmitCommand! (.setOption cfg.timeoutOption (toString (n * 1000))) (only := only)

/-- Set the default Smt options of every selected backend solver: for each
    solver, its `SolverConfig.defaultOptions` pairs in order, followed by the
    random seed and timeout when provided in the solver options. Each option
    set is sent only to the corresponding solver process (solvers reject each
    other's option names). -/
def setDefaultSmtOptions (sOpts : BlasterOptions) : TranslateEnvT Unit := do
  let solvers := sOpts.solver.solvers
  for h : i in [0:solvers.size] do
    let cfg := solvers[i].config
    for (opt, val) in cfg.defaultOptions do
      trySubmitCommand! (.setOption opt val) (only := some i)
    setRandomSeed cfg sOpts.randomSeed (only := some i)
    setTimeout cfg (only := some i)

/-- Perform the following actions:
     - when option `only-smt-lib` is set to `false`:
       - Spawn one backend solver process per selected solver and update TranslateEnv
       - set the default smt solver options by emitting the corresponding commands
     - when option `only-smt-lib` is set to `true`:
       - only add the solver options to the list of smt commands.
-/
def setBlasterProcess : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  unless sOpts.onlySmtLib do
    let mut procs := #[]
    for s in sOpts.solver.solvers do
      procs := procs.push (s, ← createBlasterProcess s.config)
    modify (fun env => { env with smtEnv.smtProcs := procs, smtEnv.currentProcIdx := 0 })
  setDefaultSmtOptions sOpts


end Blaster.Smt
