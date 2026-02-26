import Lean
import Blaster.Command.Options
import Blaster.Optimize.Env
import Blaster.Smt.EmitCommand

open Lean Meta Blaster.Optimize Blaster.Options

namespace Blaster.Smt

/-- Minimal version of z3 we support -/
private def minZ3Version : String := "4.15.2"

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


def blankRef : TranslateEnvT Syntax := do
  let pos ← getRefPos
  return Syntax.atom (SourceInfo.original "".toSubstring pos "  ".toSubstring pos) ""

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

/-- Tries to find if z3 is natively present in PATH, if not checks wsl z3 -/
private def findZ3CmdAndVersion : IO (String) := do
  let candidates := #["z3", "wsl z3"]
  -- We'll store a short log message for each candidate attempt
  let mut attemptLogs := #[]
  for candidate in candidates do
    try
      let out ← IO.Process.output { cmd := candidate, args := #["-version"] }
      if out.exitCode == 0 then
        -- Found a good candidate => Return immediately
        return (candidate)
      else
        attemptLogs := attemptLogs.push
          s!"Candidate '{candidate}': exit code {out.exitCode}"
    catch e =>
      -- “No such file or directory” or other IO error
      attemptLogs := attemptLogs.push
        s!"Candidate '{candidate}': IO error => {e}"

  -- If we get here, no candidate succeeded
  let attemptsReport := String.join (attemptLogs.toList.map (fun x => x ++ "\n"))
  throw <| IO.userError s!"❌ Could not find a working Z3 ≥ {minZ3Version}.\n\nTried:\n{attemptsReport}"


/-- Spawn a z3 process w.r.t. the provided solver options. -/
def createBlasterProcess : IO (IO.Process.Child ⟨.piped, .piped, .piped⟩) := do
  let z3Cmd ← findZ3CmdAndVersion  -- ensures version is OK
  IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := z3Cmd
    args   := #["-in", "-smt2"]
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

/-- Retrieve model output from `h` when a counterexample is generated.
    NOTE: A model output starts with "(" and ends with ")\n"
-/
partial def getOutputModel (h : IO.FS.Handle) (proof := false) : TranslateEnvT String := do
  let rec loop (acc : String) : TranslateEnvT String := do
    checkCancelTk?
    let line ← h.getLine
    if ((line == ")\n" || line == ")\r\n") && !proof) || ((line == "\n" || line == "\r\n") && proof) then
      return acc
    else loop (acc ++ line)
  loop ""

/-- Retrieve proof output for an `unsat` result.
    NOTE: A proof output starts with "(proof" and ends with ")\n\n".
-/
def getOutputProof := λ h => getOutputModel h true

/-- Retrieve error msg from 'h'.
    NOTE: An error msg starts with "(error" and ends with ")\n".
-/
partial def getErrorMsg (h : IO.FS.Handle) : IO String := h.getLine

/-- Retrieve an `eval` output from `h` after execution `(eval t)`
    NOTE: An eval output may either correspond to a scalar value
    or to an inductive datatype one. In the latter case it's provided
    within parenthesis. The number of opening and closing parenthesis
    should tally to stop reading from `h`.
-/
partial def getOutputEval (h : IO.FS.Handle) : IO String := do
  let line ← h.getLine
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
      let line ← h.getLine
      getIndValue (acc ++ line) (tallyParenthesis line tally)

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
  let out ← h.getLine
  match out with
  | "success\n" | "success\r\n" => return ()
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

/-- Given `s` and smt symbol `t` and smt sort and optional `assertFlag` boolean value, perform the following:
     - When `assertFlag = some b`:
        - define smt predicate `(define-fun s ((@x t)) Bool b)`
     - Otherwise:
        - declare smt predicate `(declare-fun s ((t)) Bool)`
   Assume that `s` is defined as `@is{xxx}`
-/
def definePredQualifier (s : SmtSymbol) (t : SortExpr) (assertFlag : Option Bool) : TranslateEnvT Unit := do
 match assertFlag with
 | some b =>
      let xsym := mkReservedSymbol "@x"
      let boolSmt := if b then trueSmt else falseSmt
      defineFun s #[(xsym, t)] boolSort boolSmt
 | none => declareFun s #[t] boolSort


/-- Perform the following actions:
     - Declare smt universal sort `(declare-sort @@Type 0)`
     - Define smt predicate `(define-fun @isType ((@x @@Type)) Bool true)`
    Assume `isTypeSym := @isType`
-/
def defineTypeSort (isTypeSym : SmtSymbol) : TranslateEnvT Unit := do
  declareSort typeSymbol 0
  definePredQualifier isTypeSym typeSort (some true)


/-- Perform the following actions:
     - Declare Empty sort in Smt Lib
     - Define smt predicate `(define-fun @isEmpty ((@x Empty)) Bool false)`
    Assume `isEmptySym := @isEmpty`
-/
def defineEmptySort (isEmptySym : SmtSymbol) : TranslateEnvT Unit := do
  declareSort emptySymbol 0
  definePredQualifier isEmptySym emptySort (some false)

/-- Perform the following actions:
     - Declare PEmpty sort in Smt Lib
     - Define smt predicate `(define-fun @isPEmpty ((@x PEmpty)) Bool false)`
    Assume `isPEmptySym := @isPEmpty`
-/
def definePEmptySort (isPEmptySym : SmtSymbol) : TranslateEnvT Unit := do
  declareSort pemptySymbol 0
  definePredQualifier isPEmptySym pemptySort (some false)


/-- Perform the following actions:
     - Define Prop sort in Smt Lib, which is an alias to Bool Smt Sort
     - Define smt predicate `(define-fun @isProp ((@x Prop)) Bool true)`
    Assume `isPropSym := @isProp`
-/
def definePropSort (isPropSym : SmtSymbol) : TranslateEnvT Unit := do
  defineSort propSymbol none boolSort
  definePredQualifier isPropSym propSort (some true)

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

/-- Try to retrieve to evaluate term `t` when a `sat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elaborator to parse produced value
    and generate the corresponding Lean representation.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the Smt process is not defined.
-/
def evalTerm (t : SmtTerm) : TranslateEnvT String := do
  let env ← get
  let some p := env.smtEnv.smtProc | return ""
  checkCancelTk?
  submitCommand (.evalTerm t)
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
  let some p := env.smtEnv.smtProc | return []
  let topVars := env.smtEnv.topLevelVars
  if !env.optEnv.options.solverOptions.generateCex then return []
  checkCancelTk?
  if topVars.isEmpty
  then
    submitCommand (.getModel)
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
       match ← IO.ofExcept res.get with
       | "sat\n" | "sat\r\n"    => return (.Falsified (← getModel))
       | "unsat\n" | "unsat\r\n"    => return .Valid
       | "unknown\n" | "unknown\r\n" => return .Undetermined -- unknown is also return when timeout is set to stdin
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

/-- Set Smt `smt.mbqi` option to `b`. -/
def setMbqi (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.mbqi" (toString b))

/-- Set Smt `smt.pull-nested-quantifiers` option to `b`. -/
def setPullNestedQuantifiers (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.pull-nested-quantifiers" (toString b))

/-- Set Smt `print-success` option to `b`. -/
def setPrintSuccess (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":print-success" (toString b))

/-- Set Smt `smt.random-seed` option to `n` or none. -/
def setRandomSeed (n : Option Nat) : TranslateEnvT Unit := do
  match n with
  | some n => trySubmitCommand! (.setOption ":smt.random-seed" (toString n))
  | none => pure ()

/-- Set Smt `auto_config` option to `b`. -/
def setAutoConfig (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":auto_config" (toString b))

/-- Set Smt `smt.case_split` to `n`, with n ∈ [0..6]. -/
def setCaseSplit (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.case_split" (toString n))

/-- Set Smt `smt.qi.eager_threshold` to `n`. -/
def setQiEagerThreshold (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.qi.eager_threshold" (toString n))


/-- Set Smt `smt.delay_units` to `b`. -/
def setDelayUnits (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.delay_units" (toString b))

/-- Set Smt `smt.macro_finder` option to `b`. -/
def setMacroFinder (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.macro_finder" (toString b))

/-- Set Smt `smt.relevancy` option to `i`. -/
def setRelevancy (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt.relevancy" (toString n))

/-- Set Smt `timeout` when option is specified. -/
def setTimeout : TranslateEnvT Unit := do
  let sOpts := (← get).optEnv.options.solverOptions
  let some n := sOpts.timeout | return ()
  -- need to convert timeout to milliseconds
  trySubmitCommand! (.setOption ":timeout" (toString (n * 1000)))

/-- Set the default Smt options, i.e.:
     - (set-option :print-success true)
     - (set-option :produce-models true)
     - (set-option :produce-proofs true)
     - (set-option :smt-pull-nested-quantifiers true)
     - (set-option :smt-mbqi true)
     - (set-option :auto_config false)
     - (set-option :smt.random-seed n) when `n` is provided in solver options
     - (set-option :smt.macro_finder true)
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

/-- Perform the following actions:
     - when option `only-smt-lib` is set to `false`:
       - Spawn the backend solver process and update TranslateEnv
       - set the default smt solver options by emitting the corresponding commands
     - when option `only-smt-lib` is set to `true`:
       - only add the solver options to the list of smt commands.
-/
def setBlasterProcess : TranslateEnvT Unit := do
  let env ← get
  let sOpts := env.optEnv.options.solverOptions
  unless sOpts.onlySmtLib do
    let proc ← createBlasterProcess
    set { env with smtEnv.smtProc := proc }
  setDefaultSmtOptions sOpts


end Blaster.Smt
