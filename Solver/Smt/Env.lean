import Lean
import Solver.Command.Options
import Solver.Optimize.Env

open Lean Meta Solver.Optimize Solver.Options

namespace Solver.Smt

/-- Result of an SMT query. -/
inductive Result where
  | Valid        : Result
  | Falsified    : Result
  | Undetermined : Result
deriving Repr, DecidableEq


def toResult (e : Expr) : Result :=
 match e with
 | Expr.const ``True _  => Result.Valid
 | Expr.const ``False _  => Result.Falsified
 | _ => Result.Undetermined


/-- Spawn a z3 process w.r.t. the provided solver options. -/
def createSolverProcess (sOpts : SolverOptions) : IO (IO.Process.Child ⟨.piped, .piped, .piped⟩) := do
 let sec :=
     match sOpts.timeout with
      | none => ""
      | some n => s!"-T:{n}"
 IO.Process.spawn {
   stdin := .piped
   stdout := .piped
   stderr := .piped
   cmd := "z3"
   args := #["-in", "-smt2", sec]
 }

/-- Spawn the backend solver process and update TranslateEnv only when `spawnSolver` is set to `true`.
    Otherwise do nothing.
-/
def setSolverProcess (sOpts : SolverOptions) (env: TranslateEnv) : IO TranslateEnv := do
  if sOpts.onlySmtLib
  then
    let proc ← createSolverProcess sOpts
    let smtEnv := {env.smtEnv with smtProc := proc}
    return {env with smtEnv := smtEnv}
  else return env

/-- Update translation cache with `a := b`.
-/
def updateTranslateCache (a : Expr) (b : SmtTerm) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := {env.smtEnv with translateCache := env.smtEnv.translateCache.insert a b}
  set {env with smtEnv := smtEnv}


/-- Return `b` if `a := b` is already in the translation cache.
    Otherwise, the following actions are performed:
      - execute `b ← fun ()`
      - update cache with `a := b`
      - return b
-/
def withTranslateEnvCache (a : Expr) (f : Unit → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let env ← get
  match env.smtEnv.translateCache.find? a with
  | some b => return b
  | none => do
     let b ← f ()
     updateTranslateCache a b
     return b

/-- Retrieve all msg from stdout. -/
def getOutput (proc : (IO.Process.Child ⟨.piped, .piped, .piped⟩)) : IO String := do
 let mut out ← proc.stdout.getLine
 let mut msg := out
 while !out.isEmpty do
   out ← proc.stdout.getLine
   msg := s!"{msg}\n {out}"
 return msg

/-- Push smt command `c` in the translation environment and forward it
    to the backend solver if the corresponding process has been created.
    An error is triggered when the `checkSuccess` flag is set and
    not `success` output is produced.
    NOTE: The `checkSuccess` is to be set only for SMT command that
    are NOT expected to produce any output.
-/
def trySubmitCommand! (c : SmtCommand) (checkSuccess := true) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := { env.smtEnv with smtCommands := env.smtEnv.smtCommands.push c }
  set {env with smtEnv := smtEnv }
  let some p := env.smtEnv.smtProc | return ()
  p.stdin.putStr s!"{c}"
  p.stdin.flush
  if !checkSuccess then return ()
  let mut out ← p.stdout.getLine
  match out with
  | "success" => return ()
  | _ =>
    let err ← getOutput p
    throwError s!"Unexpected smt error:\n {err}"

/-- Same as trySubmitCommand! but with flag `checkSuccess` set to `false`.
-/
def submitCommand (c : SmtCommand) : TranslateEnvT Unit :=
  trySubmitCommand! c (checkSuccess := false)


/-- Declare a free variable with name `id` and sort `t`. -/
def declareConst (id : SmtSymbol) (t : SortExpr) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareConst id t)

/-- Declare an inductive type in SMT lib with name `nm` and body `decl`. -/
def declareDataType (nm : SmtSymbol) (decl : SmtDatatypeDecl) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareDataType nm decl)

/-- Declare mutual inductive types in SMT lib with names `nms` and bodies `decls`.
    An error is triggered if nms.size ≠ decls.size.
-/
def declareMutualDataTypes (nms : Array SmtSortDecl) (decls : Array SmtDatatypeDecl) : TranslateEnvT Unit := do
  if nms.size != decls.size then throwError s!"declareMutualDataTypes: names and declarations mismatched: {nms} ≠ {decls}"
  trySubmitCommand! (.declareMutualDataTypes nms decls)

/-- Declare an uninterpreted function with name `nm`, arguments `args` and return type `rt`. -/
def declareFun (nm : SmtSymbol) (args: Array SortExpr) (rt : SortExpr) : TranslateEnvT Unit :=
   trySubmitCommand! (.declareFun nm args rt)

/-- Define a function with name `nm`, parameters `args`, return type `rt` and body `b`. -/
def defineFun (nm : SmtSymbol) (args : SortedVars) (rt : SortExpr) (b : SmtTerm) : TranslateEnvT Unit :=
  trySubmitCommand! (.defineFun false nm args rt b)

/-- Define a recursive function with name `nm`, parameters `args`, return type `rt` and body `b`. -/
def defineFunRec (nm : SmtSymbol) (args : SortedVars) (rt : SortExpr) (b : SmtTerm) : TranslateEnvT Unit :=
  trySubmitCommand! (.defineFun true nm args rt b)

/-- Define mutually recursive functions with declarations `decls` and bodies `bs`.
    An error is triggered if decls.size ≠ bs.size.
-/
def defineMutualFuns (decls : Array SmtFunDecl) (bs : Array SmtTerm) : TranslateEnvT Unit := do
  if decls.size != bs.size then throwError s!"defineMutualFuns: declarations and bodies mismatched: {decls} ≠ {bs}"
  trySubmitCommand! (.defineFunsRec decls bs)


/-- Declare a sort with name `nm` and arity `n`. -/
def declareSort (nm : SmtSymbol) (n : Nat) : TranslateEnvT Unit :=
  trySubmitCommand! (.declareSort nm n)

/-- Define a sort with name `nm`, optional parameters `args` and body `b`. -/
def defineSort (nm : SmtSymbol) (args : Option (Array SmtSymbol)) (b : SortExpr) : TranslateEnvT Unit :=
  trySubmitCommand! (.defineSort nm args b)

/-- Assert a proposition `p`. -/
def assertTerm (p : SmtTerm) : TranslateEnvT Unit := trySubmitCommand! (.assertTerm p)


/-- Perform the following:
     - Define Nat sort in SMT Lib, which is an alias to Int Smt Sort
     - Declare function `IsNat : Nat → Bool` to qualify quantifiers on Nat
     - Assert constraint ∀ x : Nat, isNat x → 0 ≤ x
-/
def defineNatSort : TranslateEnvT Unit := do
  defineSort "Nat" none intSort
  declareFun "isNat" #[natSort] boolSort
  let varId := smtVarId "x"
  let isNatExpr := mkSmtAppN "isNat" #[varId]
  let impExpr := impliesSmt isNatExpr (leqSmt (natLitSmt 0) varId)
  let annots := #[mkPattern #[isNatExpr], mkQid "__nat_constraint"]
  assertTerm (mkForallTerm none #[("x", natSort)] impExpr (some annots))

/-- Define Nat.sub SMT function, i.e.,
     Nat.sub x y := (ite (< x y) 0 (- x y))
-/
def defineNatSub : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let fdef := iteSmt (ltSmt xId yId) (natLitSmt 0) (subSmt xId yId)
  defineFun natSubSymbol #[("x", natSort), ("y", natSort)] natSort fdef

/-- Define Int.ediv SMT function, i.e.,
      Int.ediv x y := (ite (= 0 y) 0 (div x y))
 -/
def defineIntEDiv : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let natZero := natLitSmt 0
  let fdef := iteSmt (eqSmt natZero yId) natZero (divSmt xId yId)
  defineFun edivSymbol #[("x", intSort), ("y", intSort)] intSort fdef

/-- Define Int.emod SMT function, i.e.,
      Int.emod x y := (ite (= 0 y) x (mod x y))
 -/
def defineIntEMod : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let natZero := natLitSmt 0
  let fdef := iteSmt (eqSmt natZero yId) xId (modSmt xId yId)
  defineFun emodSymbol #[("x", intSort), ("y", intSort)] intSort fdef


/-- Define Int.div SMT function, i.e.,
      Int.div x y :=
        (let (t (ite (< x 0) (div (- x) y) (div x y)))
             (ite (= 0 y) 0 (ite (< x 0) (- t) t)))
 -/
def defineIntDiv : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let tId := smtVarId "t"
  let natZero := natLitSmt 0
  let xLtZero := ltSmt xId natZero
  let lbody := iteSmt (eqSmt natZero yId) natZero (iteSmt xLtZero (negSmt tId) tId)
  let fdef := mkLetTerm #[("t", iteSmt xLtZero (divSmt (negSmt xId) yId) (divSmt xId yId))] lbody
  defineFun tdivSymbol #[("x", intSort), ("y", intSort)] intSort fdef

/-- Define Int.mod SMT function, i.e.,
     Int.tmod x y :=
       (let (t (ite (< x 0) (mod (- x) y) (mod x y)))
            (ite (= 0 y) x (ite (< x 0) (- t) t)))
-/
def defineIntMod : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let tId := smtVarId "t"
  let natZero := natLitSmt 0
  let xLtZero := ltSmt xId natZero
  let lbody := iteSmt (eqSmt natZero yId) xId (iteSmt xLtZero (negSmt tId) tId)
  let fdef := mkLetTerm #[("t", iteSmt xLtZero (modSmt (negSmt xId) yId) (modSmt xId yId))] lbody
  defineFun tdivSymbol #[("x", intSort), ("y", intSort)] intSort fdef


/-- Define Int.fdiv SMT function, i.e.,
      Int.fdiv x y :=
        (ite (= 0 y) 0 (ite (< y 0) (div (-x) (- y)) (div x y)))
 -/
def defineIntFDiv : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let natZero := natLitSmt 0
  let yLtZero := ltSmt yId natZero
  let innerIte := iteSmt yLtZero (divSmt (negSmt xId) (negSmt yId)) (divSmt xId yId)
  let fdef := iteSmt (eqSmt natZero yId) natZero innerIte
  defineFun fdivSymbol #[("x", intSort), ("y", intSort)] intSort fdef

/-- Define Int.fmod SMT function, i.e.,
     Int.fmod x y :=
       (let (t (ite (and (< x 0) (< y 0)) (mod (- x) y) (mod x y)))
            (ite (= 0 y) x (ite (and (< x 0) (< y 0)) (- t) t)))
-/
def defineIntFMod : TranslateEnvT Unit := do
  let xId := smtVarId "x"
  let yId := smtVarId "y"
  let tId := smtVarId "t"
  let natZero := natLitSmt 0
  let xLtZero := ltSmt xId natZero
  let yLtZero := ltSmt yId natZero
  let flipCond := andSmt xLtZero yLtZero
  let lbody := iteSmt (eqSmt natZero yId) xId (iteSmt flipCond (negSmt tId) tId)
  let fdef := mkLetTerm #[("t", iteSmt flipCond (modSmt (negSmt xId) yId) (modSmt xId yId))] lbody
  defineFun fdivSymbol #[("x", intSort), ("y", intSort)] intSort fdef


/-- Check satisfiability of current SMT query and return the result.
    An error is triggered when an unexpected check-sat result is obtained.
    Return `Undetermined` when the SMT process is not defined.
-/
def checkSat : TranslateEnvT Result := do
  let env ← get
  let some proc := env.smtEnv.smtProc | return .Undetermined
  submitCommand (.checkSat)
  let satResult ← proc.stdout.getLine -- only one line expected for checkSat result
  match satResult with
   | "sat"     => return .Valid
   | "unsat"   => return .Falsified
   | "unknown" => return .Undetermined
   | _ => throwError "checkSat: Unexpected check-sat result: {satResult}"

/-- Try to retrieve the model when a `sat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elabtorator to parse produced model
    and generate the corresponding Lean representation.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the SMT process is not defined.
-/
def getModel : TranslateEnvT Unit := do
  let env ← get
  let some proc := env.smtEnv.smtProc | return ()
  submitCommand (.getModel)
  logWarning s!"Counterexample:"
  let model ← getOutput proc
  logWarning s!"{model}"


/-- Try to retrieve the proof artifact when a `unsat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elabtorator to parse and reconstruct
    the proof in Lean.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the SMT process is not defined.
-/
def getProof : TranslateEnvT Unit := do
  let env ← get
  let some proc := env.smtEnv.smtProc | return ()
  submitCommand (.getProof)
  logInfo s!"Proof:"
  let proof ← getOutput proc
  logInfo s!"{proof}"


/-- Try to retrieve to evaluate term `t` when a `sat` result is obtained and dump result to stdout.
    TODO: We need to define the Smt-lib syntax and term elabtorator to parse produced value
    and generate the corresponding Lean representation.
    This will also be helpful when writing the test cases to validate the Smt-Lib translation.
    Do nothing if the SMT process is not defined.
-/
def evalTerm (t : SmtTerm) : TranslateEnvT Unit := do
  let env ← get
  let some proc := env.smtEnv.smtProc | return ()
  submitCommand (.evalTerm t)
  logInfo s!"Value for {t}:"
  let value ← getOutput proc
  logInfo s!"{value}"


/-- Try to terminate the SMT process.
    Do nothing if SMT process is not defined.
-/
def exitSmt : TranslateEnvT UInt32 := do
 let env ← get
 let some proc := env.smtEnv.smtProc | return 0
 submitCommand (.exitSmt)
 let (_, p) ← proc.takeStdin
 p.wait


/-- Set the SMT logic to `ALL`. -/
def setLogicAll : TranslateEnvT Unit :=
  trySubmitCommand! (.setLogic "ALL")

/-- Set SMT `produce-proofs` option to `b`. -/
def setProduceProofs (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":produce-proofs" b)

/-- Set SMT `produce-models` option to `b`. -/
def setProduceModels (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":produce-models" b)

/-- Set SMT `smt-mbqi` option to `b`. -/
def setMbqi (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt-mbqi" b)

/-- Set SMT `smt-pull-nested-quantifiers` option to `b`. -/
def setPullNestedQuantifiers (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":smt-pull-nested-quantifiers" b)

/-- Set SMT `print-success` option to `b`. -/
def setPrintSuccess (b : Bool) : TranslateEnvT Unit :=
  trySubmitCommand! (.setOption ":print-success" b)


end Solver.Smt
