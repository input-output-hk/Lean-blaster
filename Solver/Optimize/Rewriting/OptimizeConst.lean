import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta

namespace Solver.Optimize

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - when `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - when `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - when `n := Int.negSucc ∨ n := Nat.pred ∨ n := Nat.succ`:
        - return `optimize (← etaExpand e)`
     - when `n := Int.le`
        - return `mkIntLeOp`
     - when `n := Nat.le`
        - return `mkNatLeOp`
     - when `n := Nat.beq` ∧ (← isOptimizeRecCall):
         - return `mkNatEqOp`
     - when `n := Nat.ble` ∧ (← isOptimizeRecCall):
        - return `optimize (← etaExpand e)`
     - when `¬ isNotFoldable e (recFunCheck := false) ∧ ¬ hasImplicitArgs e`:
         - when `isRecursiveFun n` (i.e., a recursive function passed as argument):
            - return `(← normOpaqueAndRecFun e #[] optimizer)`
         - when `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n`:
            - return `optimizer (← getFunBody e)`
     - otherwise
         - return `mkExpr e`
-/
partial def normConst (e : Expr) (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let Expr.const n _ := e | throwEnvError f!"normConst: name expression expected but got {reprStr e}"
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ =>
    if let some e ← isGlobalConstant n then return e
    if let some e ← isToNormOpaqueFun n then
      trace[Optimize.const] f!"normalizing opaque function {n} => {reprStr e}"
      return e
    if let some r ← isHOF n then
      trace[Optimize.const] f!"normalizing HOF {n} => {reprStr r}"
      return r
    return e

  where
    isGlobalConstant (c : Name) : TranslateEnvT (Option Expr) := do
     let ConstantInfo.opaqueInfo opVal ← getConstInfo c | return none
     trace[Optimize.const] "normalizing global constant {c} => {reprStr opVal.value}"
     optimizer opVal.value

    etaNormOpaqueFun (of : Expr) : TranslateEnvT Expr := do
      let rec visit (l : Expr) : TranslateEnvT Expr := do
        match l with
        | Expr.lam n t b bi =>
             withLocalDecl n bi (← optimizer t) fun x => do
               mkLambdaExpr x (← visit (b.instantiate1 x))
        | r => optimizeApp r.getAppFn' r.getAppArgs
      visit (← etaExpand of)

    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option Expr) := do
      match n with
      | ``Int.negSucc
      | ``Nat.pred
      | ``Nat.succ => etaNormOpaqueFun e
      | ``Int.le => mkIntLeOp
      | ``Nat.le => mkNatLeOp
      | ``Nat.ble =>
           if (← isOptimizeRecCall) then etaNormOpaqueFun e else return none
      | ``Nat.beq =>
           if (← isOptimizeRecCall) then mkNatEqOp else return none
      | _ => return none

    isHOF (f : Name) : TranslateEnvT (Option Expr) := do
     if (← isNotFoldable e #[] (recFunCheck := false)) then return none
     if (← hasImplicitArgs e) then return none
     if (← isRecursiveFun f) then return (← normOpaqueAndRecFun e #[] optimizer)
     -- non recursive function case
     let some fbody ← getFunBody e | return none
     optimizer fbody

initialize
  registerTraceClass `Optimize.const

end Solver.Optimize
