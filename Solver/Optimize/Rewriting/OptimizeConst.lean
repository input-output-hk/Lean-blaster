import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta

namespace Solver.Optimize

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - when `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - when `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - when `n` corresponds to a function passed as argument (i.e., isArgApp set to `true`):
         - when `n := Int.negSucc ∨ n := Nat.pred ∨ n := Nat.succ`
            - return `optimizer (← etaExpand e)`
         - when `n := Nat.beq`
            - return `mkNatEqOp`
         - when `isRecursiveFun n` (i.e., a recursive function passed as argument):
            - return `(← normOpaqueAndRecFun e #[] optimizer)`
         - when `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n ∧ n ∉ opaqueFuns ∧ ¬ isInductiveType n l ∧ ¬ isInstance n ∧ ¬ isCtorName n`:
            - return `optimizer (← getFunBody e)`
     - otherwise
         - return `mkExpr e`
    An error is triggered when:
      - `n` is a match function used as an effective parameter (i.e., isArgApp set to `true`); or
      - `n` is a function passed as argument such that `n` has implicit parameters (i.e., polymorphic parameters to be instantiated).
-/
def normConst (e : Expr) (isArgApp : Bool) (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let Expr.const n l := e | throwError "normConst: name expression expected but got {reprStr e}"
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ =>
    if let some e ← isGlobalConstant n then return e
    if let some r ← isHOF n l then return r
    mkExpr e

  where
    isGlobalConstant (c : Name) : TranslateEnvT (Option Expr) := do
     let ConstantInfo.opaqueInfo opVal ← getConstInfo c | return none
     optimizer opVal.value

    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option Expr) := do
      match n with
      | ``Int.negSucc
      | ``Nat.pred
      | ``Nat.succ => optimizer (← etaExpand e)
      | ``Nat.beq => mkNatEqOp
      | _ => return none

    isHOF (f : Name) (us : List Level) : TranslateEnvT (Option Expr) := do
     if (← isInstance f) then return none
     if !isArgApp then return none -- no unfolding on applied function expression
     if (← isInductiveType f us) then return none -- also handles class constraint case
     if (← isMatchExpr f) then throwError "normConst: unexpected match function passed as argument {f}"
     if (← hasImplicitArgs e) then
       throwError "normConst: unexpected implicit arguments for function {f}"
     if let some r ← isToNormOpaqueFun f then return r
     if (← isRecursiveFun f) then return (← normOpaqueAndRecFun e #[] optimizer)
     if (opaqueFuns.contains f) then return none
     -- non recursive function case
     let some fbody ← getFunBody e | return none
     optimizer fbody

end Solver.Optimize
