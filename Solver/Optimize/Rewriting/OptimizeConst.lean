import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta

namespace Solver.Optimize

/-- Given `n` a const name and `l` a list level, apply the following normalization rule:
     - when `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - when `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - when `n` corresponds to a function passed as argument (i.e., isFunApp set to `false`):
         - return `(← normOpaqueAndRecFun (mkConst n l) #[] optimizer)` if `isRecursiveFun n` (i.e., a recursive function passed as argument)
         - return `optimizer (← getFunBody (mkConst n l))`
              if `getFunBody (mkConst n l).isSome ∧ ¬ isRecursiveFun n ∧ n ∉ opaqueFuns ∧ ¬ isInductiveType n l ∧ ¬ isInstance n`.
     - otherwise
         - return `mkConst n l`
    Trigger an error when:
      - `n` is a match function with no arguments that is used as an effective parameter (i.e., isFunApp set to `false`); or
      - `n` is a function passed as argument such that `n` has implicit parameters (i.e., polymorphic parameters to be instantiated).
-/
def normConst (n : Name) (l : List Level) (isFunApp : Bool) (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ =>
    if let some e ← isGlobalConstant n then return e
    if let some r ← isHOF n l then return r
    return (mkConst n l)

  where
    isGlobalConstant (c : Name) : TranslateEnvT (Option Expr) := do
     let ConstantInfo.opaqueInfo opVal ← getConstInfo c | return none
     optimizer opVal.value

    hasImplicitArgs (f : Name) (us : List Level) : MetaM Bool := do
      let fInfo ← getFunInfo (mkConst f us)
      for i in [:fInfo.paramInfo.size] do
        if !fInfo.paramInfo[i]!.isExplicit then return true
      return false

    isHOF (f : Name) (us : List Level) : TranslateEnvT (Option Expr) := do
     if (← isInstance f) then return none
     if isFunApp then return none -- no unfolding on applied function expression
     if (← isInductiveType f us) then return none -- also handles class constraint case
     if (← isMatchExpr f) then throwError "normConst: unexpected match function passed as argument"
     if (← hasImplicitArgs f us) then throwError "normConst: unexpected implicit arguments for function {f}"
     if (← isRecursiveFun f) then return (← normOpaqueAndRecFun (mkConst n us) #[] optimizer)
     if (opaqueFuns.contains f) then return none
     -- non recursive function case
     let some fbody ← getFunBody (mkConst n us) | return none
     optimizer fbody

end Solver.Optimize
