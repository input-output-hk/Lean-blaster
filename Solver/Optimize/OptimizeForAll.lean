import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - ∀ (n : t), False | e → False ==> False
      - False → e ==> True
      - True → e ==> e
      - e1 → e2 ===> True (if p1 =ₚₜᵣ p2 ∧ Type(e1) = Prop)
      - ¬ e → e ==> e (requires classical)
      - e → ¬ e ==> ¬ e (requires classical)
      - true = c → false = c ==> false = c
      - false = c → true = c ==> true = c
  TODO: consider additional simplification rules
-/
def optimizeForall (n : Expr) (t : Expr) (b : Expr) : TranslateEnvT Expr := do
  match b with
  | Expr.const ``True _ | Expr.const ``False _ => pure b
  | _ =>
    match t with
     | Expr.const ``False _ => mkPropTrue
     | Expr.const `True _ => pure b
     | _ =>
       if (← exprEq t b) && (← inferType t).isProp
       then mkPropTrue
       else if (← (isNotExprOf t b) <||> (isNotExprOf b t) <||> (isNegBoolEqOf t b))
            then pure b
            else mkForallExpr n b

/-- `mkImpliesExpr a b` perform the following:
      - construct expression `a → b`
      - apply normalization/simplification rules on `a → b`
      - cache result
-/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default a fun x =>
    optimizeForall x a b

end Solver.Optimize
