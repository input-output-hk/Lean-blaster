import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - ∀ (n : t), False ==> False
      - False → e ==> True
      - True → e ==> e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)
      - ¬ e → e ==> e (requires classical)
      - e → ¬ e ==> ¬ e (requires classical)
      - true = c → false = c ==> false = c
      - false = c → true = c ==> true = c
  TODO: consider additional simplification rules
  TODO: check if we can have a simplification rule for:
    -- (∀ (a b : Type), P a b) → (∀ (b a : Type), P a b) ===> True
-/
def optimizeForall (n : Expr) (t : Expr) (b : Expr) : TranslateEnvT Expr := do
  match b with
  | Expr.const ``True _ => pure b
  | _ =>
    if (← isFalseForall t b)
    then pure b
    else
      match t with
      | Expr.const ``False _ => mkPropTrue
      | Expr.const `True _ => pure b
      | _ =>
        if (← (exprEq t b) <&&> (isProp t))
        then mkPropTrue
        else if (← (isNotExprOf t b) <||> (isNotExprOf b t) <||> (isNegBoolEqOf t b))
             then pure b
             else mkForallExpr n b

  where
    /-- Return `true` only `b := False` ∧ !isProp t. -/
    isFalseForall (t : Expr) (b : Expr) : MetaM Bool := do
     match b with
     | Expr.const ``False _ => pure !(← isProp t)
     | _ => pure false


/-- `mkImpliesExpr a b` perform the following:
      - construct expression `a → b`
      - apply normalization/simplification rules on `a → b`
      - cache result
-/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default a fun x =>
    optimizeForall x a b

end Solver.Optimize
