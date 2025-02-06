import Lean
import Solver.Optimize.Rewriting.OptimizePropNot

open Lean Meta Elab
namespace Solver.Optimize

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - False → e ==> True (if Type(e) = Prop)
      - True → e ==> e (if Type(e) = Prop)
      - e → False ==> ¬ e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ Type(e1) = Prop)
      - ¬ e → e ==> e (requires classical)
      - e → ¬ e ==> ¬ e (requires classical)
      - true = c → false = c ==> false = c
      - false = c → true = c ==> true = c
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ fVarInExpr n.fvarId! e)
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  TODO: consider additional simplification rules
  TODO: check if we can have a simplification rule for:
    -- (∀ (a b : Type), P a b) → (∀ (b a : Type), P a b) ===> True
-/
def optimizeForall (n : Expr) (t : Expr) (b : Expr) : TranslateEnvT Expr := do
  if let Expr.const ``True _ := b then return b
  if let some r ← isCstImplies? t b then return r
  if let some r ← isNotDef? t b then return r
  if (← (exprEq t b) <&&> (isProp t)) then return (← mkPropTrue)
  if (← (isNotExprOf t b) <||> (isNotExprOf b t) <||> (isNegBoolEqOf t b) <||> (isNegBoolEqOf b t)) then return b
  if (← (isSortOrInhabited t) <&&> (isProp b) <&&> (pure !(fVarInExpr n.fvarId! b))) then return b
  mkForallExpr n b

  where
    /-- Given `a → b`, apply the simplification rules:
          - When `a := True ∧ Type(b) = Prop`:
             - return `some b`
          - When `a := False ∧ Type(b) = Prop`:
              - return `True`
          - Otherwise
              - return `none`
    -/
    isCstImplies? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
      if !(← isProp b) then return none
      match a with
      | Expr.const ``True _ => return b
      | Expr.const ``False _ => return (← mkPropTrue)
      | _ => return none

    /-- Given `a → b`, apply the following normalization rule:
         - When `b := False ∧ Type(a) = Prop`
            - return `some ¬ a`
         - Otherwise
            - return `none`
    -/
    isNotDef? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
      if !(← isProp a) then return none
      match b with
      | Expr.const ``False _ => optimizeNot (← mkPropNotOp) #[a]
      | _ => return none

/-- `mkImpliesExpr a b` perform the following:
      - construct expression `a → b`
      - apply normalization/simplification rules on `a → b`
      - cache result
-/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default a fun x =>
    optimizeForall x a b

end Solver.Optimize
