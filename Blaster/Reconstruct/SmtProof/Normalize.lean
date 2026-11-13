import Lean

/-!
# Checked preparation of residual propositions

Predicate wrappers are unfolded definitionally. Equalities of functions become
pointwise equalities, with an explicit `funext` proof transporting the resulting
SMT proof back to the original goal. The caller kernel-checks that composition.
-/

open Lean Meta

namespace Blaster.Reconstruct.SmtProof

private def logicalHead (e : Expr) : Bool :=
  e.isForall || e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 ||
  e.isAppOfArity ``Not 1 || e.isAppOfArity ``Eq 3 || e.isAppOfArity ``Iff 2 ||
  e.isAppOfArity ``Exists 2 || e.isConstOf ``True || e.isConstOf ``False

/-- Expose predicate applications as logical structure or applied predicate variables.
    Keep existing connectives and arithmetic atoms in the translator's vocabulary. -/
def unfoldPredicateHeads (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if logicalHead t || !(← isProp t) then return .done t
    let nf ← withDefault (whnf t)
    if (logicalHead nf || nf.getAppFn.isFVar) && nf != t && (← withDefault (isDefEq t nf)) then
      return .visit nf
    return .done t)

/-- Extensionality as a propositional equivalence, including dependent functions. -/
theorem pointwise_iff {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} :
    f = g ↔ ∀ x, f x = g x := ⟨fun h x => congrFun h x, funext⟩

/-- Rewrite function equalities also in hypotheses and nested logical structure.
    Only the extensionality lemma is supplied to the simplifier. -/
private def pointwiseGoal? (goal : Expr) : MetaM (Option (Expr × Expr)) := do
  let hasFunctionEquality := (goal.find? fun e =>
    e.isAppOfArity ``Eq 3 && (e.getArg! 0).isForall).isSome
  if !hasFunctionEquality then return none
  let thms ← ({} : SimpTheorems).addConst ``pointwise_iff
  let ctx ← Simp.mkContext
    (config := { beta := false, iota := false, zeta := false, zetaDelta := false, proj := false })
    (simpTheorems := #[thms])
  let (result, _) ← Meta.simp goal ctx
  let some equality := result.proof? | return none
  withLocalDeclD `h result.expr fun h => do
    let value ← mkEqMPR equality h
    return some (result.expr, ← mkLambdaFVars #[h] value)

/-- Prepare a residual for first-order SMT replay, with a function restoring a
    proof of the original proposition. Definitional changes need no extra axiom. -/
def normalizeResidual (goal : Expr) : MetaM (Expr × (Expr → Expr)) := do
  let goal ← unfoldPredicateHeads goal
  if let some (pointwise, back) ← pointwiseGoal? goal then
    return (← unfoldPredicateHeads pointwise, mkApp back)
  return (goal, id)

end Blaster.Reconstruct.SmtProof
