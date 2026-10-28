import Blaster.FiniteField.InverseGraph

/-!
# Scoped inverse and division encoding

An inverse witness is existentially scoped to one query. Its graph is a positive
conjunct, outside the negated residual goal, not an assumption under that
negation. The residual is arbitrary: it may contain nested Boolean connectives,
conditionals, and assumptions mentioning the witness. Local parameters remain
parameters of the residual, and all witnesses retain the same field modulus.
-/

namespace Blaster.FiniteField.Residue

variable {p : Nat} [PrimeModulus p]

/-- Totality supplies a witness; functionality makes replacing the inverse safe
in any residual predicate, without a restriction on Boolean polarity. -/
theorem inverseGraph_residual (b : Residue p) (residual : Residue p → Prop) :
    residual b⁻¹ ↔ ∃ y, InverseGraph b y ∧ residual y := by
  have canonical : InverseGraph b b⁻¹ := (inverseGraph_iff b b⁻¹).mpr rfl
  constructor
  · intro h
    obtain ⟨y, hy⟩ := inverseGraph_total b
    exact ⟨y, hy, (inverseGraph_functional hy canonical).symm ▸ h⟩
  · rintro ⟨y, hy, h⟩
    exact inverseGraph_functional hy canonical ▸ h

/-- The query-level graph is conjoined positively with the negated residual. -/
theorem inverseGraph_negated (b : Residue p) (residual : Residue p → Prop) :
    (¬ residual b⁻¹) ↔ ∃ y, InverseGraph b y ∧ ¬ residual y :=
  inverseGraph_residual b (fun y => ¬ residual y)

/-- Assumptions depending on the inverse belong inside the residual implication,
not outside the witness graph or outside the goal's negation. -/
theorem inverseGraph_assumptions (b : Residue p)
    (assumption goal : Residue p → Prop) :
    (¬ (assumption b⁻¹ → goal b⁻¹)) ↔
      ∃ y, InverseGraph b y ∧ ¬ (assumption y → goal y) :=
  inverseGraph_negated b (fun y => assumption y → goal y)

/-- Division is multiplication by the graph witness, including division by zero. -/
theorem divisionGraph_residual (a b : Residue p) (residual : Residue p → Prop) :
    residual (a / b) ↔ ∃ y, InverseGraph b y ∧ residual (a * y) := by
  rw [div_eq_mul_inv]
  exact inverseGraph_residual b (fun y => residual (a * y))

/-- Arbitrary local parameters and witness-dependent hypotheses stay in the same
existential counterexample scope. The parameter type may package many locals. -/
theorem inverseGraph_scoped {α : Sort u} (denominator : α → Residue p)
    (assumption goal : α → Residue p → Prop) :
    (∃ x, ¬ (assumption x (denominator x)⁻¹ → goal x (denominator x)⁻¹)) ↔
      ∃ x y, InverseGraph (denominator x) y ∧ ¬ (assumption x y → goal x y) := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, (inverseGraph_assumptions (denominator x) (assumption x) (goal x)).mp h⟩
  · rintro ⟨x, h⟩
    exact ⟨x, (inverseGraph_assumptions (denominator x) (assumption x) (goal x)).mpr h⟩

/-- Nested inverses introduce dependent witnesses in dependency order; both
positive graphs remain outside any Boolean structure of the residual. -/
theorem inverseGraph_nested (b : Residue p) (residual : Residue p → Prop) :
    residual (b⁻¹)⁻¹ ↔
      ∃ y z, InverseGraph b y ∧ InverseGraph y z ∧ residual z := by
  constructor
  · intro h
    obtain ⟨y, hy, h⟩ := (inverseGraph_residual b (fun y => residual y⁻¹)).mp h
    obtain ⟨z, hz, h⟩ := (inverseGraph_residual y residual).mp h
    exact ⟨y, z, hy, hz, h⟩
  · rintro ⟨y, z, hy, hz, h⟩
    apply (inverseGraph_residual b (fun y => residual y⁻¹)).mpr
    exact ⟨y, hy, (inverseGraph_residual y residual).mpr ⟨z, hz, h⟩⟩

end Blaster.FiniteField.Residue
