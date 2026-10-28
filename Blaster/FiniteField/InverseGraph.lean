import Blaster.FiniteField.Field

/-!
# The graph of total inversion

The zero branch is explicit: requiring only `b * y = 1` would lose the total
inverse at zero. This relation describes the existing inverse operation without
introducing an alternative carrier or additional algebraic instances.
-/

namespace Blaster.FiniteField.Residue

variable {p : Nat} [PrimeModulus p]

/-- The graph of inversion, including its value at zero. -/
def InverseGraph (b y : Residue p) : Prop :=
  (b = 0 ∧ y = 0) ∨ b * y = 1

/-- The explicit graph describes exactly the total inverse. -/
theorem inverseGraph_iff (b y : Residue p) : InverseGraph b y ↔ y = b⁻¹ := by
  constructor
  · intro h
    rcases h with ⟨hb, hy⟩ | hmul
    · rw [hb, hy, inv_zero]
    · exact eq_inv_of_mul_eq_one
        ((Lean.Grind.CommSemiring.mul_comm y b).trans hmul)
  · intro hy
    subst y
    by_cases hb : b = 0
    · exact Or.inl ⟨hb, by rw [hb, inv_zero]⟩
    · exact Or.inr (mul_inv_cancel hb)

/-- Every denominator, including zero, has an inverse-graph witness. -/
theorem inverseGraph_total (b : Residue p) : ∃ y, InverseGraph b y :=
  ⟨b⁻¹, (inverseGraph_iff b b⁻¹).mpr rfl⟩

/-- The graph has at most one output for each denominator. -/
theorem inverseGraph_functional {b y z : Residue p}
    (hy : InverseGraph b y) (hz : InverseGraph b z) : y = z :=
  ((inverseGraph_iff b y).mp hy).trans ((inverseGraph_iff b z).mp hz).symm

/-- A graph witness permits replacing division by multiplication, even at zero. -/
theorem div_eq_mul_of_inverseGraph (a : Residue p) {b y : Residue p}
    (h : InverseGraph b y) : a / b = a * y := by
  rw [div_eq_mul_inv, (inverseGraph_iff b y).mp h]

end Blaster.FiniteField.Residue
