

namespace Solver.Optimize.Lemmas

/-! ## Lemmas validating the normalization and simplifications rules on ``Nat.sub -/

/-! Lemma to validate the following simplification rules
      - `N1 - (N2 + n) ===> (N1 "-" N2) - n`.
      - (n - N1) - N2 ==> n - (N1 "+" N2).
-/
theorem sub_add_eq_sub_sub : ∀ (x y z : Nat), x - (y + z) = (x - y) - z := by
  intros x y z
  apply eq_comm.1
  apply Nat.sub_sub


/-! Lemma to validate simplification rule `(N1 - n) - N2 ==> (N1 "-" N2) - n`. -/
theorem sub_assoc : ∀ (x y z : Nat), (x - y) - z = (x - z) - y := by
  intros x y z
  have h2 := Nat.sub_sub x y z
  have h3 := Nat.sub_sub x z y
  have h4 := Nat.add_comm y z
  rw [h2]
  rw [h3]
  rw [h4]

/-! Lemma to validate simplification rule `(N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)`. -/
theorem add_sub_assoc : ∀ (x y z : Nat), x ≥ z → (x + y) - z = (x - z) + y := by
 intros x y z h1; simp at *
 have h2 := Nat.add_sub_assoc h1 y
 rw [Nat.add_comm x y]
 rw [h2]
 rw [Nat.add_comm (x - z) y]

end Solver.Optimize.Lemmas
