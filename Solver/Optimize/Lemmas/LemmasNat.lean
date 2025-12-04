import Lean
import Solver.Optimize.Env

open Lean Meta Solver.Optimize

namespace Solver

/-! ## Lemmas validating the normalization and simplifications rules on `Nat` -/

/-! Lemma to validate the following simplification rules
      - `N1 - (N2 + n) ===> (N1 "-" N2) - n`.
      - (n - N1) - N2 ==> n - (N1 "+" N2).
-/
protected theorem nat_sub_add_eq_sub_sub : ∀ (x y z : Nat), x - (y + z) = (x - y) - z := by
  intros x y z
  apply eq_comm.1
  apply Nat.sub_sub


/-! Lemma to validate simplification rule `(N1 - n) - N2 ==> (N1 "-" N2) - n`. -/
protected theorem nat_sub_assoc : ∀ (x y z : Nat), (x - y) - z = (x - z) - y := by
  intros x y z
  have h2 := Nat.sub_sub x y z
  have h3 := Nat.sub_sub x z y
  have h4 := Nat.add_comm y z
  rw [h2]
  rw [h3]
  rw [h4]

/-! Lemma to validate simplification rule `(N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)`. -/
protected theorem nat_add_sub_assoc : ∀ (x y z : Nat), x ≥ z → (x + y) - z = (x - z) + y := by
 intros x y z h1; simp at *
 have h2 := Nat.add_sub_assoc h1 y
 rw [Nat.add_comm x y]
 rw [h2]
 rw [Nat.add_comm (x - z) y]

protected theorem nat_not_lt_of_lt {a b : Nat} (h : a < b) : ¬ b < a := by
  apply (Nat.lt_asymm h)

protected theorem nat_not_lt_right_of_eq {a b : Nat} (h : a = b) : ¬ b < a := by
  apply (Nat.not_lt_of_le (Nat.le_of_eq h))

protected theorem nat_not_lt_left_of_eq {a b : Nat} (h : a = b) : ¬ a < b := by
  apply (Nat.not_lt_of_le (Nat.le_of_eq (eq_comm.1 h)))

protected theorem nat_not_eq_of_lt_left {a b : Nat} (h : a < b) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Solver.nat_not_lt_left_of_eq h1; contradiction

protected theorem nat_not_eq_of_lt_right {a b : Nat} (h : b < a) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Solver.nat_not_lt_right_of_eq h1; contradiction

protected theorem nat_not_zero_eq_of_zero_lt {a : Nat} (h : 0 < a) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem nat_zero_lt_of_not_zero_eq {a : Nat} (h : ¬ 0 = a) : 0 < a := by grind

protected theorem sub_min_nat_of_eq (N1 N2 a b : Nat) (h : N1 + a = N2 + b) :
    N1 - Nat.min N1 N2 + a = N2 - Nat.min N1 N2 + b := by
    by_cases h : N1 ≤ N2 <;> simp [Nat.min_def, h] <;> omega

/-- Return `Solver.nat_not_lt_of_lt` const expression and cache result. -/
def mkNat_not_lt_of_lt : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_lt_of_lt)

/-- Return `Solver.nat_not_lt_right_of_eq` const expression and cache result. -/
def mkNat_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_lt_right_of_eq)

/-- Return `Solver.nat_not_lt_left_of_eq` const expression and cache result. -/
def mkNat_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_lt_left_of_eq)

/-- Return `Solver.nat_not_eq_of_lt_left` const expression and cache result. -/
def mkNat_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_eq_of_lt_left)

/-- Return `Solver.nat_not_eq_of_lt_right` const expression and cache result.-/
def mkNat_not_eq_of_lt_right : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_eq_of_lt_right)

/-- Return `Solver.nat_not_zero_eq_of_zero_lt` const expression and cache result. -/
def mkNat_not_zero_eq_of_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_not_zero_eq_of_zero_lt)

/-- Return `Solver.nat_zero_lt_of_not_zero_eq` const expression and cache result. -/
def mkNat_zero_lt_of_not_zero_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.nat_zero_lt_of_not_zero_eq)

/-- Return `Solver.sub_min_nat_of_eq` const expression and cache result. -/
def mkNat_sub_min_nat_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.sub_min_nat_of_eq)

end Solver
