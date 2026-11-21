import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize


namespace Blaster

/-! ## Lemmas validating the normalization and simplifications on `Int` -/

protected theorem int_not_lt_of_lt {a b : Int} (h : a < b) : ¬ b < a := by
  apply (Int.lt_asymm h)

protected theorem int_not_lt_right_of_eq {a b : Int} (h : a = b) : ¬ b < a := by
  apply (Int.not_lt_of_ge (Int.le_of_eq h))

protected theorem int_not_lt_left_of_eq {a b : Int} (h : a = b) : ¬ a < b := by
  apply (Int.not_lt_of_ge (Int.le_of_eq (eq_comm.1 h)))

protected theorem int_not_eq_of_lt_left {a b : Int} (h : a < b) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Blaster.int_not_lt_left_of_eq h1; contradiction

protected theorem int_not_eq_of_lt_left_sym {a b : Int} (h : a < b) : ¬ b = a := by
  unfold Not; intro h1; have h2 := Blaster.int_not_lt_right_of_eq h1; contradiction

protected theorem int_not_eq_of_lt_right {a b : Int} (h : b < a) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Blaster.int_not_lt_right_of_eq h1; contradiction

protected theorem int_not_zero_eq_of_lt_zero {a : Int} (h : a < 0) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem int_not_zero_eq_of_zero_lt {a : Int} (h : 0 < a) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem zero_lt_neg_of_lt_zero {a : Int} (h : a < 0) : 0 < -a := by simp; assumption

protected theorem lt_zero_of_zero_lt_neg {a : Int} (h : 0 < -a) : a < 0 := by simp at *; assumption

protected theorem int_not_zero_eq_of_eq_neq {a b : Int} (h1 : a = b) (h2 : ¬ (0 = a)) : ¬ 0 = b := by
  unfold Not; intro h3; rw [← h3] at h1; rw [eq_comm] at h1; contradiction

protected theorem int_zero_lt_of_eq_zero_lt {a b : Int} (h1 : a = b) (h2 : (0 < a)) : 0 < b := by
  rw [h1] at h2; assumption

protected theorem int_lt_zero_of_eq_lt_zero {a b : Int} (h1 : a = b) (h2 : (a < 0)) : b < 0 := by
  rw [h1] at h2; assumption

protected theorem int_not_zero_eq_of_lt_zero_lt {a b : Int} (h1 : a < b) (h2 : 0 < a) : ¬ 0 = b := by
  unfold Not; intros h3; rw [← h3] at h1; omega

protected theorem int_not_zero_eq_of_lt_lt_zero {a b : Int} (h1 : a < b) (h2 : b < 0) : ¬ 0 = a := by
  unfold Not; intros h3; rw [← h3] at h1; omega

protected theorem int_zero_lt_of_nlt_zero_lt {a b : Int} (h1 : ¬ (a < b)) (h2 : 0 < b) : 0 < a := by
  have hba : b ≤ a := Int.not_lt.mp h1
  exact Int.lt_of_lt_of_le h2 hba

protected theorem int_lt_zero_of_nlt_lt_zero {a b : Int} (h1 : ¬ (b < a)) (h2 : b < 0) : a < 0 := by
  have hab : a ≤ b := Int.not_lt.mp h1
  exact Int.lt_of_le_of_lt hab h2

protected theorem sub_min_int_of_eq (N1 N2 a b : Int) (h : N1 + a = N2 + b) :
    N1 - min N1 N2 + a = N2 - min N1 N2 + b := by
    by_cases h : N1 ≤ N2 <;> simp [Int.min_def, h] <;> omega

/-- Return `Blaster.int_not_lt_of_lt` const expression and cache result. -/
def mkInt_not_lt_of_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_of_lt)

/-- Return `Blaster.int_not_lt_right_of_eq` const expression and cache result. -/
def mkInt_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_right_of_eq)

/-- Return `Blaster.int_not_lt_left_of_eq` const expression and cache result. -/
def mkInt_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_left_of_eq)

/-- Return `Blaster.int_not_eq_of_lt_left` const expression and cache result. -/
def mkInt_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_left)

/-- Return `Blaster.int_not_eq_of_lt_left_sym` const expression and cache result. -/
def mkInt_not_eq_of_lt_left_sym : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_left_sym)

/-- Return `Blaster.int_not_eq_of_lt_right` const expression and cache result. -/
def mkInt_not_eq_of_lt_right : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_right)

/-- Return `Blaster.int_not_zero_eq_of_lt_zero` const expression and cache result. -/
def mkInt_not_zero_eq_of_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_lt_zero)

/-- Return `Blaster.int_not_zero_eq_of_zero_lt` const expression and cache result. -/
def mkInt_not_zero_eq_of_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_zero_lt)

/-- Return `Blaster.zero_lt_neg_of_lt_zero` const expression and cache result. -/
def mkInt_zero_lt_neg_of_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.zero_lt_neg_of_lt_zero)

/-- Return `Blaster.lt_zero_of_zero_lt_neg` const expression and cache result. -/
def mkInt_lt_zero_of_zero_lt_neg : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.lt_zero_of_zero_lt_neg)

/-- Return `Blaster.int_not_zero_eq_of_eq_neq` const expression and cache result. -/
def mkInt_not_zero_eq_of_eq_neq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_eq_neq)

/-- Return `Blaster.int_zero_lt_of_eq_zero_lt` const expression and cache result. -/
def mkInt_zero_lt_of_eq_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_zero_lt_of_eq_zero_lt)

/-- Return `Blaster.int_lt_zero_of_eq_lt_zero` const expression and cache result. -/
def mkInt_lt_zero_of_eq_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_lt_zero_of_eq_lt_zero)

/-- Return `Blaster.int_not_zero_eq_of_lt_zero_lt` const expression and cache result. -/
def mkInt_not_zero_eq_of_lt_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_lt_zero_lt)

/-- Return `Blaster.int_not_zero_eq_of_lt_lt_zero` const expression and cache result. -/
def mkInt_not_zero_eq_of_lt_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_lt_lt_zero)

/-- Return `Blaster.int_zero_lt_of_nlt_zero_lt` const expression and cache result. -/
def mkInt_zero_lt_of_nlt_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_zero_lt_of_nlt_zero_lt)

/-- Return `Blaster.int_lt_zero_of_nlt_lt_zero` const expression and cache result. -/
def mkInt_lt_zero_of_nlt_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_lt_zero_of_nlt_lt_zero)

/-- Return `Blaster.sub_min_int_of_eq` const expression and cache result. -/
def mkInt_sub_min_int_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.sub_min_int_of_eq)

/-- Return `Int.lt_trans` const expression and cache result. -/
def mkInt_lt_trans : TranslateEnvT Expr := mkExpr (mkConst ``Int.lt_trans)

end Blaster
