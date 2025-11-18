import Lean
import Solver.Optimize.Env

open Lean Meta Solver.Optimize


namespace Solver

/-! ## Lemmas validating the normalization and simplifications on `Int` -/

protected theorem int_not_lt_of_lt {a b : Int} (h : a < b) : ¬ b < a := by
  apply (Int.lt_asymm h)

protected theorem int_not_lt_right_of_eq {a b : Int} (h : a = b) : ¬ b < a := by
  apply (Int.not_lt_of_ge (Int.le_of_eq h))

protected theorem int_not_lt_left_of_eq {a b : Int} (h : a = b) : ¬ a < b := by
  apply (Int.not_lt_of_ge (Int.le_of_eq (eq_comm.1 h)))

protected theorem int_not_eq_of_lt_left {a b : Int} (h : a < b) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Solver.int_not_lt_left_of_eq h1; contradiction

protected theorem int_not_eq_of_lt_right {a b : Int} (h : b < a) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Solver.int_not_lt_right_of_eq h1; contradiction

protected theorem int_not_zero_eq_of_lt_zero {a : Int} (h : a < 0) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem int_not_zero_eq_of_zero_lt {a : Int} (h : 0 < a) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem zero_lt_neg_of_lt_zero {a : Int} (h : a < 0) : 0 < -a := by simp; assumption

protected theorem lt_zero_of_zero_lt_neg {a : Int} (h : 0 < -a) : a < 0 := by simp at *; assumption

/-- Return `Solver.int_not_lt_of_lt` const expression and cache result. -/
def mkInt_not_lt_of_lt : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_lt_of_lt)

/-- Return `Solver.int_not_lt_right_of_eq` const expression and cache result. -/
def mkInt_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_lt_right_of_eq)

/-- Return `Solver.int_not_lt_left_of_eq` const expression and cache result. -/
def mkInt_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_lt_left_of_eq)

/-- Return `Solver.int_not_eq_of_lt_left` const expression and cache result. -/
def mkInt_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_eq_of_lt_left)

/-- Return `Solver.int_not_eq_of_lt_right` const expression and cache result. -/
def mkInt_not_eq_of_lt_right : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_eq_of_lt_right)

/-- Return `Solver.int_not_zero_eq_of_lt_zero` const expression and cache result. -/
def mkInt_not_zero_eq_of_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_zero_eq_of_lt_zero)

/-- Return `Solver.int_not_zero_eq_of_zero_lt` const expression and cache result. -/
def mkInt_not_zero_eq_of_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Solver.int_not_zero_eq_of_zero_lt)

/-- Return `Solver.zero_lt_neg_of_lt_zero` const expression and cache result. -/
def mkInt_zero_lt_neg_of_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Solver.zero_lt_neg_of_lt_zero)

/-- Return `Solver.lt_zero_of_zero_lt_neg` const expression and cache result. -/
def mkInt_lt_zero_of_zero_lt_neg : TranslateEnvT Expr := mkExpr (mkConst ``Solver.lt_zero_of_zero_lt_neg)


end Solver
