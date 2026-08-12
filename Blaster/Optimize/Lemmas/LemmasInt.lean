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

protected theorem int_not_eq_of_lt_right {a b : Int} (h : b < a) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Blaster.int_not_lt_right_of_eq h1; contradiction

protected theorem int_not_zero_eq_of_lt_zero {a : Int} (h : a < 0) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem int_not_zero_eq_of_zero_lt {a : Int} (h : 0 < a) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem zero_lt_neg_of_lt_zero {a : Int} (h : a < 0) : 0 < -a := by simp; assumption

protected theorem lt_zero_of_zero_lt_neg {a : Int} (h : 0 < -a) : a < 0 := by simp at *; assumption

protected theorem sub_min_int_of_eq (N1 N2 a b : Int) (h : N1 + a = N2 + b) :
    N1 - min N1 N2 + a = N2 - min N1 N2 + b := by
    by_cases h : N1 ≤ N2 <;> simp [Int.min_def, h] <;> omega

protected theorem int_ediv_gcd_norm (N1 N2 x : Int) :
    N1 * x / N2 = N1 / ↑(N1.gcd N2) * x / (N2 / ↑(N1.gcd N2)) := by
  rcases Nat.eq_zero_or_pos (N1.gcd N2) with h0 | hpos
  · rw [Int.gcd_eq_zero_iff] at h0; obtain ⟨rfl, rfl⟩ := h0; simp
  · have hg : 0 < (↑(N1.gcd N2) : Int) := by exact_mod_cast hpos
    have h1 : (↑(N1.gcd N2) : Int) ∣ N1 := Int.gcd_dvd_left N1 N2
    have h2 : (↑(N1.gcd N2) : Int) ∣ N2 := Int.gcd_dvd_right N1 N2
    generalize (↑(N1.gcd N2) : Int) = g at hg h1 h2 ⊢
    have hg0 : g ≠ 0 := by omega
    obtain ⟨a1, rfl⟩ := h1; obtain ⟨a2, rfl⟩ := h2
    rw [Int.mul_ediv_cancel_left _ hg0, Int.mul_ediv_cancel_left _ hg0,
        Int.mul_assoc, Int.mul_ediv_mul_of_pos _ _ hg]

protected theorem int_tdiv_gcd_norm (N1 N2 x : Int) :
    (N1 * x).tdiv N2 = (N1.tdiv ↑(N1.gcd N2) * x).tdiv (N2.tdiv ↑(N1.gcd N2)) := by
  rcases Nat.eq_zero_or_pos (N1.gcd N2) with h0 | hpos
  · rw [Int.gcd_eq_zero_iff] at h0; obtain ⟨rfl, rfl⟩ := h0; simp
  · have hg : 0 < (↑(N1.gcd N2) : Int) := by exact_mod_cast hpos
    have h1 : (↑(N1.gcd N2) : Int) ∣ N1 := Int.gcd_dvd_left N1 N2
    have h2 : (↑(N1.gcd N2) : Int) ∣ N2 := Int.gcd_dvd_right N1 N2
    generalize (↑(N1.gcd N2) : Int) = g at hg h1 h2 ⊢
    have hg0 : g ≠ 0 := by omega
    obtain ⟨a1, rfl⟩ := h1; obtain ⟨a2, rfl⟩ := h2
    rw [Int.mul_tdiv_cancel_left _ hg0, Int.mul_tdiv_cancel_left _ hg0,
        Int.mul_assoc, Int.mul_tdiv_mul_of_pos _ _ hg]

protected theorem int_fdiv_gcd_norm (N1 N2 x : Int) :
    (N1 * x).fdiv N2 = (N1.fdiv ↑(N1.gcd N2) * x).fdiv (N2.fdiv ↑(N1.gcd N2)) := by
  rcases Nat.eq_zero_or_pos (N1.gcd N2) with h0 | hpos
  · rw [Int.gcd_eq_zero_iff] at h0; obtain ⟨rfl, rfl⟩ := h0; simp
  · have hg : 0 < (↑(N1.gcd N2) : Int) := by exact_mod_cast hpos
    have h1 : (↑(N1.gcd N2) : Int) ∣ N1 := Int.gcd_dvd_left N1 N2
    have h2 : (↑(N1.gcd N2) : Int) ∣ N2 := Int.gcd_dvd_right N1 N2
    generalize (↑(N1.gcd N2) : Int) = g at hg h1 h2 ⊢
    have hg0 : g ≠ 0 := by omega
    obtain ⟨a1, rfl⟩ := h1; obtain ⟨a2, rfl⟩ := h2
    rw [Int.mul_fdiv_cancel_left _ hg0, Int.mul_fdiv_cancel_left _ hg0,
        Int.mul_assoc, Int.mul_fdiv_mul_of_pos _ _ hg]

protected theorem int_emod_mul_zero (N1 N2 x : Int) (h : N1 % N2 = 0) : N1 * x % N2 = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  exact Int.emod_eq_zero_of_dvd ⟨k * x, by rw [hk, Int.mul_assoc]⟩

protected theorem int_tmod_mul_zero (N1 N2 x : Int) (h : N1 % N2 = 0) : (N1 * x).tmod N2 = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  exact Int.tmod_eq_zero_of_dvd ⟨k * x, by rw [hk, Int.mul_assoc]⟩

protected theorem int_fmod_mul_zero (N1 N2 x : Int) (h : N1 % N2 = 0) : (N1 * x).fmod N2 = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  exact Int.fmod_eq_zero_of_dvd ⟨k * x, by rw [hk, Int.mul_assoc]⟩

/-- Return `Blaster.int_not_lt_of_lt` const expression and cache result. -/
def mkInt_not_lt_of_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_of_lt)

/-- Return `Blaster.int_not_lt_right_of_eq` const expression and cache result. -/
def mkInt_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_right_of_eq)

/-- Return `Blaster.int_not_lt_left_of_eq` const expression and cache result. -/
def mkInt_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_left_of_eq)

/-- Return `Blaster.int_not_eq_of_lt_left` const expression and cache result. -/
def mkInt_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_left)

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

/-- Return `Blaster.sub_min_int_of_eq` const expression and cache result. -/
def mkInt_sub_min_int_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.sub_min_int_of_eq)


end Blaster
