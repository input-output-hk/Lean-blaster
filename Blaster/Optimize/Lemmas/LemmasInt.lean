import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize


namespace Blaster

/-! ## Lemmas validating the normalization and simplifications on `Int` -/

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

/-! Lemma to validate normalization rule `e1 ≤ e2 ==> ¬ (e2 < e1) (if Type(e1) = Int)`. -/
protected theorem int_le_eq_not_lt (a b : Int) : (a ≤ b) = (¬ (b < a)) :=
  propext ⟨fun h hlt => absurd (Int.lt_of_lt_of_le hlt h) (Int.lt_irrefl b), Int.not_lt.mp⟩

/-! Lemma to validate simplification rule `N1 + -(N2 + n) ==> (N1 "-" N2) + -n`. -/
protected theorem int_add_neg_add (a b c : Int) : a + -(b + c) = (a - b) + -c := by omega

/-! Helpers turning a strict sign hypothesis into `n ≠ 0`. -/
protected theorem int_ne_zero_of_zero_lt {n : Int} (h : 0 < n) : n ≠ 0 := by omega
protected theorem int_ne_zero_of_lt_zero {n : Int} (h : n < 0) : n ≠ 0 := by omega
protected theorem int_ne_zero_of_not_zero_eq {n : Int} (h : ¬ (0 = n)) : n ≠ 0 := by omega

/-! ## Lemmas validating the `optimizeLT` simplification and normalization rules on `Int` -/

/-! Lemma to validate simplification rule `e < e ==> False`. -/
protected theorem int_lt_self_eq_false (a : Int) : (a < a) = False :=
  propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate constant fold `N1 < N2 ==> True (if N1 "<" N2)`. -/
protected theorem int_lt_eq_true (a b : Int) (h : decide (a < b) = true) : (a < b) = True :=
  eq_true (of_decide_eq_true h)

/-! Lemma to validate constant fold `N1 < N2 ==> False (if ¬ (N1 "<" N2))`. -/
protected theorem int_lt_eq_false (a b : Int) (h : decide (a < b) = false) : (a < b) = False :=
  eq_false (of_decide_eq_false h)

/-! Lemma to validate normalization rule `0 < -e ==> e < 0`. -/
protected theorem int_zero_lt_neg_eq_lt_zero (a : Int) : (0 < -a) = (a < 0) := propext (by omega)

/-! Lemma to validate simplification rule `N + e < e ==> False (if N > 0)`. -/
protected theorem int_add_pos_lt_self_eq_false (a n : Int) (h : decide (0 < n) = true) :
    (n + a < a) = False := by
  have : 0 < n := of_decide_eq_true h
  exact propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate simplification rule `N + e < e ==> True (if N < 0)`. -/
protected theorem int_add_neg_lt_self_eq_true (a n : Int) (h : decide (n < 0) = true) :
    (n + a < a) = True := by
  have : n < 0 := of_decide_eq_true h
  exact propext ⟨fun _ => trivial, fun _ => by omega⟩

/-! Lemma to validate simplification rule `e < N + e ==> True (if N > 0)`. -/
protected theorem int_lt_add_pos_eq_true (a n : Int) (h : decide (0 < n) = true) :
    (a < n + a) = True := by
  have : 0 < n := of_decide_eq_true h
  exact propext ⟨fun _ => trivial, fun _ => by omega⟩

/-! Lemma to validate simplification rule `e < N + e ==> False (if N < 0)`. -/
protected theorem int_lt_add_neg_eq_false (a n : Int) (h : decide (n < 0) = true) :
    (a < n + a) = False := by
  have : n < 0 := of_decide_eq_true h
  exact propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate simplification rule `N1 + a < N2 ==> a < N2 "-" N1`. -/
protected theorem int_add_const_lt_eq_lt_sub (a n1 n2 : Int) :
    (n1 + a < n2) = (a < n2 - n1) := propext (by omega)

/-! Lemma to validate simplification rule `N1 < N2 + a ==> N1 "-" N2 < a`. -/
protected theorem int_const_lt_add_eq_sub_lt (a n1 n2 : Int) :
    (n1 < n2 + a) = (n1 - n2 < a) := propext (by omega)

/-! Lemma to validate simplification rule
    `N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`.
    `m1` and `m2` are the (already reduced) constants `N1 "-" min(N1, N2)` and
    `N2 "-" min(N1, N2)`, so the reconstructed goal matches the optimizer output literally. -/
protected theorem int_add_both_lt (a b n1 n2 m1 m2 : Int)
    (h1 : n1 - min n1 n2 = m1) (h2 : n2 - min n1 n2 = m2) :
    (n1 + a < n2 + b) = (m1 + a < m2 + b) := by
  subst h1 h2; exact propext (by omega)

/-! Lemma to validate normalization rule `a < 1 + b ==> ¬ (b < a)`. -/
protected theorem int_lt_one_add_eq_not_lt (a b : Int) : (a < 1 + b) = (¬ (b < a)) :=
  propext (by omega)

def mkInt_lt_asymm : TranslateEnvT Expr := mkExpr (mkConst ``Int.lt_asymm)

def mkInt_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_right_of_eq)

def mkInt_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_lt_left_of_eq)

def mkInt_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_left)

def mkInt_not_eq_of_lt_right : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_eq_of_lt_right)

def mkInt_not_zero_eq_of_lt_zero : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_lt_zero)

def mkInt_not_zero_eq_of_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.int_not_zero_eq_of_zero_lt)

def mkInt_sub_min_int_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.sub_min_int_of_eq)


end Blaster
