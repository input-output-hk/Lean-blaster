import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Lemmas validating the normalization and simplifications rules on `Nat` -/

/-! Lemma to validate simplification rule `(N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)`. -/
protected theorem nat_add_sub_assoc : ∀ (x y z : Nat), x ≥ z → (x + y) - z = (x - z) + y := by
 intros x y z h1; simp at *
 have h2 := Nat.add_sub_assoc h1 y
 rw [Nat.add_comm x y]
 rw [h2]
 rw [Nat.add_comm (x - z) y]

protected theorem nat_not_lt_right_of_eq {a b : Nat} (h : a = b) : ¬ b < a := by
  apply (Nat.not_lt_of_le (Nat.le_of_eq h))

protected theorem nat_not_lt_left_of_eq {a b : Nat} (h : a = b) : ¬ a < b := by
  apply (Nat.not_lt_of_le (Nat.le_of_eq (eq_comm.1 h)))

protected theorem nat_not_eq_of_lt_left {a b : Nat} (h : a < b) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Blaster.nat_not_lt_left_of_eq h1; contradiction

protected theorem nat_not_eq_of_lt_right {a b : Nat} (h : b < a) : ¬ a = b := by
  unfold Not; intro h1; have h2 := Blaster.nat_not_lt_right_of_eq h1; contradiction

protected theorem nat_not_zero_eq_of_zero_lt {a : Nat} (h : 0 < a) : ¬ 0 = a := by
  unfold Not; intro h1; rw [h1] at h; simp at *

protected theorem nat_zero_lt_of_not_zero_eq {a : Nat} (h : ¬ 0 = a) : 0 < a := by grind

protected theorem sub_min_nat_of_eq (N1 N2 a b : Nat) (h : N1 + a = N2 + b) :
    N1 - Nat.min N1 N2 + a = N2 - Nat.min N1 N2 + b := by
    by_cases h : N1 ≤ N2 <;> simp [Nat.min_def, h] <;> omega

/-! Lemma to validate simplification rule `e < 0 ==> False (if Type(e) = Nat)`. -/
protected theorem nat_lt_zero_eq_false (a : Nat) : (a < 0) = False :=
  propext ⟨fun h => Nat.not_lt_zero a h, fun h => h.elim⟩

/-! Lemma to validate normalization rule `e1 ≤ e2 ==> ¬ (e2 < e1) (if Type(e1) = Nat)`. -/
protected theorem nat_le_eq_not_lt (a b : Nat) : (a ≤ b) = (¬ (b < a)) :=
  propext ⟨fun h hlt => Nat.lt_irrefl b (Nat.lt_of_lt_of_le hlt h),
           Nat.le_of_not_lt⟩

/-! Lemma to validate simplification rule `(N1 + n) - N2 ==> (N1 "-" N2) + n (if N1 ≥ N2)`. -/
protected theorem nat_add_sub_of_ble {c a : Nat} (b : Nat) (h : Nat.ble c a = true) :
    (a + b) - c = (a - c) + b := by
  have h : c ≤ a := by simpa [Nat.ble] using h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.add_sub_assoc h b

/-! Lemma to validate simplification rule
    `(N1 * n) / N2 ==> ((N1 / g) * n) / (N2 / g)` (with `g = gcd N1 N2`). -/
protected theorem nat_mul_div_cancel_gcd {a b g : Nat} (x : Nat)
    (hg : Nat.ble 1 g = true)
    (ha : Nat.beq (a % g) 0 = true)
    (hb : Nat.beq (b % g) 0 = true) :
    (a * x) / b = ((a / g) * x) / (b / g) := by
  have hg' : 0 < g := by simp [Nat.ble_eq] at hg; omega
  have ha' : a % g = 0 := by simp [Nat.beq_eq] at ha; exact ha
  have hb' : b % g = 0 := by simp [Nat.beq_eq] at hb; exact hb
  have hag : a = a / g * g := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha')).symm
  have hbg : b = b / g * g := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb')).symm
  have key : a / g * g * x / (b / g * g) = a / g * x / (b / g) := by
    rw [Nat.mul_assoc, Nat.mul_comm g x, ← Nat.mul_assoc]
    exact Nat.mul_div_mul_right _ _ hg'
  rw [← hag, ← hbg] at key
  exact key

/-! Helper turning `¬ (0 = n)` into `0 < n`. -/
protected theorem nat_pos_of_ne_zero {n : Nat} (h : ¬ (0 = n)) : 0 < n := by omega

/-! Lemma to validate simplification rule `(a * n) % b ==> 0 (if a % b = 0)`. -/
protected theorem nat_mul_mod_of_mod_eq_zero {a b : Nat} (x : Nat)
    (h : Nat.beq (a % b) 0 = true) : (a * x) % b = 0 := by
  have h' : a % b = 0 := by simp [Nat.beq_eq] at h; exact h
  rw [Nat.mul_mod, h', Nat.zero_mul, Nat.zero_mod]

/-! ## Lemmas validating the `optimizeLT` simplification and normalization rules on `Nat` -/

/-! Lemma to validate simplification rule `e < e ==> False`. -/
protected theorem nat_lt_self_eq_false (a : Nat) : (a < a) = False :=
  propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate constant fold `N1 < N2 ==> True (if N1 "<" N2)`. -/
protected theorem nat_lt_eq_true (a b : Nat) (h : decide (a < b) = true) : (a < b) = True :=
  eq_true (of_decide_eq_true h)

/-! Lemma to validate constant fold `N1 < N2 ==> False (if ¬ (N1 "<" N2))`. -/
protected theorem nat_lt_eq_false (a b : Nat) (h : decide (a < b) = false) : (a < b) = False :=
  eq_false (of_decide_eq_false h)

/-! Lemma to validate simplification rule `e < 1 ==> 0 = e`. -/
protected theorem nat_lt_one_eq_zero_eq (a : Nat) : (a < 1) = (0 = a) :=
  propext (by omega)

/-! Lemma to validate simplification rule `a + b < a ==> False`. -/
protected theorem nat_add_lt_self_eq_false (a b : Nat) : (a + b < a) = False :=
  propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate simplification rule `b + a < a ==> False`. -/
protected theorem nat_add_lt_self_right_eq_false (a b : Nat) : (b + a < a) = False :=
  propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate simplification rule `e < N + e ==> True (if N > 0)`. -/
protected theorem nat_lt_add_left_eq_true (a n : Nat) (h : Nat.ble 1 n = true) :
    (a < n + a) = True := by
  have h1 : 1 ≤ n := Nat.le_of_ble_eq_true h
  exact propext ⟨fun _ => trivial, fun _ => by omega⟩

/-! Lemma to validate simplification rule `N1 + a < N2 ==> False (if N2 ≤ N1)`. -/
protected theorem nat_add_const_lt_eq_false (a n1 n2 : Nat) (h : Nat.ble n2 n1 = true) :
    (n1 + a < n2) = False := by
  have : n2 ≤ n1 := Nat.le_of_ble_eq_true h
  exact propext ⟨fun h => by omega, False.elim⟩

/-! Lemma to validate simplification rule `N1 + a < N2 ==> a < N2 "-" N1`. -/
protected theorem nat_add_const_lt_eq_lt_sub (a n1 n2 : Nat) :
    (n1 + a < n2) = (a < n2 - n1) := propext (by omega)

/-! Lemma to validate simplification rule `N1 < N2 + a ==> True (if N1 < N2)`. -/
protected theorem nat_const_lt_add_eq_true (a n1 n2 : Nat) (h : Nat.blt n1 n2 = true) :
    (n1 < n2 + a) = True := by
  have h1 : n1 < n2 := cast Nat.blt_eq h
  exact propext ⟨fun _ => trivial, fun _ => by omega⟩

/-! Lemma to validate simplification rule `N1 < N2 + a ==> N1 "-" N2 < a (if N1 ≥ N2)`. -/
protected theorem nat_const_lt_add_eq_sub_lt (a n1 n2 : Nat) (h : Nat.ble n2 n1 = true) :
    (n1 < n2 + a) = (n1 - n2 < a) := by
  have : n2 ≤ n1 := Nat.le_of_ble_eq_true h
  exact propext (by omega)

/-! Lemma to validate simplification rule
    `N1 + a < N2 + b ==> N1 "-" min(N1, N2) + a < N2 "-" min(N1, N2) + b`.
    `m1` and `m2` are the (already reduced) constants `N1 "-" min(N1, N2)` and
    `N2 "-" min(N1, N2)`, so the reconstructed goal matches the optimizer output literally. -/
protected theorem nat_add_both_lt (a b n1 n2 m1 m2 : Nat)
    (h1 : n1 - min n1 n2 = m1) (h2 : n2 - min n1 n2 = m2) :
    (n1 + a < n2 + b) = (m1 + a < m2 + b) := by
  subst h1 h2; exact propext (by omega)

/-! Lemma to validate normalization rule `a < 1 + b ==> ¬ (b < a)`. -/
protected theorem nat_lt_one_add_eq_not_lt (a b : Nat) : (a < 1 + b) = (¬ (b < a)) :=
  propext (by omega)

def mkNat_lt_asymm : TranslateEnvT Expr := mkExpr (mkConst ``Nat.lt_asymm)

def mkNat_not_lt_right_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_not_lt_right_of_eq)

def mkNat_not_lt_left_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_not_lt_left_of_eq)

def mkNat_not_eq_of_lt_left : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_not_eq_of_lt_left)

def mkNat_not_eq_of_lt_right : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_not_eq_of_lt_right)

def mkNat_not_zero_eq_of_zero_lt : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_not_zero_eq_of_zero_lt)

def mkNat_zero_lt_of_not_zero_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.nat_zero_lt_of_not_zero_eq)

def mkNat_sub_min_nat_of_eq : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.sub_min_nat_of_eq)

end Blaster
