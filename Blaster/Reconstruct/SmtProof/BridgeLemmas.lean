import Lean
import Blaster.Optimize.Decidable

/-!
# Lemmas of the bridge

The lemmas relating the encodings of Blaster's translation to the goal terms (see `Bridge.lean`): worlds of `Nat` and
`Bool` terms, congruences of conditionals, the macros of the `Nat` and `Int` divisions, etc.
-/

open Lean Meta Elab

namespace Blaster.Reconstruct.SmtProof.Bridge

/-! ## Lemmas -/

theorem ite_congr' {α : Sort u} {c c' : Prop} [h : Decidable c] {x x' y y' : α}
    (hc : c = c') (hx : x = x') (hy : y = y') :
    @ite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc hx hy; by_cases hc : c <;> simp [hc]

theorem ite_congr_dep {α : Sort u} {c c' : Prop} [h : Decidable c] {x x' y y' : α}
    (hc : c = c') (hx : c → x = x') (hy : ¬ c → y = y') :
    @ite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact hx hc
  · rw [if_neg hc, if_neg hc]; exact hy hc

theorem dite_congr_dep {α : Sort u} {c c' : Prop} [h : Decidable c] {x : c → α} {y : ¬ c → α} {x' y' : α}
    (hc : c = c') (hx : ∀ h, x h = x') (hy : ∀ h, y h = y') :
    @dite α c h x y = @ite α c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem natCast_dite_congr {c c' : Prop} [h : Decidable c] {x : c → Nat} {y : ¬ c → Nat} {x' y' : Int}
    (hc : c = c') (hx : ∀ h, ((x h : Nat) : Int) = x') (hy : ∀ h, ((y h : Nat) : Int) = y') :
    ((@dite Nat c h x y : Nat) : Int) = @ite Int c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem boolEq_dite_congr {c c' : Prop} [h : Decidable c] {x : c → Bool} {y : ¬ c → Bool} {x' y' : Prop}
    (hc : c = c') (hx : ∀ h, (x h = true) = x') (hy : ∀ h, (y h = true) = y') :
    ((@dite Bool c h x y) = true) = @ite Prop c' (Classical.propDecidable c') x' y' := by
  subst hc; by_cases hc : c
  · rw [dif_pos hc, if_pos hc]; exact hx hc
  · rw [dif_neg hc, if_neg hc]; exact hy hc

theorem nat_sub_bridge {x y : Nat} {x' y' : Int} (h : y ≤ x) (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x - y : Nat) : Int) = x' - y' := by
  subst hx hy; omega

theorem toNat_bridge {x x' : Int} (h : 0 ≤ x) (hx : x = x') : ((Int.toNat x : Nat) : Int) = x' := by
  subst hx; omega

theorem dite'_ite {α : Sort u} (c : Prop) (x y : α) :
    Blaster.dite' c (fun _ => x) (fun _ => y) = @ite α c (Classical.propDecidable c) x y := by
  have h := congrFun (congrFun (congrFun (congrFun (congrFun Blaster.ite_to_dite'_equiv α) c)
    (Classical.propDecidable c)) x) y
  exact h.symm

theorem natCast_ite {c : Prop} [h : Decidable c] (x y : Nat) :
    ((@ite Nat c h x y : Nat) : Int) = @ite Int c h (x : Int) (y : Int) := by
  split <;> rfl

theorem boolEq_ite {c : Prop} [h : Decidable c] (x y : Bool) :
    ((@ite Bool c h x y) = true) = @ite Prop c h (x = true) (y = true) := by
  split <;> rfl

theorem nat_eq {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x = y) = (x' = y') := by
  subst hx hy; exact propext Int.natCast_inj.symm

theorem nat_le {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x ≤ y) = (x' ≤ y') := by
  subst hx hy; exact propext Int.ofNat_le.symm

theorem nat_lt {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (x < y) = (x' < y') := by
  subst hx hy; exact propext Int.ofNat_lt.symm

theorem bool_eq {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    (x = y) = (x' = y') := by
  subst hx hy; cases x <;> cases y <;> simp

theorem iff_eq {p q p' q' : Prop} (hp : p = p') (hq : q = q') : (p ↔ q) = (p' = q') := by
  subst hp hq; exact propext ⟨propext, fun h => h ▸ Iff.rfl⟩

theorem nat_add {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x + y : Nat) : Int) = x' + y' := by
  subst hx hy; exact Int.natCast_add x y

theorem nat_mul {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x * y : Nat) : Int) = x' * y' := by
  subst hx hy; exact Int.natCast_mul x y

theorem nat_pow {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x ^ y : Nat) : Int) = x' ^ y'.toNat := by
  subst hx hy; simpa only [Int.toNat_natCast] using Int.natCast_pow x y

theorem bool_and {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    ((x && y) = true) = (x' ∧ y') := by
  subst hx hy; simp

theorem bool_or {x y : Bool} {x' y' : Prop} (hx : (x = true) = x') (hy : (y = true) = y') :
    ((x || y) = true) = (x' ∨ y') := by
  subst hx hy; simp

theorem bool_not {x : Bool} {x' : Prop} (hx : (x = true) = x') : ((!x) = true) = ¬ x' := by
  subst hx; cases x <;> simp

theorem bool_decide {a : Bool} {p : Prop} (h : (a = true) = p) : a = @decide p (Classical.propDecidable p) := by
  subst h; cases a <;> simp

theorem nat_toNat {a : Nat} {b : Int} (h : (a : Int) = b) : a = Int.toNat b := by
  subst h; simp

theorem bool_true : (true = true) = True := by simp
theorem bool_false : (false = true) = False := by simp

theorem decide'_eq {p p' : Prop} (h : p = p') : (Blaster.decide' p = true) = p' := by
  subst h; exact propext (Blaster.decide'_true p)

theorem decide_eq {p p' : Prop} [Decidable p] (h : p = p') : (decide p = true) = p' := by
  subst h; simp

theorem beq_eq {α : Type u} [BEq α] [LawfulBEq α] {x y x' y' : α} (hx : x = x') (hy : y = y') :
    ((x == y) = true) = (x' = y') := by
  subst hx hy; simp

theorem nat_beq [BEq Nat] [LawfulBEq Nat] {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    ((x == y) = true) = (x' = y') := by
  subst hx hy; simp [Int.natCast_inj]

theorem true_eq {e : Bool} {p : Prop} (h : (e = true) = p) : (true = e) = p := by
  subst h; cases e <;> simp

theorem false_eq {e : Bool} {p : Prop} (h : (e = true) = p) : (false = e) = ¬ p := by
  subst h; cases e <;> simp

theorem eq_false' {e : Bool} {p : Prop} (h : (e = true) = p) : (e = false) = ¬ p := by
  subst h; cases e <;> simp

theorem nat_ble {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (Nat.ble x y = true) = (x' ≤ y') := by
  subst hx hy; simp [Nat.ble_eq, Int.ofNat_le]

theorem nat_beq' {x y : Nat} {x' y' : Int} (hx : (x : Int) = x') (hy : (y : Int) = y') :
    (Nat.beq x y = true) = (x' = y') := by
  subst hx hy; simp [Nat.beq_eq, Int.natCast_inj]

theorem nat_forall {p : Nat → Prop} {q : Int → Prop} (h : ∀ n : Nat, p n = q (n : Int)) :
    (∀ n, p n) = (∀ x : Int, 0 ≤ x → q x) := by
  apply propext; constructor
  · intro hp x hx
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    rw [← h]; exact hp n
  · intro hq n; rw [h]; exact hq n (Int.natCast_nonneg n)

theorem nat_exists {p : Nat → Prop} {q : Int → Prop} (h : ∀ n : Nat, p n = q (n : Int)) :
    (∃ n, p n) = (∃ x : Int, 0 ≤ x ∧ q x) := by
  apply propext; constructor
  · intro ⟨n, hn⟩; exact ⟨n, Int.natCast_nonneg n, h n ▸ hn⟩
  · intro ⟨x, hx, hq⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    exact ⟨n, (h n).symm ▸ hq⟩

theorem true_imp {p p' : Prop} (h : p = p') : p = (True → p') := by
  subst h; exact propext ⟨fun h _ => h, fun h => h trivial⟩

/-! ### Macros of the `Int` divisions

The equations of the SMT macros translating the divisions and modulos of `Int` (see `Blaster.Smt.defineIntTDiv`, etc.),
with the conditionals of the interpretation (classical instances). -/

theorem ediv_macro (x y : Int) :
    x / y = @ite Int (0 = y) (Classical.propDecidable _) 0 (x / y) := by
  split
  · subst_vars; simp
  · rfl

theorem emod_macro (x y : Int) :
    x % y = @ite Int (0 = y) (Classical.propDecidable _) x (x % y) := by
  split
  · subst_vars; simp
  · rfl

theorem tdiv_macro (x y : Int) :
    Int.tdiv x y = @ite Int (0 = y) (Classical.propDecidable _) 0
      (@ite Int (0 ≤ x) (Classical.propDecidable _) (x / y) (-((-x) / y))) := by
  split
  · subst_vars; simp
  · split
    · rw [Int.tdiv_eq_ediv_of_nonneg (by assumption)]
    · have h := Int.neg_tdiv (-x) y
      rw [Int.neg_neg] at h
      rw [h, Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem tmod_macro (x y : Int) :
    Int.tmod x y = @ite Int (0 = y) (Classical.propDecidable _) x
      (@ite Int (0 ≤ x) (Classical.propDecidable _) (x % y) (-((-x) % y))) := by
  split
  · subst_vars; simp
  · split
    · rw [Int.tmod_eq_emod_of_nonneg (by assumption)]
    · have h := Int.neg_tmod (-x) y
      rw [Int.neg_neg] at h
      rw [h, Int.tmod_eq_emod_of_nonneg (by omega)]

theorem fdiv_macro (x y : Int) :
    Int.fdiv x y = @ite Int (0 = y) (Classical.propDecidable _) 0
      (@ite Int (y < 0) (Classical.propDecidable _) ((-x) / (-y)) (x / y)) := by
  split
  · subst_vars; simp
  · split
    · have h := Int.neg_fdiv_neg (-x) (-y)
      rw [Int.neg_neg, Int.neg_neg] at h
      rw [h, Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    · rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]

theorem fmod_macro (x y : Int) :
    Int.fmod x y = @ite Int (0 = y) (Classical.propDecidable _) x
      (@ite Int (y < 0) (Classical.propDecidable _) (-((-x) % y)) (x % y)) := by
  split
  · subst_vars; simp
  · split
    · have h := Int.neg_fmod_neg (-x) (-y)
      rw [Int.neg_neg, Int.neg_neg] at h
      rw [h, Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_neg]
    · rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]

end Blaster.Reconstruct.SmtProof.Bridge
