import Blaster.Optimize.Decidable

namespace Blaster

/-! ## Lemmas validating `Decidable.decide` simplifications rules on `Eq` -/


/-! Lemmas validating simplification rules `decide e1 = e2 | e2 = decide e1 ===> e1 = (true = e2)`. -/

protected theorem decide_eq_bool : ∀ (p : Prop) (b : Bool), [Decidable p] → decide p = b ↔ p = (true = b) := by
  intros p b h
  apply Iff.intro <;> intro h2
  . rw [← h2]; simp
  . cases b <;> simp [*]

protected theorem decide_eq_not_bool : ∀ (p : Prop) (b : Bool), [Decidable p] → decide p = !b ↔ p = (false = b) := by
  intros p b h
  apply Iff.intro <;> intro h2
  . have h3 : decide (false = b) = !b := by simp
    rw [← h3] at h2
    have h4 : p ↔ (false = b) := by apply (decide_eq_decide.1 h2)
    rw [h4]
  . simp [*]


/-! Lemmas validating simplification rule `c = (a == b)` ===> (true = c) = (a = b) (if isCompatibleBeqType Type(a))`. -/

protected theorem bool_eq_bool_beq_iff_eq_eq : ∀ (a b c : Bool), c = (a == b) ↔ (true = c) = (a = b) := by
  simp only [BEq.beq]
  intros a b c
  have h1 := Blaster.decide_eq_bool (a = b) c
  rw [eq_comm] at h1
  rw [h1]
  rw [eq_comm]

protected theorem bool_eq_nat_beq_iff_eq_eq : ∀ (x y : Nat) (c : Bool), c = (x == y) ↔ (true = c) = (x = y) := by
  intros x y c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : true = (x == y) ↔ (x == y) = true := eq_comm
    rw [h2]
    apply Nat.beq_eq_true_eq
  . cases c <;> simp at * <;> assumption


protected theorem bool_eq_int_beq_iff_eq_eq : ∀ (x y : Int) (c : Bool), c = (x == y) ↔ (true = c) = (x = y) := by
  intros x y c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : (x == y) = true ↔ x = y := by apply beq_iff_eq
    rw [← h2]
    have h3 : true = (x == y) ↔ (x == y) = true := eq_comm
    rw [h3]
  . cases c <;> simp at * <;> assumption


protected theorem bool_eq_string_beq_iff_eq_eq : ∀ (s t : String) (c : Bool), c = (s == t) ↔ (true = c) = (s = t) := by
  intros s t c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : (s == t) = true ↔ s = t := by apply beq_iff_eq
    rw [← h2]
    have h3 : true = (s == t) ↔ (s == t) = true := eq_comm
    rw [h3]
  . cases c <;> simp at * <;> assumption


/-! Lemmas validating simplification rule `false = (a == b)` ===> ¬ (a = b) (if isCompatibleBeqType Type(a))`. -/

protected theorem false_eq_bool_beq_iff_eq_eq : ∀ (a b : Bool), false = (a == b) ↔ ¬ (a = b) := by decide

protected theorem false_eq_nat_beq_iff_eq_eq : ∀ (x y : Nat), false = (x == y) ↔ ¬ (x = y) := by simp

protected theorem false_eq_int_beq_iff_eq_eq : ∀ (x y : Int), false = (x == y) ↔ ¬ (x = y) := by simp

protected theorem false_eq_string_beq_iff_eq_eq : ∀ (s t : String), false = (s == t) ↔ ¬ (s = t) := by simp


/-! Lemmas validating simplification rules
      - `B1 = e1 ∧ B2 = e2 ==> true = (NOP(B1, e1) && NOP(B2, e2)) (if B1 ∨ B2)`
      - `B1 = e1 ∧ B2 = e2 ==> false = (e1 || e2) (if ¬ B1 ∧ ¬ B2)`
-/

protected theorem and_iff_eq_prop_1 : ∀ (a b : Bool), (a && b) ↔ (true = a ∧ true = b) := by decide

protected theorem and_iff_eq_prop_2 : ∀ (a b : Bool), (a && !b) ↔ (true = a ∧ false = b) := by decide

protected theorem and_iff_eq_prop_3 : ∀ (a b : Bool), (!a && b) ↔ (false = a ∧ true = b) := by decide

protected theorem and_iff_eq_prop_4 : ∀ (a b : Bool), !(a || b) ↔ (false = a ∧ false = b) := by decide

/-! Lemmas validating simplification rules:
     - `B1 = e1 ∨ B2 = e2 ==> true = (NOP(B1, e1) || NOP(B2, e2)) (if B1 ∨ B2)`
     - `B1 = e1 ∨ B2 = e2 ==> false = (e1 && e2) (if ¬ B1 ∧ ¬ B2)`
-/

protected theorem or_iff_eq_prop_1 : ∀ (a b : Bool), (a || b) ↔ (true = a ∨ true = b) := by decide

protected theorem or_iff_eq_prop_2 : ∀ (a b : Bool), (a || !b) ↔ (true = a ∨ false = b) := by decide

protected theorem or_iff_eq_prop_3 : ∀ (a b : Bool), (!a || b) ↔ (false = a ∨ true = b) := by decide

protected theorem or_iff_eq_prop_4 : ∀ (a b : Bool), !(a && b) ↔ (false = a ∨ false = b) := by decide


/-! ## Lemmas validating the `decide'` regrouping on Boolean `&&`/`||:`
      - `(decide' p && decide' q) ==> decide' (p ∧ q)`
      - `(decide' p && b) | (b && decide' p) ==> decide' (p ∧ true = b)`
      - `(decide' p || decide' q) ==> decide' (p ∨ q)`
      - `(decide' p || b) | (b || decide' p) ==> decide' (p ∨ true = b)`
-/

protected theorem bool_eq_of_iff (b1 b2 : Bool) (h : b1 = true ↔ b2 = true) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all

protected theorem decide'_and_decide' (p q : Prop) :
    (Blaster.decide' p && Blaster.decide' q) = Blaster.decide' (p ∧ q) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.and_eq_true, Blaster.decide'_true]

protected theorem decide'_and_bool (p : Prop) (b : Bool) :
    (Blaster.decide' p && b) = Blaster.decide' (p ∧ (true = b)) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.and_eq_true, Blaster.decide'_true]
  constructor
  · rintro ⟨hp, hb⟩; exact ⟨hp, hb.symm⟩
  · rintro ⟨hp, hb⟩; exact ⟨hp, hb.symm⟩

protected theorem bool_and_decide' (p : Prop) (b : Bool) :
    (b && Blaster.decide' p) = Blaster.decide' (p ∧ (true = b)) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.and_eq_true, Blaster.decide'_true]
  constructor
  · rintro ⟨hb, hp⟩; exact ⟨hp, hb.symm⟩
  · rintro ⟨hp, hb⟩; exact ⟨hb.symm, hp⟩

protected theorem decide'_or_decide' (p q : Prop) :
    (Blaster.decide' p || Blaster.decide' q) = Blaster.decide' (p ∨ q) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.or_eq_true, Blaster.decide'_true]

protected theorem decide'_or_bool (p : Prop) (b : Bool) :
    (Blaster.decide' p || b) = Blaster.decide' (p ∨ (true = b)) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.or_eq_true, Blaster.decide'_true]
  constructor
  · rintro (hp | hb); exact Or.inl hp; exact Or.inr hb.symm
  · rintro (hp | hb); exact Or.inl hp; exact Or.inr hb.symm

protected theorem bool_or_decide' (p : Prop) (b : Bool) :
    (b || Blaster.decide' p) = Blaster.decide' (p ∨ (true = b)) := by
  apply Blaster.bool_eq_of_iff; simp only [Bool.or_eq_true, Blaster.decide'_true]
  constructor
  · rintro (hb | hp); exact Or.inr hb.symm; exact Or.inl hp
  · rintro (hp | hb); exact Or.inr hp; exact Or.inl hb.symm

  /-! ## Lemmas validating the `decide'` simplification rules:
      - `decide' False ==> false`
      - `decide' True ==> true`
      - `decide' (true = p) ==> p`
      - `decide' (false = p) ==> ! p`
  -/
protected theorem decide'_false_simp : Blaster.decide' False = false := by
  simp [Blaster.decide'_false]

protected theorem decide'_true_simp : Blaster.decide' True = true := by
  simp [Blaster.decide'_true]

protected theorem decide'_true_eq (p : Bool) : Blaster.decide' (true = p) = p := by
  cases p <;> simp [Blaster.decide'_true, Blaster.decide'_false]

protected theorem decide'_false_eq (p : Bool) : Blaster.decide' (false = p) = ! p := by
  cases p <;> simp [Blaster.decide'_true, Blaster.decide'_false]

end Blaster
