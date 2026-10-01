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
  simp only [decide'_false, not_false_eq_true]

protected theorem decide'_true_simp : Blaster.decide' True = true := by
  simp only [Blaster.decide'_true]

protected theorem decide'_true_eq (p : Bool) : Blaster.decide' (true = p) = p := by
  apply Blaster.bool_eq_of_iff ;
  rw [Blaster.decide'_true, Bool.true_eq]

protected theorem decide'_false_eq (p : Bool) : Blaster.decide' (false = p) = ! p := by
  apply Blaster.bool_eq_of_iff;
  rw [Blaster.decide'_true, Bool.false_eq];
  exact Bool.coe_false_iff_true.mpr rfl

/-! ## Lemma validating the nominal `Decidable.decide` to `Blaster.decide'` bridge:
    - `decide p ==> decide' p`  (drops the concrete `Decidable` instance)
-/

protected theorem decide_eq_decide' (p : Prop) [inst : Decidable p] :
    decide p = Blaster.decide' p := by
  cases h : Blaster.decide' p with
  | true => have hp := (Blaster.decide'_true p).mp h; simp [hp]
  | false => have hnp := (Blaster.decide'_false p).mp h; simp [hnp]

/-! ## Lemmas validating the `Eq`-context `decide'` normalization rules:
    - `true = decide' p        ==> p`
    - `false = decide' p       ==> ¬ p`
    - `decide' p = decide' q   ==> p = q`
    - `decide' p = b           ==> p = (true = b)`
    - `b = decide' p           ==> p = (true = b)`
-/

protected theorem true_eq_decide' (p : Prop) : (true = Blaster.decide' p) = p := by
  apply propext
  constructor
  · intro h; exact (Blaster.decide'_true p).mp h.symm
  · intro h; exact ((Blaster.decide'_true p).mpr h).symm

protected theorem false_eq_decide' (p : Prop) : (false = Blaster.decide' p) = ¬ p := by
  apply propext
  constructor
  · intro h; exact (Blaster.decide'_false p).mp h.symm
  · intro h; exact ((Blaster.decide'_false p).mpr h).symm

protected theorem decide'_eq_decide' (p q : Prop) :
    (Blaster.decide' p = Blaster.decide' q) = (p = q) := by
  apply propext
  constructor
  · intro h
    apply propext
    rw [← Blaster.decide'_true p, ← Blaster.decide'_true q, h]
  · intro h; rw [h]

protected theorem decide'_eq_bool (p : Prop) (b : Bool) :
    (Blaster.decide' p = b) = (p = (true = b)) := by
  apply propext
  constructor
  · intro h
    apply propext
    constructor
    · intro hp; rw [← h]; exact ((Blaster.decide'_true p).mpr hp).symm
    · intro hb; exact (Blaster.decide'_true p).mp (by rw [h]; exact hb.symm)
  · intro h
    rw [h]
    cases b with
    | true => exact (Blaster.decide'_true (true = true)).mpr rfl
    | false => exact (Blaster.decide'_false (true = false)).mpr (by decide)

protected theorem bool_eq_decide' (p : Prop) (b : Bool) :
    (b = Blaster.decide' p) = (p = (true = b)) := by
  have h : (b = Blaster.decide' p) = (Blaster.decide' p = b) := propext eq_comm
  rw [h, Blaster.decide'_eq_bool]

/-! ## Lemma validating the Bool-not-over-`decide'` bridge:
    - `!(decide' p) ==> decide' (¬ p)`
-/

protected theorem not_decide' (p : Prop) : (!(Blaster.decide' p)) = Blaster.decide' (¬ p) := by
  apply Blaster.bool_eq_of_iff
  cases h : Blaster.decide' p with
  | true =>
    simp only [Bool.not_true]
    constructor
    · intro hc; simp at hc
    · intro hnp
      exact absurd ((Blaster.decide'_true p).mp h) ((Blaster.decide'_true (¬ p)).mp hnp)
  | false =>
    simp only [Bool.not_false]
    exact iff_of_true trivial ((Blaster.decide'_true (¬ p)).mpr ((Blaster.decide'_false p).mp h))

end Blaster
