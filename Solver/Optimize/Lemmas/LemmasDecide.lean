

namespace Solver.Optimize.Lemmas

/-! ## Lemmas validating `Decidable.decide` simplifications rules on `Eq` -/


/-! Lemmas validating simplification rules `decide e1 = e2 | e2 = decide e1 ===> e1 = (true = e2)`. -/

theorem decide_eq_bool : ∀ (p : Prop) (b : Bool), [Decidable p] → decide p = b ↔ p = (true = b) := by
  intros p b h
  apply Iff.intro <;> intro h2
  . rw [← h2]; simp
  . cases b <;> simp [*]

theorem decide_eq_not_bool : ∀ (p : Prop) (b : Bool), [Decidable p] → decide p = !b ↔ p = (false = b) := by
  intros p b h
  apply Iff.intro <;> intro h2
  . have h3 : decide (false = b) = !b := by simp
    rw [← h3] at h2
    have h4 : p ↔ (false = b) := by apply (decide_eq_decide.1 h2)
    rw [h4]
  . simp [*]


/-! Lemmas validating simplification rule `c = (a == b)` ===> (true = c) = (a = b) (if isCompatibleBeqType Type(a))`. -/

theorem bool_eq_bool_beq_iff_eq_eq : ∀ (a b c : Bool), c = (a == b) ↔ (true = c) = (a = b) := by
  simp only [BEq.beq]
  intros a b c
  have h1 := decide_eq_bool (a = b) c
  rw [eq_comm] at h1
  rw [h1]
  rw [eq_comm]

theorem bool_eq_nat_beq_iff_eq_eq : ∀ (x y : Nat) (c : Bool), c = (x == y) ↔ (true = c) = (x = y) := by
  intros x y c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : true = (x == y) ↔ (x == y) = true := eq_comm
    rw [h2]
    apply Nat.beq_eq_true_eq
  . cases c <;> simp at * <;> assumption


theorem bool_eq_int_beq_iff_eq_eq : ∀ (x y : Int) (c : Bool), c = (x == y) ↔ (true = c) = (x = y) := by
  intros x y c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : (x == y) = true ↔ x = y := by apply beq_iff_eq
    rw [← h2]
    have h3 : true = (x == y) ↔ (x == y) = true := eq_comm
    rw [h3]
  . cases c <;> simp at * <;> assumption


theorem bool_eq_string_beq_iff_eq_eq : ∀ (s t : String) (c : Bool), c = (s == t) ↔ (true = c) = (s = t) := by
  intros s t c
  apply Iff.intro <;> intro h1
  . rw [h1]
    have h2 : (s == t) = true ↔ s = t := by apply beq_iff_eq
    rw [← h2]
    have h3 : true = (s == t) ↔ (s == t) = true := eq_comm
    rw [h3]
  . cases c <;> simp at * <;> assumption


/-! Lemmas validating simplification rule `false = (a == b)` ===> ¬ (a = b) (if isCompatibleBeqType Type(a))`. -/

theorem false_eq_bool_beq_iff_eq_eq : ∀ (a b : Bool), false = (a == b) ↔ ¬ (a = b) := by decide

theorem false_eq_nat_beq_iff_eq_eq : ∀ (x y : Nat), false = (x == y) ↔ ¬ (x = y) := by simp

theorem false_eq_int_beq_iff_eq_eq : ∀ (x y : Int), false = (x == y) ↔ ¬ (x = y) := by simp

theorem false_eq_string_beq_iff_eq_eq : ∀ (s t : String), false = (s == t) ↔ ¬ (s = t) := by simp


/-! Lemmas validating simplification rules
      - `B1 = e1 ∧ B2 = e2 ==> true = (NOP(B1, e1) && NOP(B2, e2)) (if B1 ∨ B2)`
      - `B1 = e1 ∧ B2 = e2 ==> false = (e1 || e2) (if ¬ B1 ∧ ¬ B2)`
-/

theorem and_iff_eq_prop_1 : ∀ (a b : Bool), (a && b) ↔ (true = a ∧ true = b) := by decide

theorem and_iff_eq_prop_2 : ∀ (a b : Bool), (a && !b) ↔ (true = a ∧ false = b) := by decide

theorem and_iff_eq_prop_3 : ∀ (a b : Bool), (!a && b) ↔ (false = a ∧ true = b) := by decide

theorem and_iff_eq_prop_4 : ∀ (a b : Bool), !(a || b) ↔ (false = a ∧ false = b) := by decide

/-! Lemmas validating simplification rules:
     - `B1 = e1 ∨ B2 = e2 ==> true = (NOP(B1, e1) || NOP(B2, e2)) (if B1 ∨ B2)`
     - `B1 = e1 ∨ B2 = e2 ==> false = (e1 && e2) (if ¬ B1 ∧ ¬ B2)`
-/

theorem or_iff_eq_prop_1 : ∀ (a b : Bool), (a || b) ↔ (true = a ∨ true = b) := by decide

theorem or_iff_eq_prop_2 : ∀ (a b : Bool), (a || !b) ↔ (true = a ∨ false = b) := by decide

theorem or_iff_eq_prop_3 : ∀ (a b : Bool), (!a || b) ↔ (false = a ∨ true = b) := by decide

theorem or_iff_eq_prop_4 : ∀ (a b : Bool), !(a && b) ↔ (false = a ∨ false = b) := by decide


end Solver.Optimize.Lemmas
