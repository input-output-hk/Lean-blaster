import Lean

namespace Blaster

/-! ## Lemmas validating the hypothesis-context `optimizeBoolAnd` reductions. -/

protected theorem true_and_with_hyp (a b : Bool) (h : true = a) :
  (a && b) = b := by
  exact Bool.and_eq_right_iff_imp.mpr fun a_1 => id (Eq.symm h)

protected theorem and_true_with_hyp (a b : Bool) (h : true = b) :
  (a && b) = a := by
  rw [← h]
  simp only [Bool.and_true]

protected theorem false_and_with_hyp (a b : Bool) (h : false = a) :
  (a && b) = false := by
  rw [← h]
  simp only [Bool.false_and]

protected theorem and_false_with_hyp (a b : Bool) (h : false = b) :
  (a && b) = false := by
  rw [← h]
  simp only [Bool.and_false]

/-! ## Lemmas validating the hypothesis-context `optimizeBoolOr` reductions. -/

protected theorem true_or_with_hyp (a b : Bool) (h : true = a) :
  (a || b) = true := by
  rw [← h]
  exact rfl

protected theorem or_true_with_hyp (a b : Bool) (h : true = b) :
  (a || b) = true := by
  rw [← h]
  exact Bool.or_true a

protected theorem false_or_with_hyp (a b : Bool) (h : false = a) :
  (a || b) = b := by
  rw [← h]
  exact rfl

protected theorem or_false_with_hyp (a b : Bool) (h : false = b) :
  (a || b) = a := by
  rw [← h]
  exact Bool.or_false a

/-! ## Lemmas validating the Bool `Eq` reductions rules:
  - `e = not e ==> False`
  - `true = not e ==> false = e`
  - `false = not e ==> true = e`
  - `not e1 = not e2 ==> e1 = e2`
-/

protected theorem eq_not_is_false (e : Bool) : (e = not e) = False := by
  rw[Bool.eq_not_self]

protected theorem true_eq_not_is_false_eq (e : Bool) :
  (true = not e) = (false = e) := by
  rw [Bool.true_eq, Bool.false_eq]
  exact Bool.not_eq_true' e

protected theorem false_eq_not_is_true_eq (e : Bool) :
  (false = not e) = (true = e) := by
  rw [Bool.true_eq, Bool.false_eq]
  exact Bool.not_eq_false' e

protected theorem not_eq_not_is_eq (a b : Bool) :
  (not a = not b) = (a = b) := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_not]

/-! ## Lemmas validating the Bool↔Prop bridge on `And` (propExprToBoolExpr?):
    with `NOP(B, e) = e if B else !e`
    - `(true = e1) ∧ (true = e2)   ==> true  = (e1 && e2)`
    - `(true = e1) ∧ (false = e2)  ==> true  = (e1 && !e2)`
    - `(false = e1) ∧ (true = e2)  ==> true  = (!e1 && e2)`
    - `(false = e1) ∧ (false = e2) ==> false = (e1 || e2)`
-/

protected theorem bridge_and_tt (e1 e2 : Bool) :
  ((true = e1) ∧ (true = e2)) = (true = (e1 && e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_and_tf (e1 e2 : Bool) :
  ((true = e1) ∧ (false = e2)) = (true = (e1 && !e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_and_ft (e1 e2 : Bool) :
  ((false = e1) ∧ (true = e2)) = (true = (!e1 && e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_and_ff (e1 e2 : Bool) :
  ((false = e1) ∧ (false = e2)) = (false = (e1 || e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

/-! ## Lemmas validating the Bool↔Prop bridge on `Or` (propExprToBoolExpr?):
    with `NOP(B, e) = e if B else !e`
    - `(true = e1) ∨ (true = e2)   ==> true  = (e1 || e2)`
    - `(true = e1) ∨ (false = e2)  ==> true  = (e1 || !e2)`
    - `(false = e1) ∨ (true = e2)  ==> true  = (!e1 || e2)`
    - `(false = e1) ∨ (false = e2) ==> false = (e1 && e2)`
-/

protected theorem bridge_or_tt (e1 e2 : Bool) :
  ((true = e1) ∨ (true = e2)) = (true = (e1 || e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_or_tf (e1 e2 : Bool) :
  ((true = e1) ∨ (false = e2)) = (true = (e1 || !e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_or_ft (e1 e2 : Bool) :
  ((false = e1) ∨ (true = e2)) = (true = (!e1 || e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

protected theorem bridge_or_ff (e1 e2 : Bool) :
  ((false = e1) ∨ (false = e2)) = (false = (e1 && e2)) := by
  cases e1 <;> cases e2 <;> exact propext (by decide)

end Blaster
