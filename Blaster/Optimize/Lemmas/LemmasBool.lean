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

end Blaster
