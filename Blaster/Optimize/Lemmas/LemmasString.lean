import Lean

namespace Blaster

/-! ## Lemmas validating the normalization and simplifications rules on `String` -/

/-! Lemma to validate simplification rule `e < e ==> False`. -/
protected theorem string_lt_self_eq_false (a : String) : (a < a) = False :=
  eq_false (String.lt_irrefl a)

/-! Lemma to validate constant fold `S1 < S2 ==> True (if S1 "<" S2)`. -/
protected theorem string_lt_eq_true (a b : String) (h : decide (a < b) = true) : (a < b) = True :=
  eq_true (of_decide_eq_true h)

/-! Lemma to validate constant fold `S1 < S2 ==> False (if ¬ (S1 "<" S2))`. -/
protected theorem string_lt_eq_false (a b : String) (h : decide (a < b) = false) : (a < b) = False :=
  eq_false (of_decide_eq_false h)

/-! Lemma to validate normalization rule `e1 ≤ e2 ==> ¬ (e2 < e1) (if Type(e1) = String)`.
    `String.le` is defined as `¬ (b < a)`. -/
protected theorem string_le_eq_not_lt (a b : String) : (a ≤ b) = (¬ (b < a)) := rfl

/-! Lemma to validate normalization rule `LE.le ==> λ x y => ¬ (y < x) (if Type(x) = String)`. -/
protected theorem string_le_fun_eq : (LE.le : String → String → Prop) = fun x y => ¬ (y < x) := rfl

end Blaster
