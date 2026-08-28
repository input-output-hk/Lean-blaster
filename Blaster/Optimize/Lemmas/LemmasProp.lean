import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Const-expression accessors for the `Prop` simplification rules -/

def mkBlasterAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``And.left)

def mkBlasterAndRight : TranslateEnvT Expr := mkExpr (mkConst ``And.right)

/-! ## Lemmas validating the `And` simplification rules:
    - `a ∧ ¬ a ==> False`
    - `true = a ∧ false = a ==> False`
-/
protected theorem and_not_self_is_false (a : Prop) :
  (a ∧ ¬ a) = False := by
  simp only [and_not_self]

protected theorem true_and_false_is_false (a : Bool) :
  (true = a ∧ false = a) = False := by
  apply propext
  rw [Bool.true_eq, Bool.false_eq, Bool.eq_true_and_eq_false_self]

/-! ## Lemmas validating the `Or` simplification rules:
    - `a ∨ ¬ a ==> True`
    - `true = a ∨ false = a ==> True`
-/
protected theorem or_not_self_is_true (a : Prop) :
  (a ∨ ¬ a) = True := by
  simp only [Classical.em]

protected theorem true_or_false_is_true (a : Bool) :
  (true = a ∨ false = a) = True := by
  apply propext;
  rw [Bool.true_eq, Bool.false_eq, Bool.eq_true_or_eq_false_self]

/-! ## Lemmas validating the `Not` simplification rules:
  - `¬ (¬ e) ==> e`
  - `¬ (false = e) ==> true = e`
  - `¬ (true = e) ==> false = e`
-/
protected theorem double_not_classical (p : Prop) : (¬ (¬ p)) = p := by
  apply propext;
  exact Classical.not_not


protected theorem not_false_is_true (e : Bool) :
  (¬ (false = e)) = (true = e) := by
  apply propext;
  rw [Bool.false_eq, Bool.not_eq_false, Bool.true_eq]

protected theorem not_true_is_false (e : Bool):
  (¬ (true = e)) = (false = e) := by
  apply propext;
  rw [Bool.true_eq, Bool.not_eq_true, Bool.false_eq]

/-! ## Lemmas validating the `Iff` expansion and the And/Or implicative reductions:
    - `p ↔ q ==> (p → q) ∧ (q → p)`
    - `e1 ∧ (e1 → e2) ==> e1 ∧ e2`
    - `e1 ∧ (e2 → e1) ==> e1`
    - `(e1 → e2) ∧ (¬ e1 → e2) ==> e2`
    - `e1 ∨ (e1 → e2) ==> True`
    - `e1 ∨ (e2 → e1) ==> (e2 → e1)`
-/
protected theorem iff_eq_implies_and_implies (p q : Prop) :
  (p ↔ q) = ((p → q) ∧ (q → p)) :=
  propext iff_iff_implies_and_implies

protected theorem and_imp_self_eq_and (p q : Prop) :
  (p ∧ (p → q)) = (p ∧ q) :=
  propext ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

protected theorem and_imp_right_eq_left (p q : Prop) :
  (p ∧ (q → p)) = p :=
  propext ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

protected theorem and_imp_not_imp_eq (p q : Prop) :
  ((p → q) ∧ (¬ p → q)) = q :=
  propext (imp_and_neg_imp_iff p)

protected theorem or_imp_self_eq_true (p q : Prop) :
  (p ∨ (p → q)) = True :=
  propext ⟨fun _ => trivial,
           fun _ => (Classical.em p).elim Or.inl (fun hnp => Or.inr (fun hp => absurd hp hnp))⟩

protected theorem or_imp_right_eq_imp (p q : Prop) :
  (p ∨ (q → p)) = (q → p) :=
  propext ⟨fun h => h.elim (fun hp _ => hp) id, fun h => Or.inr h⟩


/-! ## Lemmas validating the `Eq` simplifications over Prop:
    - `False = e ==> ¬ e`
    - `True = e ==> e`
    - `e = ¬ e ==> False`
    - `¬ e1 = ¬ e2 ==> e1 = e2 (Classical)`
-/

protected theorem false_prop_is_neg (e : Prop) : (False = e) = ¬ e := by
  apply propext
  rw [eq_iff_iff]
  exact iff_false_left fun a => a

protected theorem true_prop_is_idem (e : Prop) : (True = e) = e := by
  apply propext
  rw [eq_iff_iff]
  exact iff_true_left trivial

protected theorem eq_neg_is_false (e : Prop) : (e = ¬ e) = False := by
  simp only [eq_iff_iff, iff_not_self]

protected theorem neg_eq_neg_is_eq (a b : Prop) :
  ((¬ a) = ¬ b) = (a = b) := by
  classical
  apply propext
  rw [eq_iff_iff, eq_iff_iff]
  exact Decidable.not_iff_not

end Blaster
