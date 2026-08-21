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

end Blaster
