import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Const-expression accessors for the `Prop` simplification rules -/

def mkBlasterAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``And.left)

def mkBlasterAndRight : TranslateEnvT Expr := mkExpr (mkConst ``And.right)

  /-! ## Lemmas validating the `And simplfication rules:
        - `a ∧ ¬ a ==> False`
        - `true = a ∧ false = a ==> False`
  -/
theorem and_not_self_is_false (a : Prop) : (a ∧ ¬ a) = False := by
   simp

theorem true_and_false_is_false (a : Bool) : (true = a ∧ false = a) = False := by
  simp

end Blaster
