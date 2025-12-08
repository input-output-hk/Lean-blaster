import Lean
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Blaster

/-! ## Lemmas validating the normalization and simplifications rules on `Prop` -/

protected theorem Blaster.and_left {a b : Prop} (h : a ∧ b) : a := by apply (And.left h)
protected theorem Blaster.and_right {a b : Prop} (h : a ∧ b) : b := by apply (And.right h)

/-- Return `Blaster.and_left` const expression and cache result. -/
def mkBlasterAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.and_left)

/-- Return `Blaster.and_right` const expression and cache result. -/
def mkBlasterAndRight : TranslateEnvT Expr := mkExpr (mkConst ``Blaster.and_right)

end Blaster
