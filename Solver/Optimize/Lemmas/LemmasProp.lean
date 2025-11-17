import Lean
import Solver.Optimize.Env

open Lean Meta Solver.Optimize

namespace Solver

/-! ## Lemmas validating the normalization and simplifications rules on `Prop` -/

protected theorem Solver.and_left {a b : Prop} (h : a ∧ b) : a := by apply (And.left h)
protected theorem Solver.and_right {a b : Prop} (h : a ∧ b) : b := by apply (And.right h)

/-- Return `Solver.and_left` const expression and cache result. -/
def mkSolverAndLeft : TranslateEnvT Expr := mkExpr (mkConst ``Solver.and_left)

/-- Return `Solver.and_right` const expression and cache result. -/
def mkSolverAndRight : TranslateEnvT Expr := mkExpr (mkConst ``Solver.and_right)

end Solver
