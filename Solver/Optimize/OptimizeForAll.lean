import Lean
import Solver.Translate.Env
open Lean Meta

namespace Solver

/-- Apply the following simplification/normalized rules on `forallE`
   - ∀ (n : t), True ==> True
   - ∀ (n : t), False ==> False
  TODO: consider additional simplification rules
-/
def optimizeForall (n : Expr) (b : Expr) : TranslateEnvT Expr := do
  match b with
  | Expr.const ``True _ | Expr.const ``False _ => pure b
  | _ => mkForallFVars #[n] b

end Solver
