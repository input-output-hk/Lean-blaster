import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.Utils

open Lean Meta

namespace Solver.Optimize

/-- Given `n` a const name and `l` a list level, apply the following normalization rule:
     - ``Nat.zero ===> Expr.lit (Literal.natVal 0)
-/
def normConst (n : Name) (l : List Level) : TranslateEnvT Expr := do
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ => return (mkConst n l)

end Solver.Optimize
