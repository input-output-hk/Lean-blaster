import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.Utils

open Lean Meta

namespace Solver.Optimize

/-- Given `n` a const name and `l` a list level, apply the following normalization rule:
     - when `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - when `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - otherwise
         - return `mkConst n l`
-/
def normConst (n : Name) (l : List Level) (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ =>
    match (← getConstInfo n) with
    | ConstantInfo.opaqueInfo opVal => optimizer opVal.value
    | _ => return (mkConst n l)

end Solver.Optimize
