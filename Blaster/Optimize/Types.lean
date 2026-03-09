import Lean

namespace Blaster.Optimize

open Lean

/-- The result of a single optimization step with its proof.
    - `optExpr` : the optimized expression
    - `proof`: a term of type `original = expr`
-/
structure OptimizeResult where
  optExpr : Expr
  proof : Option Expr

end Blaster.Optimize
