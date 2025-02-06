import Lean
import Solver.Optimize.OptimizeDecide
import Solver.Optimize.OptimizePropNot
import Solver.Optimize.Utils


open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `not` :
     - ! (! e) ==> e
     - !(decide e) ==> decide (¬ p)
   Assume that f = Expr.const ``not.
   Do nothing if operator is partially applied (i.e., args.size < 1)
   NOTE: `not` on constant values are handled via `reduceApp`.
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then return (← mkAppExpr f args)
 let op := args[0]!
 if let some e := boolNot? op then return e
 if let some (e, d) := decide? op then
   return (← optimizeDecideCore op.getAppFn #[← optimizeNot (← mkPropNotOp) #[e], d])
 mkAppExpr f args


/-- Apply simplification/normalization rules on Boolean `not` operator.
-/
def optimizeBoolNot? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const ``not _ => some <$> optimizeBoolNot f args
 | _ => pure none

end Solver.Optimize
