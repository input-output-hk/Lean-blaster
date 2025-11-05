import Lean
import Solver.Optimize.Rewriting.Utils

open Lean Meta
namespace Solver.Optimize

/-- Given op the operand for `not`,
     - When op := decide e
        - return `some decide (¬ e)`
    - Otherwise:
        - return `none`
-/
@[always_inline, inline]
def notDecideProp? (op : Expr) : TranslateEnvT (Option Expr) := do
 let some (e, d) := decide? op | return none
 setRestart
 return mkApp2 op.getAppFn (mkApp (← mkPropNotOp) e) d

/-- Apply the following simplification/normalization rules on `not` :
     - ! true ==> false
     - ! false ==> true
     - ! (! e) ==> e
     - !(decide e) ==> decide (¬ e)
   Assume that f = Expr.const ``not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `not` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeBoolNot: exactly one argument expected"
 let op := args[0]!
 match op with
 | Expr.const ``true _ => mkBoolFalse
 | Expr.const ``false _ => mkBoolTrue
 | _ =>
    if let some e := boolNot? op then return e
    if let some r ← notDecideProp? op then return r
    return (mkApp f op)

/-- Apply simplification/normalization rules on Boolean `not` operator.
-/
def optimizeBoolNot? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const ``not _ => optimizeBoolNot f args
 | _ => pure none

end Solver.Optimize
