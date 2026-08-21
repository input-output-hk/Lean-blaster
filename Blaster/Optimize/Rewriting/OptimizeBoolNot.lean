import Lean
import Blaster.Optimize.Rewriting.Utils

open Lean Meta
namespace Blaster.Optimize

/-- Given op the operand for `not`,
     - When op := decide' e
        - return `some decide' (¬ e)`
    - Otherwise:
        - return `none`
-/
@[always_inline, inline]
def notDecideProp? (op : Expr) : TranslateEnvT (Option Expr) := do
 let some e := decide'? op | return none
 setRestart
 return mkApp op.getAppFn (mkApp (← mkPropNotOp) e)

/-- Apply the following simplification/normalization rules on `not` :
     - ! true ==> false                 [proof: Bool.not_true]
     - ! false ==> true                 [proof: Bool.not_false]
     - ! (! e) ==> e                    [proof: Bool.not_not]
     - !(decide' e) ==> decide' (¬ e)
   Assume that f = Expr.const ``not.
   An error is triggered if args.size ≠ 1 (i.e., only fully applied `not` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeBoolNot (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 1 then throwEnvError "optimizeBoolNot: exactly one argument expected"
 let op := args[0]!
 match op with
 | Expr.const ``true _ =>
    pushProofStep (.rewrite (mkConst ``Bool.not_true))
    mkBoolFalse
 | Expr.const ``false _ =>
    pushProofStep (.rewrite (mkConst ``Bool.not_false))
    mkBoolTrue
 | _ =>
    if let some e := boolNot? op then
      pushProofStep (.rewrite (mkConst ``Bool.not_not))
      return e
    if let some r ← notDecideProp? op then return r
    return (mkApp f op)

/-- Apply simplification/normalization rules on Boolean `not` operator.
-/
def optimizeBoolNot? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
 match f with
 | Expr.const ``not _ => optimizeBoolNot f args
 | _ => pure none

end Blaster.Optimize
