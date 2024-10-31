import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env


open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false
     - true && e ==> e
     - e && not e ==> false
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``and.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolAnd (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``false _ := op1 then return op1
 if let Expr.const ``true _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isBoolNotExprOf op2 op1) then return (← mkBoolFalse)
 mkExpr (mkApp2 f op1 op2) cacheResult

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e
     - true || e ==> true
     - e || not e ==> true
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``or.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   TODO: reordering on list of `||` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolOr (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``false _ := op1 then return op2
 if let Expr.const ``true _ := op1 then return op1
 if (← exprEq op1 op2) then return op1
 if (← isBoolNotExprOf op2 op1) then return (← mkBoolTrue)
 mkExpr (mkApp2 f op1 op2) cacheResult

end Solver.Optimize
