import Lean
import Solver.Optimize.Utils
import Solver.Translate.Env

open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∧ ¬ e ==> False
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: The `reduceApp` rule will not reduce `And` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _  := op1 then return op1
 if let Expr.const ``True _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return (← mkPropFalse)
 mkExpr (mkApp2 f op1 op2) cacheResult



/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∨ ¬ e ==> True (classical)
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   Do nothing if operator is partially applied (i.e., args.size < 2)
   NOTE: The `reduceApp` rule will not reduce `Or` applied to `Prop` constructors.
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then return (← mkAppExpr f args)
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _ := op1 then return op2
 if let Expr.const ``True _ := op1 then return op1
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return (← mkPropTrue)
 -- should not cache at this stage as optimizeAnd is called
 -- by optimizeBoolPropOr
 mkExpr (mkApp2 f op1 op2) cacheResult

end Solver.Optimize
