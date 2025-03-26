import Lean
import Solver.Optimize.Rewriting.OptimizeForAll

open Lean Meta
namespace Solver.Optimize

/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∧ ¬ e ==> False
     - true = e ∧ false = e ==> False
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `And` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeAnd: exactly two arguments expected"
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _  := op1 then return op1
 if let Expr.const ``True _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return (← mkPropFalse)
 if (← isNegBoolEqOf op2 op1) then return (← mkPropFalse)
 mkExpr (mkApp2 f op1 op2) cacheResult



/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∨ ¬ e ==> True (classical)
     - true = e ∨ false = e ==> True
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Or` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeOr: exactly two arguments expected"
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _ := op1 then return op2
 if let Expr.const ``True _ := op1 then return op1
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return (← mkPropTrue)
 if (← isNegBoolEqOf op2 op1) then return (← mkPropTrue)
 -- should not cache at this stage as optimizeAnd is called
 -- by optimizeBoolPropOr
 mkExpr (mkApp2 f op1 op2) cacheResult


/-- Normalize `p ↔ p` to `p → q ∧ p → q`
    An error is triggered when args.size ≠ 2 (i.e., only fully applied `↔` expected at this stage)
-/
def optimizeIff (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIff: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 optimizeAnd (← mkPropAndOp) #[← mkImpliesExpr op1 op2, ← mkImpliesExpr op2 op1]

end Solver.Optimize
