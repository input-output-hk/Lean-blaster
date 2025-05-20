import Lean
import Solver.Optimize.Rewriting.OptimizeForAll

open Lean Meta
namespace Solver.Optimize

 /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
     - When a := _ ∈ hypsInContext,
        - return `some b`
     - When b := _ ∈ hypsInContext,
        - return `some a`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ a
        - return `some False`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ b
        - return `some False`
     - Otherwise:
        - return `none`
 -/
 def andPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypsInContext
  if (← inHypMap a hyps).isSome then return b
  if (← inHypMap b hyps).isSome then return a
  if (← notInHypMap a hyps) then return (← mkPropFalse)
  if (← notInHypMap b hyps) then return (← mkPropFalse)
  return none


/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False
     - True ∧ e ==> e
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∧ ¬ e ==> False
     - true = e ∧ false = e ==> False
     - e1 ∧ (e1 → e2) ==> e1 ∧ e2
     - e1 ∧ (e2 → e1) ==> e1
     - e1 ∧ e2 ==> e2 (if e1 := _ ∈ hypsInContext)
     - e1 ∧ e2 ==> e1 (if e2 := _ ∈ hypsInContext)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypsInContext, e = ¬ e1)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypsInContext, e = ¬ e2)
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `And` expected at this stage)
   TODO: consider additional simplification rules
-/
partial def optimizeAnd (f : Expr) (args : Array Expr) (cacheResult := true) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeAnd: exactly two arguments expected"
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _  := op1 then return op1
 if let Expr.const ``True _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return (← mkPropFalse)
 if (← isNegBoolEqOf op2 op1) then return (← mkPropFalse)
 if let some r ← andImpliesReduce? op1 op2 then return r
 if let some r ← andPropReduction? op1 op2 then return r
 mkExpr (mkApp2 f op1 op2) cacheResult

 where
   /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
       - When `b := a → c`
          - return `some a ∧ c`
       - When `b := c → a`
          - return `some a`
       - Otherwise:
         - return `none`
   -/
   andImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
     match b with
     | Expr.forallE _ t c _ =>
         if (← exprEq t a) then return (← optimizeAnd f #[a, c])
         if (← exprEq c a) then return a
         return none
     | _ => return none

 /-- Given `a` and `b` the operands for `Or`, apply the simplification rules:
     - When a := _ ∈ hypsInContext,
        - return `some True`
     - When b := _ ∈ hypsInContext,
        - return `some True`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ a
        - return `some b`
     - When ∃ e := _ ∈ hypsInContext, e = ¬ b
        - return `some a`
     - Otherwise:
        - return `none`
 -/
 def orPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypsInContext
  if (← inHypMap a hyps).isSome then return (← mkPropTrue)
  if (← inHypMap b hyps).isSome then return (← mkPropTrue)
  if (← notInHypMap a hyps) then return b
  if (← notInHypMap b hyps) then return a
  return none


/-- Given `a` and `b` the operands for `Or`, apply the simplification rules:
    - When `b := a → c`
       - return `some True`
    - When `b := c → a`
       - return `some b`
    - Otherwise:
      - return `none`
-/
def orImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  match b with
  | Expr.forallE _ t c _ =>
      if (← exprEq t a) then return (← mkPropTrue)
      if (← exprEq c a) then return b
      return none
  | _ => return none

/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e
     - True ∨ e ==> True
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e ∨ ¬ e ==> True (classical)
     - true = e ∨ false = e ==> True
     - e1 ∨ (e1 → e2) ==> True
     - e1 ∨ (e2 → e1) ==> (e2 → e1)
     - e1 ∨ e2 ==> True (if e1 := _ ∈ hypsInContext)
     - e1 ∨ e2 ==> True (if e2 := _ ∈ hypsInContext)
     - e1 ∨ e2 ==> e2 (if ∃ e := _ ∈ hypsInContext, e = ¬ e1)
     - e1 ∨ e2 ==> e1 (if ∃ e := _ ∈ hypsInContext, e = ¬ e2)
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
 if let some r ← orImpliesReduce? op1 op2 then return r
 if let some r ← orPropReduction? op1 op2 then return r
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
