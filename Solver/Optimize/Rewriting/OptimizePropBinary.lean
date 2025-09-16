import Lean
import Solver.Optimize.Rewriting.OptimizeForAll

open Lean Meta
namespace Solver.Optimize

 /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
     - When a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some b`
     - When b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some False`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some False`
     - Otherwise:
        - return `none`
 -/
 def andPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
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
     - e1 ∧ (e1 → e2) ==> e1 ∧ e2 (if ¬ e2.hasLooseBVars)
     - e1 ∧ (e2 → e1) ==> e1
     - e1 ∧ e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∧ e2 ==> e1 (if e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1)
     - e1 ∧ e2 ==> False (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
     - e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``And.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `And` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeAnd: exactly two arguments expected"
 let opArgs ← reorderPropOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``False _  := op1 then return op1
 if let Expr.const ``True _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isNotExprOf op2 op1) then return ← mkPropFalse
 if (← isNegBoolEqOf op2 op1) then return ← mkPropFalse
 if let some r ← andImpliesReduce? op1 op2 then return r
 if let some r ← andPropReduction? op1 op2 then return r
 -- no caching at this level as optimizeAnd is called by optimizeBoolPropAnd
 return mkApp2 f op1 op2

 where
   /-- Given `a` and `b` the operands for `And`, apply the simplification rules:
       - When `b := a → c ∧ ¬ c.hasLooseBVars`
          - return `some a ∧ c`
       - When `b := c → a`
          - return `some a`
       - Otherwise:
         - return `none`
   -/
   andImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
     match b with
     | Expr.forallE _ t c _ =>
         if (← exprEq t a) && !(c.hasLooseBVars) then
           setRestart
           return mkApp2 f a c
         if (← exprEq c a) then return a -- no need to restart here
         return none
     | _ => return none

 /-- Given `a` and `b` the operands for `Or`, apply the simplification rules:
     - When a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some True`
     - When b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some True`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some b`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some a`
     - Otherwise:
        - return `none`
 -/
 def orPropReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
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
     - e1 ∨ e2 ==> True (if e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∨ e2 ==> True (if e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 ∨ e2 ==> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1)
     - e1 ∨ e2 ==> e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
     - e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``Or.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `Or` expected at this stage)
   TODO: consider additional simplification rules
-/
def optimizeOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
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
 -- no caching at this level as optimizeOr is called by optimizeBoolPropOr
 return mkApp2 f op1 op2


/-- Normalize `p ↔ p` to `p → q ∧ p → q`
    An error is triggered when args.size ≠ 2 (i.e., only fully applied `↔` expected at this stage)
-/
def optimizeIff (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIff: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 setRestart
 return mkApp2 (← mkPropAndOp) (← mkImpliesExpr op1 op2) (← mkImpliesExpr op2 op1)

end Solver.Optimize
