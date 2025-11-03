import Lean
import Solver.Optimize.Rewriting.Utils
import Solver.Optimize.Env


open Lean Meta
namespace Solver.Optimize

 /-- Given `a` and `b` the operands for `and`, apply the simplification rules:
     - When true = a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some b`
     - When true = b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = a
        - return `some false`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = b
        - return `some false`
     - Otherwise:
        - return `none`
 -/
 def andBoolReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if hyps.contains (← mkEqBool a true) then return b
  if hyps.contains (← mkEqBool b true) then return a
  if hyps.contains (← mkEqBool a false) then return (← mkBoolFalse)
  if hyps.contains (← mkEqBool b false) then return (← mkPropFalse)
  return none

/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false
     - true && e ==> e
     - e && not e ==> false
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 && e2 ===> e2 (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 && e2 ===> e1 (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)
     - e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``and.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `and` expected at this stage)

   TODO: reordering on list of `&&` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolAnd (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeBoolAnd: exactly two arguments expected"
 let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``false _ := op1 then return op1
 if let Expr.const ``true _ := op1 then return op2
 if (← exprEq op1 op2) then return op1
 if (← isBoolNotExprOf op2 op1) then return (← mkBoolFalse)
 if let some r ← andBoolReduction? op1 op2 then return r
 -- no caching at this level as optimizeBoolAnd is called by optimizeDecideBoolAnd
 return mkApp2 f op1 op2

 /-- Given `a` and `b` the operands for `or`, apply the simplification rules:
     - When true = a := _ ∈ hypothesisContext.hypothesisMap,
        - return `some true`
     - When true = b := _ ∈ hypothesisContext.hypothesisMap,
        - return `some true`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = a
        - return `some b`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = b
        - return `some a`
     - Otherwise:
        - return `none`
 -/
 def orBoolReduction? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  if hyps.contains (← mkEqBool a true) then return (← mkBoolTrue)
  if hyps.contains (← mkEqBool b true) then return (← mkBoolTrue)
  if hyps.contains (← mkEqBool a false) then return b
  if hyps.contains (← mkEqBool b false) then return a
  return none

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e
     - true || e ==> true
     - e || not e ==> true
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)
     - e1 || e2 ===> true (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 || e2 ===> true (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)
     - e1 || e2 ===> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)
     - e1 || e2 ===> e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)
     - e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)
   Assume that f = Expr.const ``or.
   An error is triggered when args.size ≠ 2 (i.e., only fully applied `or` expected at this stage)

   TODO: reordering on list of `||` must be performed to regroup all `decide e`
   together and all boolean expression together. The reordering must be
   deterministic to produce the same sequence.
   TODO: consider additional simplification rules
-/
def optimizeBoolOr (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeBoolOr: exactly two arguments expected"
 let opArgs ← reorderBoolOp args -- error triggered when args.size ≠ 2
 let op1 := opArgs[0]!
 let op2 := opArgs[1]!
 if let Expr.const ``false _ := op1 then return op2
 if let Expr.const ``true _ := op1 then return op1
 if (← exprEq op1 op2) then return op1
 if (← isBoolNotExprOf op2 op1) then return (← mkBoolTrue)
 if let some r ← orBoolReduction? op1 op2 then return r
 -- no caching at this level as optimizeBoolAnd is called by optimizeDecideBoolOr
 return mkApp2 f op1 op2

end Solver.Optimize
