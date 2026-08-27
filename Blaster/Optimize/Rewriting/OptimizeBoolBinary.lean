import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env
import Blaster.Optimize.Lemmas.LemmasBool

open Lean Meta
namespace Blaster.Optimize

/-- Proof-returning companion to looking for `mkEqBool b true` in the hypothesis context
  for a non literal `e`: when `true = e` is a hypothesis in the context,
  return its proof; otherwise `none`.
-/
def trueEqProof? (e : Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  return hyps.get? (← mkEqBool e true)

/-- Proof-returning companion to looking for `mkEqBool b false` in the hypothesis context
  for a non literal `e`: when `false = e` is a hypothesis in the context,
  return its proof; otherwise `none`.
-/
def falseEqProof? (e: Expr) : TranslateEnvT (Option Expr) := do
  let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
  return hyps.get? (← mkEqBool e false)

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
  if let some p ← trueEqProof? a then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.true_and_with_hyp) a b p))
    return b
  if let some p ← trueEqProof? b then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.and_true_with_hyp) a b p))
    return a
  if let some p ← falseEqProof? a then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.false_and_with_hyp) a b p))
    return (← mkBoolFalse)
  if let some p ← falseEqProof? b then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.and_false_with_hyp) a b p))
    return (← mkBoolFalse)
  return none

/-- Apply the following simplification/normalization rules on `and` :
     - false && e ==> false                                                                  [proof: Bool.false_and]
     - true && e ==> e                                                                       [proof: Bool.true_and]
     - e && not e ==> false                                                                  [proof: Bool.and_not_self]
     - e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)                                                        [proof: Bool.and_self]
     - e1 && e2 ===> e2 (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)               [proof: Blaster.true_and_with_hyp]
     - e1 && e2 ===> e1 (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)               [proof: Blaster.and_true_with_hyp]
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)  [proof: Blaster.false_and_with_hyp]
     - e1 && e2 ===> false (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)  [proof: Blaster.and_false_with_hyp]
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
 let op1 := args[0]!
 let op2 := args[1]!
 if let Expr.const ``false _ := op1 then
   pushProofStep (.rewrite (mkConst ``Bool.false_and))
   return op1
 if let Expr.const ``true _ := op1 then
   pushProofStep (.rewrite (mkConst ``Bool.true_and))
   return op2
 if exprEq op1 op2 then
   pushProofStep (.rewrite (mkConst ``Bool.and_self))
   return op1
 if isBoolNotExprOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Bool.and_not_self))
   return (← mkBoolFalse)
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
  if let some p ← trueEqProof? a then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.true_or_with_hyp) a b p))
    return (← mkBoolTrue)
  if let some p ← trueEqProof? b then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.or_true_with_hyp) a b p))
    return (← mkBoolTrue)
  if let some p ← falseEqProof? a then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.false_or_with_hyp) a b p))
    return b
  if let some p ← falseEqProof? b then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.or_false_with_hyp) a b p))
    return a
  return none

/-- Apply the following simplification/normalization rules on `or` :
     - false || e ==> e                                                                      [proof: Bool.false_or]
     - true || e ==> true                                                                    [proof: Bool.true_or]
     - e || not e ==> true                                                                   [proof: Bool.or_not_self]
     - e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)                                                        [proof: Bool.or_self]
     - e1 || e2 ===> true (if true = e1 := _ ∈ hypothesisContext.hypothesisMap)             [proof: Blaster.true_or_with_hyp]
     - e1 || e2 ===> true (if true = e2 := _ ∈ hypothesisContext.hypothesisMap)             [proof: Blaster.or_true_with_hyp]
     - e1 || e2 ===> e2 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e1)     [proof: Blaster.false_or_with_hyp]
     - e1 || e2 ===> e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = false = e2)     [proof: Blaster.or_false_with_hyp]
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
 let op1 := args[0]!
 let op2 := args[1]!
 if let Expr.const ``false _ := op1 then
   pushProofStep (.rewrite (mkConst ``Bool.false_or))
   return op2
 if let Expr.const ``true _ := op1 then
   pushProofStep (.rewrite (mkConst ``Bool.true_or))
   return op1
 if exprEq op1 op2 then
   pushProofStep (.rewrite (mkConst ``Bool.or_self))
   return op1
 if isBoolNotExprOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Bool.or_not_self))
   return (← mkBoolTrue)
 if let some r ← orBoolReduction? op1 op2 then return r
 -- no caching at this level as optimizeBoolAnd is called by optimizeDecideBoolOr
 return mkApp2 f op1 op2

end Blaster.Optimize
