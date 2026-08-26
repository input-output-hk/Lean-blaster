import Lean
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Meta
namespace Blaster.Optimize


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
  if (← notInHypMap a hyps).isSome then return (← mkPropFalse)
  if (← notInHypMap b hyps).isSome then return (← mkPropFalse)
  return none


/-- Apply the following simplification/normalization rules on `And` :
     - False ∧ e ==> False                                  [proof: false_and]
     - True ∧ e ==> e                                       [proof: true_and]
     - e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)                        [proof: and_self]
     - e ∧ ¬ e ==> False                                    [proof: Blaster.and_not_self_is_false]
     - true = e ∧ false = e ==> False                       [proof: Blaster.true_and_false_is_false]
     - e1 ∧ (e1 → e2) ==> e1 ∧ e2 (if ¬ e2.hasLooseBVars)
     - e1 ∧ (e2 → e1) ==> e1
     - (e1 → e2) ∧ (¬ e1 → e2) ==> e2
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
 let op1 := args[0]!
 let op2 := args[1]!
 if let Expr.const ``False _  := op1 then
   pushProofStep (.rewrite (mkConst ``false_and))
   return op1
 if let Expr.const ``True _ := op1 then
   pushProofStep (.rewrite (mkConst ``true_and))
   return op2
 if exprEq op1 op2 then
   pushProofStep (.rewrite (mkConst ``and_self))
   return op1
 if isNotExprOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Blaster.and_not_self_is_false))
   return ← mkPropFalse
 if isNegBoolEqOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Blaster.true_and_false_is_false))
   return ← mkPropFalse
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
       - When `a := c → d ∧ b := ¬ c → d`
          - return `some d`
       - Otherwise:
         - return `none`
   -/
   andImpliesReduce? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
     match b with
     | Expr.forallE _ t1 c1 _ =>
         if exprEq t1 a && !(c1.hasLooseBVars) then
           pushProofStep (.rewrite (mkConst ``Blaster.and_imp_self_eq_and))
           setRestart
           return mkApp2 f a c1
         if exprEq c1 a then
           pushProofStep (.rewrite (mkConst ``Blaster.and_imp_right_eq_left))
           return a -- no need to restart here
         match a with
         | Expr.forallE _ t2 c2 _ =>
            if !(exprEq c1 c2) then return none
            let not_t2 ← optimizeNot (← mkPropNotOp) (cacheResult := false) #[t2]
            if t1 == not_t2 then
              pushProofStep (.rewrite (mkConst ``Blaster.and_imp_not_imp_eq))
              return c1 -- no need to restart here
            else return none
         | _ => return none
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
  if (← notInHypMap a hyps).isSome then return b
  if (← notInHypMap b hyps).isSome then return a
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
      if exprEq t a then
        pushProofStep (.rewrite (mkConst ``Blaster.or_imp_self_eq_true))
        pushProofStep (.exact (mkConst ``True.intro))
        return (← mkPropTrue)
      if exprEq c a then
        pushProofStep (.rewrite (mkConst ``Blaster.or_imp_right_eq_imp))
        return b
      return none
  | _ => return none

/-- Apply the following simplification/normalization rules on `Or` :
     - False ∨ e ==> e                 [proof: false_or]
     - True ∨ e ==> True               [proof: true_or]
     - e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)   [proof: or_self]
     - e ∨ ¬ e ==> True (classical)    [proof: Blaster.or_not_self_is_true]
     - true = e ∨ false = e ==> True   [proof: Blaster.true_or_false_is_true]
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
 let op1 := args[0]!
 let op2 := args[1]!
 if let Expr.const ``False _ := op1 then
   pushProofStep (.rewrite (mkConst ``false_or))
   return op2
 if let Expr.const ``True _ := op1 then
   pushProofStep (.rewrite (mkConst ``true_or))
   pushProofStep (.exact (mkConst ``True.intro))
   return op1
 if exprEq op1 op2 then
   pushProofStep (.rewrite (mkConst ``or_self))
   return op1
 if isNotExprOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Blaster.or_not_self_is_true))
   pushProofStep (.exact (mkConst ``True.intro))
   return (← mkPropTrue)
 if isNegBoolEqOf op2 op1 then
   pushProofStep (.rewrite (mkConst ``Blaster.true_or_false_is_true))
   pushProofStep (.exact (mkConst ``True.intro))
   return (← mkPropTrue)
 if let some r ← orImpliesReduce? op1 op2 then return r
 if let some r ← orPropReduction? op1 op2 then return r
 -- no caching at this level as optimizeOr is called by optimizeBoolPropOr
 return mkApp2 f op1 op2


/-- Normalize `p ↔ q` to `(p → q) ∧ (q → p)`             [proof: Blaster.iff_eq_implies_and_implies]
    An error is triggered when args.size ≠ 2 (i.e., only fully applied `↔` expected at this stage)
-/
def optimizeIff (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 2 then throwEnvError "optimizeIff: exactly two arguments expected"
 let op1 := args[0]!
 let op2 := args[1]!
 pushProofStep (.rewrite (mkConst ``Blaster.iff_eq_implies_and_implies))
 setRestart
 return mkApp2 (← mkPropAndOp) (← mkImpliesExpr op1 op2) (← mkImpliesExpr op2 op1)

end Blaster.Optimize
