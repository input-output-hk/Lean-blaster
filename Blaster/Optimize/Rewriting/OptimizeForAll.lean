import Lean
import Blaster.Optimize.RetentionCounters
import Blaster.Optimize.Hypotheses

open Lean Meta Elab
namespace Blaster.Optimize

/-- `mkImpliesExpr a b` return expression `a → b` without applying any normalization. -/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default a b

/-- Given `a → b`, apply the simplification rules:
    - When isProp:
       - When `a := True`
          - return `some $ instantiate1' b True.intro`
       - When `a := False
          - return `some True`
       - When a := sif h : c then e1 else e2 ∧ ¬ b.hasLooseBVars`
         - return `some $ sif h : c then e1 → b else e2 → b`
    - Otherwise:
       - return `none`
-/
def forallReduction? (a : Expr) (b : Expr) (isProp : Bool) : TranslateEnvT (Option Expr) := do
 if isProp then
   match a with
   | Expr.const ``True _ => instantiateShared1 b (← mkTrueIntro)
   | Expr.const ``False _ => mkPropTrue
   | _ => return none
 else return none

 /-- Given `a → b`, apply the following normalization rule:
      - When `b := False ∧ Type(a) = Prop`
          - return `some ¬ a`
      - Otherwise
          - return `none`
 -/
 def isNotDef? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
 if ← isPropEnv a then
   match b with
   | Expr.const ``False _ =>
       setRestart
       mkAppExpr (← mkPropNotOp) a
   | _ => return none
 else return none

 /-- Given `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = ¬ b
        - return `some ¬ a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some ¬ a`
     - Otherwise:
        - return `none`
 -/
 def impliesToNeg? (a : Expr) (b : Expr) (isProp : Bool) : TranslateEnvT (Option Expr) := do
  if !isProp then return none
  if (← notInHypMap b).isSome then
    setRestart
    mkAppExpr (← mkPropNotOp) a
  else return none

 /-- Given `a → b`, apply the simplification rules:
      - When ∃ e := _ ∈ h, e = b
          - return `some True`
      - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = b
          - return `some True`
      - When isProp ∧ ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some True`
     - Otherwise:
        - return `none`
 -/
 def impliesToTrue? (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  if (← inHypMap b).isSome then return ← mkPropTrue
  if !(← isPropEnv a) then return none
  if (← notInHypMap a).isSome then return ← mkPropTrue
  return none


/-- Given `h : a → b` returns `true` only when the following condition is satisfied:
     - ∃ h : a → b := _ ∈ hypothesisContext.hypothesisMap
-/
def impliesInHyp (h : Expr) (isProp : Bool) : TranslateEnvT Bool :=
   if isProp then hypMapContains h else return false

/-- Given `h : a → b`, apply the simplification rules:
    - When isPropEnv a ∧ a := p ∈ hypothesisContext.hypothesisMap
       - When ¬ containsFVar b h.fvarId!
          - return `some b`
       - When containsFVar b h.fvarId!
          - return `some b[h/p]
    - Otherwise:
       - return `none`
-/
def hypReduction? (mscope : Option CtxScope) (h : Expr) (a : Expr) (b : Expr) (isProp : Bool) : TranslateEnvT (Option Expr) := do
 if (← isPropEnv a) && isProp then
   -- We only consider parent context for hypReduction
   let some s := mscope | throwEnvError "hypReduction?: CtxScope expected !!!"
   withParentHyps s $ do
     match (← inHypMap a) with
     | none => return none
     | some p =>
           if !containsFVar b h
           then return b
           else replaceShared b (λ h' => do if exprEq h' h then return some p else return none)
 else return none

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True
      - e → False ==> ¬ e
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ isProp)
      - e1 → e2 ==> True (if ∃ e1 → e2 := _ ∈ hypothesisContext.hypothesisMap)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2)
      - e1 → e2 ==> True (if ∃ e2 := _ ∈ h)
      - e1 → e2 ==> True (if ∃ e2 := _ ∈ hypothesisContext.hypothesisMap)
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1 ∧ isProp)
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ containsFVar e2 h.fvarId! ∧ isProp)
      - h : e1 → e2 ==> e2[h/h'] (if e1 := h' ∈ hypothesisContext.hypothesisMap ∧ containsFVar e2 h.fvarId! ∧ isProp)
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ containsFVar e n.fvarId!)
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  Assume that `h` corresponds to the hypothesis map updated with hypotheses in `t`.
-/
def optimizeForall (n : Expr) (t : Expr) (b : Expr) (s : Option CtxScope) (isProp : Bool) : TranslateEnvT Expr := do
  Retention.crumb "optForall"
  if let Expr.const ``True _ := b then return b
  if let some r ← isNotDef? t b then return r
  if exprEq t b then if isProp then return (← mkPropTrue)
  let imp ← mkForallFVarExpr n b
  if (← impliesInHyp imp isProp) then return (← mkPropTrue)
  if let some r ← impliesToNeg? t b isProp then return r
  if let some r ← impliesToTrue? t b then return r
  if let some r ← hypReduction? s n t b isProp then return r
  if (← (isSortOrInhabited t) <&&> (pure isProp) <&&> (pure !containsFVar b n)) then return b
  return imp

end Blaster.Optimize
