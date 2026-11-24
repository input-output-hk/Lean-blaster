import Lean
import Blaster.Optimize.Hypotheses

open Lean Meta Elab
namespace Blaster.Optimize

/-- `mkImpliesExpr a b` return expression `a → b` without applying any normalization. -/
def mkImpliesExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default a b

/-- Given `a → b`, apply the simplification rules:
    - When isProp:
       - When `a := True`
          - return `some $ instantiate1' b True.intro`     [proof: true_implies, Blaster.implies_eq_right_of_hyp_dep]
       - When `a := False
          - return `some True`                              [proof: False.elim, forall_false]
       - When a := sif h : c then e1 else e2 ∧ ¬ b.hasLooseBVars`
         - return `some $ sif h : c then e1 → b else e2 → b`
    - Otherwise:
       - return `none`
    Called before the binder is opened: `b` is the body, with the binder as loose bound variable 0.
-/
def forallReduction? (a : Expr) (b : Expr) (isProp : Bool) : TranslateEnvT (Option Expr) := do
 if isProp then
   match a with
   | Expr.const ``True _ =>
       if b.hasLooseBVar 0 then
         pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.implies_eq_right_of_hyp_dep)
           a (mkLambda `h .default a b) (mkConst ``True.intro)))
       else pushProofStep (.rewrite (mkConst ``true_implies))
       instantiateShared1 b (← mkTrueIntro)
   | Expr.const ``False _ =>
       -- `fun h : False => False.elim b`, closing the forall or its body once the replay intro'd it
       pushProofStep (.exact (mkLambda `h .default a (mkApp2 (mkConst ``False.elim [levelZero]) b (mkBVar 0))))
       pushProofStep (.rewrite (mkConst ``forall_false))
       mkPropTrue
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
       pushProofStep (.rewrite (mkApp (mkConst ``Lean.Grind.imp_false_eq) a))
       mkAppExpr (← mkPropNotOp) a
   | _ => return none
 else return none

/-- Given (p : ¬ b), push the step (a → b) = ¬ a,
abstracting the implementation's binder n out of p
-/
def pushImpliesNegProofSteps (n a p b : Expr) : TranslateEnvT Unit :=
   pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.implies_eq_neg_of_imp_not) a b (mkLambda `h .default a (p.abstract #[n]))))

 /-- Given `n : a` and `a → b`, apply the simplification rules:
     - When ∃ e := _ ∈ h, e = ¬ b
        - return `some ¬ a`
     - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ b
        - return `some ¬ a`
     - Otherwise:
        - return `none`
    The binder `n` is only used by the proof step: the proof found may mention it.
 -/
 def impliesToNeg? (n : Expr) (a : Expr) (b : Expr) (isProp : Bool) : TranslateEnvT (Option Expr) := do
  if !isProp then return none
  if let some p ← notInHypMap b then
    setRestart
    pushImpliesNegProofSteps n a p b
    mkAppExpr (← mkPropNotOp) a
  else return none

 /-- Given `p : b` and `n : a`, push the steps closing `a → b`: `p` itself when the replay
     introduced `n`, and `(a → b) = True` when the implication is left in a sub-term. -/
 def pushImpliesTrueSteps (n a b p : Expr) : TranslateEnvT Unit := do
  pushProofStep (.exact p)
  let imp := mkForall `h .default a (b.abstract #[n])
  pushProofStep (.rewrite (mkApp2 (mkConst ``eq_true) imp (mkLambda `h .default a (p.abstract #[n]))))

 /-- Given `n : a` and `a → b`, apply the simplification rules:
      - When ∃ e := _ ∈ h, e = b
          - return `some True`
      - When ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = b
          - return `some True`
      - When isProp ∧ ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ a
        - return `some True`
     - Otherwise:
        - return `none`
    The binder `n` is only used by the proof step: the proof found may mention it.
 -/
 def impliesToTrue? (n : Expr) (a : Expr) (b : Expr) : TranslateEnvT (Option Expr) := do
  if let some p ← inHypMap b then
    pushImpliesTrueSteps n a b p
    return ← mkPropTrue
  if !(← isPropEnv a) then return none
  if let some q ← notInHypMap a then
    pushImpliesTrueSteps n a b (mkApp4 (mkConst ``absurd [levelZero]) a b n q)
    return ← mkPropTrue
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
           then
             pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.implies_eq_right_of_hyp) a b p))
             return b
           else
             pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.implies_eq_right_of_hyp_dep)
               a (mkLambda `h .default a (b.abstract #[h])) p))
             replaceShared b (λ h' => do if exprEq h' h then return some p else return none)
 else return none

/-- Apply the following simplification/normalized rules on `forallE`.
    Note that implication `a → b` is internally represented as `forallE _ a b bi`.
    The simplification/normalization rules applied are:
      - ∀ (n : t), True | e → True ==> True                                  [proof: eq_true]
      - e → False ==> ¬ e                                                    [proof: Lean.Grind.imp_false_eq]
      - e1 → e2 ==> True (if e1 =ₚₜᵣ e2 ∧ isProp)                             [proof: the premise, Blaster.implies_self_eq_true]
      - e1 → e2 ==> True (if ∃ e1 → e2 := _ ∈ hypothesisContext.hypothesisMap) [proof: the proof found applied to e1, eq_true]
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ h, e = ¬ e2)                                [proof: Blaster.implies_eq_neg_of_imp_not]
      - e1 → e2 ==> ¬ e1 (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e2) [proof: Blaster.implies_eq_neg_of_imp_not]
      - e1 → e2 ==> True (if ∃ e2 := _ ∈ h)                                  [proof: the proof of e2 found, eq_true]
      - e1 → e2 ==> True (if ∃ e2 := _ ∈ hypothesisContext.hypothesisMap)  [proof: the proof of e2 found, eq_true]
      - e1 → e2 ==> True (if ∃ e := _ ∈ hypothesisContext.hypothesisMap, e = ¬ e1 ∧ isProp) [proof: absurd, eq_true]
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ containsFVar e2 h.fvarId! ∧ isProp) [proof: Blaster.implies_eq_right_of_hyp]
      - h : e1 → e2 ==> e2[h/h'] (if e1 := h' ∈ hypothesisContext.hypothesisMap ∧ containsFVar e2 h.fvarId! ∧ isProp) [proof: Blaster.implies_eq_right_of_hyp_dep]
      - ∀ (n : t), e ===> e (if isSortOrInhabited t ∧ Type(e) = Prop ∧ ¬ containsFVar e n.fvarId!) [proof: Blaster.forall_coi]
  Assume that `n` is a free variable expression. An error is triggered if this is not the case.
  Assume that `h` corresponds to the hypothesis map updated with hypotheses in `t`.
-/
def optimizeForall (n : Expr) (t : Expr) (b : Expr) (s : Option CtxScope) (isProp : Bool) : TranslateEnvT Expr := do
  if let Expr.const ``True _ := b then
    pushImpliesTrueSteps n t b (mkConst ``True.intro)
    return b
  if let some r ← isNotDef? t b then return r
  if exprEq t b then
    if isProp then
      pushProofStep (.exact n)
      pushProofStep (.rewrite (mkConst ``Blaster.implies_self_eq_true))
      return (← mkPropTrue)
  let imp ← mkForallFVarExpr n b
  if (← impliesInHyp imp isProp) then
    if let some p ← hypMapFind? imp then pushImpliesTrueSteps n t b (mkApp p n)
    return (← mkPropTrue)
  if let some r ← impliesToNeg? n t b isProp then return r
  if let some r ← impliesToTrue? n t b then return r
  if let some r ← hypReduction? s n t b isProp then return r
  if (← (isSortOrInhabited t) <&&> (pure isProp) <&&> (pure !containsFVar b n)) then
    -- the sort of `t` is in the cache, as `isSortOrInhabited t` has just inferred it
    if let Expr.sort u ← inferTypeEnv t then
      -- when no instance is built here the replay synthesizes `Nonempty t`
      let inst ← nullaryCtorNonempty? u t
      pushProofStep (.rewrite (mkAppN (mkConst ``Blaster.forall_coi [u]) (#[t, b] ++ inst.toArray)))
    return b
  return imp

end Blaster.Optimize
