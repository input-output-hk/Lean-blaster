import Lean
import Blaster.Optimize.Rewriting.OptimizeForAll
import Blaster.Optimize.Lemmas.LemmasITE

open Lean Meta Elab
namespace Blaster.Optimize

/-- The universe level of the branch type `iteType` of a `Blaster.dite'`, which its proof steps need
    (the optimizer's `dite'` is always at level one). Not `getLevelEnv`, which writes the optimizer's
    `inferTypeCache` and throws when the type of `iteType` is not syntactically a `Sort`: emission may
    do neither.
-/
@[inline] private def diteLevel (iteType : Expr) : TranslateEnvT Level :=
  withLocalContext $ do getLevel iteType

/-- Given `e` and `c` corresponding respectively to then/else and conditional operands for `Blaster.dite'`,
    perform the following:
     - When `e := λ h : c => x` return `h : c → x`
     - Otherwise:
        - return `h : c => (mkApp e h)`
-/
def toImpliesExpr (e : Expr) (c : Expr) (isThen := false) (isRestart := true) : TranslateEnvT Expr := do
 match e with
 | Expr.lam n t b bi =>
      -- NOTE: we need to propagate the reuse context to the new implication expressions
      let e' ← mkForallExpr n bi t b
      if isThen && isRestart then propagateReuseContext e e' 0 else
        freeRewriteCacheReuse e 0
      return e'
 | _ =>
     mkForallExpr (← Term.mkFreshBinderName) BinderInfo.default c (← mkAppExpr e (← mkBVarExpr 0))

/-- Given `thn` and `els` corresponding respectively to the `then` and `else` terms
    of a `Blaster.dite'` expression, perform the following normalization rules:
      - When `Type(t) = Prop ∧ thn := c → Prop ∧ els := ¬ c → Prop`
          - return `(h : c → thn h) ∧ (h : ¬ c → els h)`   [proof: Blaster.dite'_prop_eq]
      - When `Type(t) ≠ Prop ∨ thn.isLambda ∨ else.isLambda:
          - return `none`
      - Otherwise
           - return ⊥
-/
def diteToPropExpr? (iteType: Expr) (cond : Expr) (thn : Expr) (els : Expr) : TranslateEnvT (Option Expr) := do
  if !iteType.isProp || thn.isLambda || els.isLambda then return none
  pushProofStep (.rewrite (mkApp (mkConst ``Blaster.dite'_prop_eq) cond))
  let leftAnd ← toImpliesExpr thn cond (isThen := true)
  let rightAnd ← toImpliesExpr els (← mkAppExpr (← mkPropNotOp) cond)
  mkApp2Expr (← mkPropAndOp) leftAnd rightAnd


/-- Return `some (true = c')` only when `c := false = c'`.
    This function also checks if `true = c'` is already in cache.
    Otherwise `none`.
-/
def isITEBoolSwap? (c : Expr) : TranslateEnvT (Option Expr) := do
  match eq? c with
  | some (eq_sort, Expr.const ``false _, op2) =>
      mkApp3Expr c.getAppFn eq_sort (← mkBoolTrue) op2
  | _ => return none

/-- Given `e`, a `Blaster.dite'` then/else expression perform the following:
      - When `e := fun h : c => b`:
         - return `b`
      - When `Type(e) := h : c → b`:
         - return `e`
      - Otherwise:
         - return ⊥
-/
def extractDependentITEExpr (e : Expr) : TranslateEnvT Expr := do
  match e with
  | Expr.lam _n _t b _bi => return b
  | _ =>
    if !(← isQuantifiedFun e) then
      throwEnvError "extractDependentITEExpr : lambda/quantified function expected but got {reprStr e}"
    else return e -- case when then/else clause is a quantified function (see theorem `dite_true`).

/-- Given an `Blaster.dite'` expression:
      - return `some sif h : c' then e2 else e1` when `c := ¬ c'`                 [proof: Blaster.dite'_not_swap]
      - return `some sif h : true = c' then e2 else e1` when `c := false = c'`   [proof: Blaster.dite'_bool_swap]
    Otherwise none.

-/
def isITESwap? (f : Expr) (iteType : Expr) (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
 if let Expr.app (Expr.const ``Not _) ne := c
 then
   pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.dite'_not_swap [← diteLevel iteType]) iteType ne))
   mkApp4Expr f iteType ne e t
 else if let some c' ← (isITEBoolSwap? c)
 then
   pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.dite'_bool_swap [← diteLevel iteType]) iteType c.appArg!))
   mkApp4Expr f iteType c' e t
 else return none

/-- Given `c`, `t` and `e` corresponding respectively to the conditional, then and else operands for `Blaster.dite'`,
    apply the following simplification rules:
      - sif h : c then e1 else e2 ==> e1 (if e1 =ₚₜᵣ e2)   [proof: Blaster.dite'_abs]
      - sif h : c then True else False ===> c   [proof: Blaster.dite'_true_false]
      - sif h : c then False else True ===> ¬ c (restart)   [proof: Blaster.dite'_false_true]

      - sif h : c then True else p ===> h : ¬ c → p (restart)   [proof: Blaster.dite'_then_true]
      - sif h : c then c else p ===> h : ¬ c → p (restart)   [proof: Blaster.dite'_then_true]
      - sif h : c then q else p ===> h : ¬ c → p (restart) (if q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_then_true]

      - sif h : c then False else p ===> ¬ c ∧ (h : ¬ c → p) (restart) (if p.hasLooseBVars)   [proof: Blaster.dite'_then_false]
      - sif h : c then False else p ===> ¬ c ∧ p (restart) if (¬ p.hasLooseBVars)   [proof: Blaster.dite'_then_false_const]
      - sif h : c then ¬ c else p ===> ¬ c ∧ (h : ¬ c → p) (restart) (if p.hasLooseBVars)   [proof: Blaster.dite'_then_false]
      - sif h : c then ¬ c else p ===> ¬ c ∧ p (restart) (if ¬ p.hasLooseBVars)   [proof: Blaster.dite'_then_false_const]
      - sif h : c then ¬ q else p ===> ¬ c ∧ (h : ¬ c → p) (restart) (if p.hasLooseBVars ∧ q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_then_false]
      - sif h : c then ¬ q else p ===> ¬ c ∧ p (restart) (if ¬ p.hasLooseBVars ∧ q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_then_false_const]

      - sif h : c then p else True ===> h : c → p   [proof: Blaster.dite'_else_true]
      - sif h : c then p else ¬ c ==> h : c → p   [proof: Blaster.dite'_else_true]
      - sif h : c then p else q ==> h : c → p (if q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_else_true]

      - sif h : c then p else False ===> c ∧ (h : c → p) (restart) (if p.hasLooseBVars)   [proof: Blaster.dite'_else_false]
      - sif h : c then p else False ===> c ∧ p (restart) (if ¬ p.hasLooseBVars)   [proof: Blaster.dite'_else_false_const]
      - sif h : c then p else c ===> c ∧ (h : c → p) (restart) (if p.hasLooseBVars)   [proof: Blaster.dite'_else_false]
      - sif h : c then p else c ===> c ∧ p (restart) (if ¬ p.hasLooseBVars)   [proof: Blaster.dite'_else_false_const]
      - sif h : c then p else ¬ q ===> c ∧ (h : c → p) (restart) (if p.hasLooseBVars ∧ q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_else_false]
      - sif h : c then p else ¬ q ===> c ∧ p (restart) (if ¬ p.hasLooseBVars ∧ q := _ ∈ hypothesisContext.hypothesisMap)   [proof: Blaster.dite'_else_false_const]
-/
def iteSimp? (iteType : Expr) (c : Expr) (t : Expr) (e : Expr) (inDiteChoice := false) : TranslateEnvT (Option Expr) := do
 let thenExpr ← extractDependentITEExpr t
 let elseExpr ← extractDependentITEExpr e
 if exprEq thenExpr elseExpr then
    pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.dite'_abs [← diteLevel iteType]) iteType c thenExpr))
    freeRewriteCacheReuse t 0
    freeRewriteCacheReuse e 0
    return thenExpr -- c cannot be referenced in both thenExpr and elseExpr
 else if !iteType.isProp then return none
 else
   match thenExpr, elseExpr with
   | Expr.const ``True _, Expr.const ``False _ =>
       pushProofStep (.rewrite (mkApp (mkConst ``Blaster.dite'_true_false) c))
       freeRewriteCacheReuse t 0
       freeRewriteCacheReuse e 0
       return c

   | Expr.const ``False _, Expr.const ``True _ =>
        pushProofStep (.rewrite (mkApp (mkConst ``Blaster.dite'_false_true) c))
        freeRewriteCacheReuse t 0
        freeRewriteCacheReuse e 0
        setRestart
        mkAppExpr (← mkPropNotOp) c
   | _, _ =>
      if let some r ← isThenTrue? thenExpr then return r
      if let some r ← isThenFalse? thenExpr elseExpr then return r
      if let some r ← isElseTrue? elseExpr then return r
      if let some r ← isElseFalse? elseExpr thenExpr then return r
      return none

 where

   /-- `some p` with `p` a proof of `e` when `e := True` or `e := p ∈ hypothesisContext.hypothesisMap`.
       Otherwise `none`. -/
   @[always_inline, inline]
   isTrueHyp (e : Expr) : TranslateEnvT (Option Expr) := do
     match e with
     | Expr.const ``True _ => return some (← mkTrueIntro)
     | _ => inHypMap e

   /-- `some p` with `p` a proof of `¬ e` when `e := False` or `¬ e := p ∈ hypothesisContext.hypothesisMap`.
       Otherwise `none`. -/
   @[always_inline, inline]
   isFalseHyp (e : Expr) : TranslateEnvT (Option Expr) := do
     match e with
     | Expr.const ``False _ => return some (← mkNotFalse)
     | _ => notInHypMap e

   /-- Push the step `lemma c q (fun h : hc => p)` of the absorbed branch `q`, which does not use `h`:
       `p` proves `q` (or `¬ q`) under `h : hc` (`c` for the then branch, `¬ c` for the else branch),
       mentioning `h` as loose bound variable `0`. The other branch is left to the replay. -/
   @[always_inline, inline]
   absorbStep (lemma : Name) (hc : Expr) (q : Expr) (p : Expr) : TranslateEnvT Unit :=
     pushProofStep (.rewrite (mkApp3 (mkConst lemma) c q (mkLambda `h BinderInfo.default hc p)))

   @[always_inline, inline]
   isThenTrue? (thenExpr : Expr) : TranslateEnvT (Option Expr) := do
     let hyp? ← isTrueHyp thenExpr
     if hyp?.isSome || exprEq c thenExpr then
       -- `thenExpr` holds by `True.intro`, by its hypothesis, or is `c` itself
       let p := match hyp? with | some p => p | none => mkBVar 0
       absorbStep ``Blaster.dite'_then_true c thenExpr p
       freeRewriteCacheReuse t 0
       setRestart
       toImpliesExpr e (← mkAppExpr (← mkPropNotOp) c)
     else return none

   @[always_inline, inline]
   isThenFalse? (thenExpr : Expr) (elseExpr : Expr) : TranslateEnvT (Option Expr) := do
     let hyp? ← isFalseHyp thenExpr
     if hyp?.isSome || isNotExprOf thenExpr c || isNegBoolEqOf thenExpr c then
       -- `¬ thenExpr` holds by `not_false`, by its hypothesis, or `thenExpr` is `¬ c` or `false = b` for `c := true = b`
       let p := match hyp? with
         | some p => p
         | none =>
           if isNotExprOf thenExpr c then mkApp2 (mkConst ``not_not_intro) c (mkBVar 0)
           else mkApp2 (mkConst ``Blaster.not_false_eq_of_true_eq) c.appArg! (mkBVar 0)
       freeRewriteCacheReuse t 0
       setRestart
       let notExpr ← mkAppExpr (← mkPropNotOp) c
       if elseExpr.hasLooseBVars then
         absorbStep ``Blaster.dite'_then_false c thenExpr p
         let impExpr ← toImpliesExpr e notExpr
         mkApp2Expr (← mkPropAndOp) notExpr impExpr
       else
         absorbStep ``Blaster.dite'_then_false_const c thenExpr p
         freeRewriteCacheReuse e 0
         mkApp2Expr (← mkPropAndOp) notExpr elseExpr
     else return none

   @[always_inline, inline]
   isElseTrue? (elseExpr : Expr) : TranslateEnvT (Option Expr) := do
     let hyp? ← isTrueHyp elseExpr
     if hyp?.isSome || isNotExprOf elseExpr c || isNegBoolEqOf elseExpr c then
       -- `elseExpr` holds by `True.intro`, by its hypothesis, or is `¬ c` or `false = b` for `c := true = b`
       let p := match hyp? with
         | some p => p
         | none =>
           if isNotExprOf elseExpr c then mkBVar 0
           else mkApp2 (mkConst ``Blaster.false_eq_of_not_true_eq) c.appArg! (mkBVar 0)
       absorbStep ``Blaster.dite'_else_true (mkApp (← mkPropNotOp) c) elseExpr p
       freeRewriteCacheReuse e 0
       toImpliesExpr t c (isThen := true) (isRestart := inDiteChoice)
     else return none

   @[always_inline, inline]
   isElseFalse? (elseExpr : Expr) (thenExpr : Expr) : TranslateEnvT (Option Expr) := do
     let hyp? ← isFalseHyp elseExpr
     if hyp?.isSome || exprEq c elseExpr then
       -- `¬ elseExpr` holds by `not_false`, by its hypothesis, or `elseExpr` is `c` itself
       let p := match hyp? with | some p => p | none => mkBVar 0
       let notC := mkApp (← mkPropNotOp) c
       freeRewriteCacheReuse e 0
       setRestart
       if thenExpr.hasLooseBVars then
         absorbStep ``Blaster.dite'_else_false notC elseExpr p
         let impExpr ← toImpliesExpr t c (isThen := true)
         mkApp2Expr (← mkPropAndOp) c impExpr
       else
         absorbStep ``Blaster.dite'_else_false_const notC elseExpr p
         freeRewriteCacheReuse t 0
         mkApp2Expr (← mkPropAndOp) c thenExpr
     else return none


/-- Given `a`, 't` and `e` the condition, then and else expressions for
    a Blaster.dite' expression,
     - When `t := sif h2 : c1 then e1 else e2` ∧
            `e := sif h3 : c2 then e1 else e2` ∧
            ¬ c1.hasLooseBVars ∧
            ¬ c2.hasLooseBVars
        - return `some $ sif h1 : (a ∧ c1) ∨ (¬ a ∧ c2) then e1 else e2`

     - When `t := sif h2 : c then e1 else e2` ∧
            `e := sif h2 : c then e1 else e3`
        - return `some $ sif h2 : c then e1 else (sif h1 : a then e2 else e3)`

     - When `t := sif h2 : c then e1 else e2` ∧
            `e := sif h2 : c then e3 else e2`
        - return `some $ sif h2 : c then (sif h1 : a then e1 else e3) else e2`

     - When `t := sif h2 : c then e1 else e2` ∧
            `e := sif h2 : c then e2 else e1`
        - return `some $ sif h3 : a = c then e1 else e2`
-/
def diteFactorize? (a : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
  match t, e with
  | Expr.lam n1 dc1 thn bi1, Expr.lam n2 dc2 els bi2 =>
      let some (sort1, c1, t1, e1) := dite'? thn | return none
      let some (_sort2, c2, t2, e2) := dite'? els | return none
      if exprEq t1 t2 then
        if exprEq e1 e2 then
          if !c1.hasLooseBVars && !c2.hasLooseBVars then
            setRestart
            let and_op ← mkPropAndOp
            let and_e1 ← mkApp2Expr and_op a c1
            let and_e2 ← mkApp2Expr and_op (← mkAppExpr (← mkPropNotOp) a) c2
            let or_e ← mkApp2Expr (← mkPropOrOp) and_e1 and_e2
            let hName ← Term.mkFreshBinderName
            let lam1 ← mkLambdaExpr hName BinderInfo.default or_e t1
            let lam2 ← mkLambdaExpr hName BinderInfo.default (← mkAppExpr (← mkPropNotOp) or_e) e1
            return ← mkApp4Expr (← mkBlasterDIteOp) sort1 or_e lam1 lam2
          else return none
      if exprEq c1 c2 then
        if exprEq t1 t2 then
          withLocalDecl' n1 bi1 dc1 fun n1' => do
            withLocalDecl' n2 bi2 dc2 fun n2' => do
              match ← instantiateShared1 e1 n1', ← instantiateShared1 e2 n2' with
              | Expr.lam x1 tc1 e1' bi1', Expr.lam _x2 _tc2 e2' _bi2' =>
                  setRestart
                  pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.dite'_factorize_thn [← diteLevel sort1]) sort1 a c1))
                  withLocalDecl' x1 bi1' tc1 fun x1' => do
                    let lam1 ← mkLambdaFVarsExpr #[n1'] (← instantiateShared1 e1' x1')
                    let lam2 ← mkLambdaFVarsExpr #[n2'] (← instantiateShared1 e2' x1')
                    let dite ← mkLambdaFVarsExpr #[x1'] (← mkApp4Expr (← mkBlasterDIteOp) sort1 a lam1 lam2)
                    return ← mkApp4Expr (← mkBlasterDIteOp) sort1 c1 t1 dite
              |_, _ => return none
        else if exprEq e1 e2 then
           withLocalDecl' n1 bi1 dc1 fun n1' => do
            withLocalDecl' n2 bi2 dc2 fun n2' => do
              match ← instantiateShared1 t1 n1', ← instantiateShared1 t2 n2' with
              | Expr.lam x1 tc1 t1' bi1', Expr.lam _x2 _tc2 t2' _bi2' =>
                  setRestart
                  pushProofStep (.rewrite (mkApp3 (mkConst ``Blaster.dite'_factorize_els [← diteLevel sort1]) sort1 a c1))
                  withLocalDecl' x1 bi1' tc1 fun x1' => do
                    let lam1 ← mkLambdaFVarsExpr #[n1'] (← instantiateShared1 t1' x1')
                    let lam2 ← mkLambdaFVarsExpr #[n2'] (← instantiateShared1 t2' x1')
                    let dite ← mkLambdaFVarsExpr #[x1'] (← mkApp4Expr (← mkBlasterDIteOp) sort1 a lam1 lam2)
                    return ← mkApp4Expr (← mkBlasterDIteOp) sort1 c1 dite e1
              |_, _ => return none
        else if exprEq t1 e2 && exprEq t2 e1 then
          setRestart
          let eq_cond ← mkApp3Expr (← mkEqOp) (← mkPropType) a c1
          let hName ← Term.mkFreshBinderName
          let lam1 ← mkLambdaExpr hName BinderInfo.default eq_cond t1
          let lam2 ← mkLambdaExpr hName BinderInfo.default (← mkAppExpr (← mkPropNotOp) eq_cond) e1
          return ← mkApp4Expr (← mkBlasterDIteOp) sort1 eq_cond lam1 lam2
        else return none
      else return none
  | _, _ => return none


/-- Given a `Solve.dite'` expression of the form `sif h : c then e1 else e2` apply the following constant
    propagation rule:

    - Let cst ← isCstIteMatch c
    - When cst.res ∧
           c := match₂ f₁, ..., fₚ with
                | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => t₁
                ...
                | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => tₘ
       Return
         `match₂ f₁, ..., fₚ with
          | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => sif h : t₁ then e1 else e2
          ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => sif h : tₘ then e1 else e2`

    - When cst.res ∧
           c := sif hₒ : a then t₁ else t₂
       Return
         `sif : h₀ : a then sif h : t₁ then e1 else e2 else sif h : t₂ then e1 else e2`

    Assume that `normChoiceApplication?` has already been applied.

-/
def constDITEPropagation? (f : Expr) (dargs : Array Expr) : TranslateEnvT (Option Expr) := do
  let c := dargs[1]!
  if !(← isCstIteMatch c).res then return none
  else
    let iteType := dargs[0]!
    let t := dargs[2]!
    let e := dargs[3]!
    let r ← pushDite? c iteType t e
    freeRewriteCacheReuse t 0
    freeRewriteCacheReuse e 0
    return r

  where
    @[always_inline, inline]
    pushDiteInLambda (iteType : Expr) (thn : Expr) (els : Expr) (rhs : Expr) : TranslateEnvT Expr := do
       -- NOTE: we can safely telescope as isCstPropMatch guarantees match/ite are not functions
       applyOnLambdaBody rhs (fun body => do
                                  match body with
                                  | Expr.const ``True _ => mkAppExpr thn (← mkTrueIntro)
                                  | Expr.const ``False _ => mkAppExpr els (← mkNotFalse)
                                  | _ => mkApp4Expr f iteType body thn els)

    @[always_inline, inline]
    pushDite? (m : Expr) (iteType : Expr) (thn : Expr) (els : Expr) : TranslateEnvT Expr := do
      if let some argInfo ← isMatcher? m.getAppFn then
        let mut pargs := m.getAppArgs
        for i in [argInfo.getFirstAltPos : argInfo.arity] do
          -- NOTE: No need to propagate reuse context as match name and discriminators have not changed
          pargs ← pargs.modifyM i (pushDiteInLambda iteType thn els)
        -- NOTE: we also need to set the return type for pulled over match to meet the Dite type.
        let idxType := argInfo.getFirstDiscrPos - 1
        pargs ← pargs.modifyM idxType (updateMatchReturnType argInfo pargs iteType)
        mkAppNExpr argInfo.nameExpr pargs
      else if let some (_psort, pcond, e1, e2) := dite'? m then
        let e1' ← pushDiteInLambda iteType thn els e1
        let e2' ← pushDiteInLambda iteType thn els e2
        -- NOTE: we need to propagate the reuse context to the new then and else expressions
        propagateReuseContext e1 e1' 0
        propagateReuseContext e2 e2' 0
        mkApp4Expr f iteType pcond e1' e2'
      else throwEnvError "constDITEPropagation: ite/match expected but got {reprStr m}"


/-- Apply the following simplification/normalization rules on `Solve.dite'` in the given order only when args.size ≥ 4:
     - sif h : True then e1 else e2 ==> applyExtraArgs e1   [proof: Blaster.dite'_true]

     - sif h : False then e1 else e2 ==> applyExtraArgs e2   [proof: Blaster.dite'_false]

     - sif h : c then e1 else e2 ==> applyExtraArgs (mkApp e1 h')   [proof: Blaster.dite'_reduce_pos]
           (if c := h' ∈ hypothesisContext.hypothesisMap)

     - sif h : c then e1 else e2 ==> applyExtraArgs (mkApp e2 h')
           (if ∃ e := h' ∈ hypothesisContext.hypothesisMap ∧ e = optimizeAdvancedNot (¬ c))
           [proof: Blaster.dite'_reduce_neg, on the proof of `¬ c` obtained from `h'`, see `notNormProof`]

     - sif h : c then e1 else e2 ==> r (if some r ← iteSimp? c e1 e2)

     - sif h : c then e1 else e2 ==> r (if some r ← constDITEPropagation? args)

     - sif h : c then e1 else e2 ==> (h : c → e1) ∧ (h : ¬ c → e2) (if Type(e1) = Prop)   [proof: Blaster.dite'_prop_eq]
         -- TO BE REMOVED: when performing normalization at the implication level

     - (sif h : c then e1 else e2) x₁ ... xₙ  ==> (sif h : c' then e2 else e1) x₁ ... xₙ (if c = ¬ c')   [proof: Blaster.dite'_not_swap]

     - (sif h : c then e1 else e2) x₁ ... xₙ ==> (sif h : true = c' then e2 else e1) x₁ ... xₙ (if c := false = c')   [proof: Blaster.dite'_bool_swap]

    with
      applyExtraArgs e :=
        if args.size > 4 then
          mkAppRangeExpr e 4 args.size args
        else e
    Note that this function is called only when dite conditional has been optimized,
    i.e., then and else terms still have to be optimized (see DiteChoiceWaitForCond logic in `optimizeStack`).

    Assume that f = Expr.const ``Blaster.dite'
    Assume that `normChoiceApplication` has already applied to push extra arguments in then/else expression.
-/
def optimizeDITEChoice (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 if args.size < 4 then return none
 -- args[0] is sort parameter
 -- args[1] is cond operand
 -- args[2] is then operand
 -- args[3] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let t := args[2]!
 let e := args[3]!
 if let some r ← condReduction? c t e then return r
 if let some r ← diteReduce? c t e ``Blaster.dite'_reduce_pos id then return r
 let notOp ← mkPropNotOp
 let notC ← optimizeAdvancedNot notOp #[c] (restart := false)
 if let some r ← diteReduce? notC e t ``Blaster.dite'_reduce_neg (notNormProof notOp c notC) then return r
 if let some r ← iteSimp? iteType c t e (inDiteChoice := true) then
    resetRestart
    return r
 if let some r ← constDITEPropagation? f args then return r
 if let some r ← diteToPropExpr? iteType c t e then return r
 isITESwap? f iteType c t e

 where

   @[always_inline, inline]
   condReduction? (c : Expr) (t : Expr) (e : Expr) : TranslateEnvT (Option Expr) := do
     match c with
     | Expr.const ``True _ =>
          -- `args[0]!` is the branch type
          pushProofStep (.rewrite (mkConst ``Blaster.dite'_true [← diteLevel args[0]!]))
          freeRewriteCacheReuse t 0
          freeRewriteCacheReuse e 0
          mkAppExpr t (← mkTrueIntro)
     | Expr.const ``False _ =>
          pushProofStep (.rewrite (mkConst ``Blaster.dite'_false [← diteLevel args[0]!]))
          freeRewriteCacheReuse t 0
          freeRewriteCacheReuse e 0
          mkAppExpr e (← mkNotFalse)
     | _ => return none

   /-- Given `cond` and `t` the condition and then/else expression for a Blaster.dite' expression,
       perform the following:
        - When `c := h' ∈ hypothesisContext.hypothesisMap`
            - return `some $ mkApp t h'`
        - Otherwise
            - return `none`
       `lemma` is the step's lemma (`Blaster.dite'_reduce_pos` or `Blaster.dite'_reduce_neg`),
       applied to the branch type, the condition `args[1]!` and `premise h'`, the proof of the
       lemma's premise (`c` or `¬ c`) obtained from the proof `h'` of `cond`.
   -/
   @[always_inline, inline]
   diteReduce? (cond : Expr) (t : Expr) (e : Expr) (lemma : Name) (premise : Expr → Expr) :
       TranslateEnvT (Option Expr) := do
     if let some p ← inHypMap cond
     then
       pushProofStep (.rewrite (mkApp3 (mkConst lemma [← diteLevel args[0]!]) args[0]! args[1]! (premise p)))
       freeRewriteCacheReuse t 0
       freeRewriteCacheReuse e 0
       mkAppExpr t p
     else return none

/-- Apply simplification/normalization rules on `Blaster.dite'` in the given order.
    Note that dependent ite is written with notation `if h : c then t else e`, which
    is now replaced with `Blaster.dite' c (fun h : c => t) (fun h : ¬ c => e)` to ignore
    the decidable instance. In the following simplification rules `Blaster.dite'`
    is annotated as `sif h : c then th else eh` to facilitate comprehension.

    The simplifcation/normalization rules applied are:
     - sif h : c then e1 else e2 ==> e1  (if e1 =ₚₜᵣ e2)  [proof: Blaster.dite'_abs]
     - sif h : c then True else False ===> c  [proof: Blaster.dite'_true_false]
     - sif h : c then False else True ===> ¬ c (restart)  [proof: Blaster.dite'_false_true]
     - sif h : c then True else p ===> h : ¬ c → p (restart)  [proof: Blaster.dite'_then_true]
     - sif h : c then False else p ===> ¬ c ∧ (h : ¬ c → p) (restart)  [proof: Blaster.dite'_then_false]
     - sif h : c then p else True ===> h : c → p  [proof: Blaster.dite'_else_true]
     - sif h : c then p else False ===> c ∧ (h : c → p) (restart)  [proof: Blaster.dite'_else_false]
     - sif h : c then c else p ===> h : ¬ c → p (restart)  [proof: Blaster.dite'_then_true]
     - sif h : c then p else c ===> c ∧ (h : c → p) (restart)  [proof: Blaster.dite'_else_false]
     - sif h : c then p else ¬ c ==> h : c → p  [proof: Blaster.dite'_else_true]
     - sif h : c then ¬ c else p ===> ¬ c ∧ (h : ¬ c → p) (restart)  [proof: Blaster.dite'_then_false]
       (see `iteSimp?` for all its cases and their proofs)
     - sif h : c then e1 else e2 ==> (h : c → e1) ∧ (h : ¬ c → e2) (if Type(e1) = Prop)
           [proof: Blaster.dite'_prop_eq, pushed by `diteToPropExpr?` in `optimizeDITEChoice`; nothing here]
         -- TO BE REMOVED: when performing normalization at the implication level
     - sif h1 : a then (sif h2 : c1 then e1 else e2) else (sif h3 : c2 then e1 else e2) ==>
          sif h1 : (a ∧ c1) ∨ (¬ a ∧ c2) then e1 else e2 (if ¬ c1.hasLooseBVars ∧ ¬ c2.hasLooseBVars)
        -- NOTE: rule is sound as h1, h2 and h3 can't be referenced in e1 and e2.

     - sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e1 else e3) ==>
          sif h2 : c then e1 else (sif h1 : a then e2 else e3)  [proof: Blaster.dite'_factorize_thn]
        -- NOTE: rule is sound as h1 can't be referenced in c and e1 but h1 and h2 can be referenced in e2 and e3.

     - sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e3 else e2) ==>
          sif h2 : c then (sif h1 : a then e1 else e3) else e2  [proof: Blaster.dite'_factorize_els]
        -- NOTE: rule is sound as h1 can't be referenced in c and e2 but h1 and h2 can be referenced in e1 and e3.

     - sif h1 : a then (sif h2 : c then e1 else e2) else (if h2 : c then e2 else e1) ==>
          sif h3 : a = c then e1 else e2
        -- NOTE: rule is sound as h1 and h2 can't be referenced in e1 and e2 and h1 can't be referenced in c.

    Assume that f = Expr.const ``Blaster.dite'
    An error is triggered when args.size ≠ 4 (i.e., only fully applied `dite'` expected at this stage)
-/
def optimizeDITE (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
 if args.size != 4 then throwEnvError "optimizeDITE: exactly four arguments expected"
 -- args[0] is sort parameter
 -- args[1] is cond operand
 -- args[2] is then operand
 -- args[3] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let t := args[2]!
 let e := args[3]!
 if let some r ← iteSimp? iteType c t e then return r
 if let some r ← diteFactorize? c t e then return r
 let ite' ← mkApp4Expr f iteType c t e
 let isCtor ← updateCtorCache ite' t e
 freeUnusedContext iteType t e isCtor
 return ite'

 where
   updateCtorCache (ite : Expr) (t : Expr) (e : Expr) : TranslateEnvT Bool := do
     let isCtorMatchPropCache := (← get).optEnv.memCache.isCtorMatchPropCache
     if isCtorMatchPropCache.contains t && isCtorMatchPropCache.contains e then
       updateCtorMatchPropCache ite
       return true
     else return false

   freeUnusedContext (iteType : Expr) (t : Expr) (e : Expr) (isCtor : Bool) : TranslateEnvT Unit := do
     if (← isCtorArg) || ((← isAppArg) && (isCtor || isBoolType iteType)) then return ()
     else
       -- erase context
       freeRewriteCacheReuse t 0
       freeRewriteCacheReuse e 0

end Blaster.Optimize
