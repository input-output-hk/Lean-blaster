import Lean
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Meta Elab
namespace Blaster.Optimize

/-- Given `thn` and `els` corresponding respectively to the `then` and `else` terms
    of a `Blaster.dite'` expression, perform the following normalization rules:
      - When `Type(t) = Prop ∧ t := fun h : c => e1 ∧ e := fun h : ¬ c => e2`
          - return `(h : c → e1) ∧ (h : ¬ c → e2)`
      - When `Type(t) = Prop ∧ t := c → Prop ∧ e := ¬ c → Prop`
          - return `(h : c → t h) ∧ (h : ¬ c → e h)`
      - When `Type(t) ≠ Prop:
          - return `none`
      - Otherwise
           - return ⊥
-/
def diteToPropExpr? (iteType: Expr) (cond : Expr) (thn : Expr) (els : Expr) : TranslateEnvT (Option Expr) := do
  if !iteType.isProp then return none
  let leftAnd ← toImpliesExpr thn cond
  let rightAnd ← toImpliesExpr els (mkApp (← mkPropNotOp) cond)
  return mkApp2 (← mkPropAndOp) leftAnd rightAnd

  where
    toImpliesExpr (ite : Expr) (c : Expr) : TranslateEnvT Expr := do
     match ite with
     | Expr.lam n t b bi => return mkForall n bi t b
     | _ =>
         if !(← isQuantifiedFun ite) then
            throwEnvError "diteToPropExpr? : lambda/quantified function expected but got {reprStr ite}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun x : cond => ite x`
           withLocalDecl' (← Term.mkFreshBinderName) BinderInfo.default c fun x => do
             mkForallFVars #[x] (ite.beta #[x])


/-- Return `some (true = c')` only when `c := false = c'`.
    This function also checks if `true = c'` is already in cache.
    Otherwise `none`.
-/
def isITEBoolSwap? (c : Expr) : TranslateEnvT (Option Expr) := do
  match eq? c with
  | some (eq_sort, Expr.const ``false _, op2) =>
      mkExpr (mkApp3 c.getAppFn eq_sort (← mkBoolTrue) op2)
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

/-- Given an Blaster.dite' expression:
      - return `some sif h : c' then e2 else e1` when `c := ¬ c'`
      - return `some sif h : true = c' then e2 else e1` when `c := false = c'`
    Otherwise none.

-/
def isITESwap? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let c := args[1]!
 if let Expr.app (Expr.const ``Not _) ne := c then
    return mkAppN f ((args.set! 1 ne).swapIfInBounds 2 3)
 if let some c' ← (isITEBoolSwap? c) then
    return mkAppN f ((args.set! 1 c').swapIfInBounds 2 3)
 return none

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
            let and_e1 := mkApp2 and_op a c1
            let and_e2 := mkApp2 and_op (mkApp (← mkPropNotOp) a) c2
            let or_e := mkApp2 (← mkPropOrOp) and_e1 and_e2
            let hName ← Term.mkFreshBinderName
            let lam1 := mkLambda hName BinderInfo.default or_e t1
            let lam2 := mkLambda hName BinderInfo.default (mkApp (← mkPropNotOp) or_e) e1
            return mkApp4 (← mkBlasterDIteOp) sort1 or_e lam1 lam2
          else return none
      if exprEq c1 c2 then
        if exprEq t1 t2 then
          withLocalDecl' n1 bi1 dc1 fun n1' => do
            withLocalDecl' n2 bi2 dc2 fun n2' => do
              match instantiate1' e1 n1', instantiate1' e2 n2' with
              | Expr.lam x1 tc1 e1' bi1', Expr.lam _x2 _tc2 e2' _bi2' =>
                  setRestart
                  withLocalDecl' x1 bi1' tc1 fun x1' => do
                    let lam1 ← mkLambdaFVar n1' (instantiate1' e1' x1')
                    let lam2 ← mkLambdaFVar n2' (instantiate1' e2' x1')
                    let dite ← mkLambdaFVar x1' (mkApp4 (← mkBlasterDIteOp) sort1 a lam1 lam2)
                    return mkApp4 (← mkBlasterDIteOp) sort1 c1 t1 dite
              |_, _ => return none
        else if exprEq e1 e2 then
           withLocalDecl' n1 bi1 dc1 fun n1' => do
            withLocalDecl' n2 bi2 dc2 fun n2' => do
              match instantiate1' t1 n1', instantiate1' t2 n2' with
              | Expr.lam x1 tc1 t1' bi1', Expr.lam _x2 _tc2 t2' _bi2' =>
                  setRestart
                  withLocalDecl' x1 bi1' tc1 fun x1' => do
                    let lam1 ← mkLambdaFVar n1' (instantiate1' t1' x1')
                    let lam2 ← mkLambdaFVar n2' (instantiate1' t2' x1')
                    let dite ← mkLambdaFVar x1' (mkApp4 (← mkBlasterDIteOp) sort1 a lam1 lam2)
                    return mkApp4 (← mkBlasterDIteOp) sort1 c1 dite e1
              |_, _ => return none
        else if exprEq t1 e2 && exprEq t2 e1 then
          setRestart
          let eq_cond := mkApp3 (← mkEqOp) (← mkPropType) a c1
          let hName ← Term.mkFreshBinderName
          let lam1 := mkLambda hName BinderInfo.default eq_cond t1
          let lam2 := mkLambda hName BinderInfo.default (mkApp (← mkPropNotOp) eq_cond) e1
          return mkApp4 (← mkBlasterDIteOp) sort1 eq_cond lam1 lam2
        else return none
      else return none
  | _, _ => return none

/-- Apply the following simplification/normalization rules on `Solve.dite'` in the given order only when args.size ≥ 4:
     - sif h : True then e1 else e2 ==> applyExtraArgs e1 -- TODO: consider proof reconstruction

     - sif h : False then e1 else e2 ==> applyExtraArgs e2 -- TODO: consider proof reconstruction

     - sif h : c then e1 else e2 ==> applyExtraArgs e1
           (if c := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e1.hasLooseBVars)

     - sif h : c then e1 else e2 ==> applyExtraArgs e2
           (if ∃ e := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e2.hasLooseBVars ∧ e = ¬ c )

     - sif h : c then e1 else e2 ==> applyExtraArgs e1[h/h']
           (if c := h' ∈ hypothesisContext.hypothesisMap ∧ e1.hasLooseBVars)

     - sif h : c then e1 else e2 ==> applyExtraArgs e2[h/h']
          (if ∃ e := h' ∈ hypothesisContext.hypothesisMap ∧ e2.hasLooseBVars ∧ e = ¬ c)

     - sif h : c then e1 else e2 ==> (h : c → e1) ∧ (h : ¬ c → e2) (if Type(e1) = Prop)
         -- TO BE REMOVED: when performing normalization at the implication level

     - (sif h : c then e1 else e2) x₁ ... xₙ  ==> (sif h : c' then e2 else e1) x₁ ... xₙ (if c = ¬ c')

     - (sif h : c then e1 else e2) x₁ ... xₙ ==> (sif h : true = c' then e2 else e1) x₁ ... xₙ (if c := false = c')

    with
      applyExtraArgs e :=
        if args.size > 4 then
          let extra_args := args.extract 4 args.size
          mkAppN e extra_args
        else e
    Note that this function is called only when dite conditional has been optimized,
    i.e., then and else terms still have to be optimized (see DiteChoiceWaitForCond logic in `optimizeStack`).

    Assume that f = Expr.const ``Blaster.dite'
-/
def optimizeDITEChoice (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if args.size < 4 then return none
 -- args[0] is sort parameter
 -- args[1] is cond operand
 -- args[2] is then operand
 -- args[3] is else operand
 let iteType := args[0]!
 let c := args[1]!
 let t := args[2]!
 let e := args[3]!
 if let Expr.const ``True _ := c then return applyExtraArgs (betaLambda t #[← mkTrueIntro])
 if let Expr.const ``False _ := c then return applyExtraArgs (betaLambda e #[← mkNotFalse])
 if let some r ← diteReduce? c t then return applyExtraArgs r
 if let some r ← diteReduce? (← optimizeNot (← mkPropNotOp) #[c] (cacheResult := false)) e then
   return applyExtraArgs r
 if let some r ← diteToPropExpr? iteType c t e then return r
 isITESwap? f args

 where
   @[always_inline, inline]
   applyExtraArgs (e : Expr) : Expr :=
     if args.size > 4 then
       let extra_args := args.extract 4 args.size
       mkAppN e extra_args
     else e

   /-- Given `cond` and `t` the condition and then/else expression for a Blaster.dite' expression,
       perform the following:
        - When `t := fun h : c => e ∧ c := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ e.hasLooseBVars`
            - return `some e`
        - When `t := fun h : c => e ∧ c := h' ∈ hypothesisContext.hypothesisMap ∧ e.hasLooseBVars`
            - return `some e[h/h']`
        - When `t := c → α ∧ c := h ∈ hypothesisContext.hypothesisMap`
            - return `some t h`
        - Otherwise
            - return `none`
   -/
   diteReduce? (cond : Expr) (t : Expr) : TranslateEnvT (Option Expr) := do
     let hyps := (← get).optEnv.hypothesisContext.hypothesisMap
     match t with
     | Expr.lam _h _c b _bi =>
         if let some p ← inHypMap cond hyps then
            if !b.hasLooseBVars
            then return b
            else return (t.beta #[p])
         else return none
     | _ =>
        if !(← isQuantifiedFun t) then
          throwEnvError "diteReduce?: lambda/quantified function expression expected but got {reprStr t}"
        if let some p ← inHypMap cond hyps
        then return (t.beta #[p])
        else return none

/-- Apply simplification/normalization rules on `Blaster.dite'` in the given order.
    Note that dependent ite is written with notation `if h : c then t else e`, which
    is now replaced with `Blaster.dite' c (fun h : c => t) (fun h : ¬ c => e)` to ignore
    the decidable instance. In the following simplification rules `Blaster.dite'`
    is annotated as `sif h : c then th else eh` to facilitate comprehension.

    The simplifcation/normalization rules applied are:
     - sif h : c then e1 else e2 ==> e1  (if e1 =ₚₜᵣ e2)

     - sif h1 : a then (sif h2 : c1 then e1 else e2) else (sif h3 : c2 then e1 else e2) ==>
          sif h1 : (a ∧ c1) ∨ (¬ a ∧ c2) then e1 else e2 (if ¬ c1.hasLooseBVars ∧ ¬ c2.hasLooseBVars)
        -- NOTE: rule is sound as h1, h2 and h3 can't be referenced in e1 and e2.

     - sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e1 else e3) ==>
          sif h2 : c then e1 else (sif h1 : a then e2 else e3)
        -- NOTE: rule is sound as h1 can't be referenced in c and e1 but h1 and h2 can be referenced in e2 and e3.

     - sif h1 : a then (sif h2 : c then e1 else e2) else (sif h2 : c then e3 else e2) ==>
          sif h2 : c then (sif h1 : a then e1 else e3) else e2
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
 let thenExpr ← extractDependentITEExpr t
 let elseExpr ← extractDependentITEExpr e
 if exprEq thenExpr elseExpr then return betaLambda t #[← mkOfDecideEqProof c true]
 if let some r ← diteFactorize? c t e then return r
 return mkApp4 f iteType c t e

end Blaster.Optimize
