import Lean
import Blaster.Optimize.Rewriting.OptimizeApp

open Lean Meta Elab

namespace Blaster.Optimize

/-- Perform the following normalization on `l`
    - When `l := .mvar m`
       - When `some l := getLevelMVarAssignmentExp (← getMCtx) m`
          - return l
       - Otherwise
          - return ⊥
    - When `l := .succ l'`
        - return .succ (← normLevel l')
    - When `l := .max l1 l2`
        - return .max (← normLevel l1) (← normLevel l2)
    - When `l := .imax l1 l2`
        - return .imax (← normLevel l1) (← normLevel l2)
    - Otherwise
        - return `l`
-/
partial def normLevel (l : Level) : TranslateEnvT Level := do
 match l with
 | .mvar m =>
      let some l := getLevelMVarAssignmentExp (← getMCtx) m
        | throwEnvError "normLevel: level assignment expected for meta variables {reprStr m}"
      normLevel l
 | .succ l' => return .succ (← normLevel l')
 | .max l1 l2 => return .max (← normLevel l1) (← normLevel l2)
 | .imax l1 l2 => return .imax (← normLevel l1) (← normLevel l2)
 | _ => return l -- case for .param and .zero

/-- Push the proof step of the application `f ras` when its head is unfolded or normalized.
    Called before `f` is optimized, since the normalization of `f` is cached.
    Repeated identical applications hit the application cache and get a single step,
    which rewrites all their occurrences at once.
     - Nat.succ x ==> 1 + x    [proof: Nat.succ_eq_one_add]
     - Nat.pred x ==> x - 1    [proof: Nat.pred_eq_sub_one]
     - Nat.ble x y ==> Blaster.decide' (x ≤ y) (if isOptimizeRecCall)    [proof: Blaster.nat_ble_eq_decide']
     - Decidable.decide p ==> Blaster.decide' p    [proof: Blaster.decide'_equiv]
     - ite c t e ==> Blaster.dite' c (fun _ => t) (fun _ => e)    [proof: Blaster.ite_to_dite'_equiv]
     - dite c t e ==> Blaster.dite' c t e    [proof: Blaster.dite_equiv]
     - Int.sub x y ==> x + -y    [proof: Int.sub_eq_add_neg]
    `Int.le` pushes its point-free step in the `isToNormOpaqueFun` arm of `normConst`.
    Other non-recursive definitions get an unfold step where they are unfolded (see `pushUnfoldProofStep`).
-/
@[always_inline, inline]
def pushOpaqueFunProofStep (f : Expr) (ras : Array Expr) : TranslateEnvT Unit := do
  let Expr.const n us := f | return ()
  match n with
  | ``Nat.succ =>
      if ras.size == 1 then
        pushProofStep (.rewrite (mkApp (mkConst ``Nat.succ_eq_one_add) ras[0]!))
  | ``Nat.pred =>
      if ras.size == 1 then
        pushProofStep (.rewrite (mkApp (mkConst ``Nat.pred_eq_sub_one) ras[0]!))
  | ``Nat.ble =>
      if ras.size == 2 then
        if (← isOptimizeRecCall) then
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_ble_eq_decide') ras[0]! ras[1]!))
  | ``Decidable.decide =>
      if ras.size == 2 then
        pushProofStep (.rewrite (mkConst ``Blaster.decide'_equiv))
  -- point-free steps, so no arity check
  | ``ite => pushProofStep (.rewrite (mkConst ``Blaster.ite_to_dite'_equiv us))
  | ``dite => pushProofStep (.rewrite (mkConst ``Blaster.dite_equiv us))
  | ``Int.sub =>
      -- not an unfold step since the goal shows `HSub.hSub`, whose instance hides `Int.sub`
      -- pushed bare since the operands may carry optimizer-local fvars under binders
      if ras.size == 2 then
        pushProofStep (.rewrite (mkConst ``Int.sub_eq_add_neg))
  | _ => return ()

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - When `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`

     - When `n := Nat.pred`
         - return `λ n => n - 1`

     - When `n := Nat.succ`
         - return `λ n => 1 + n`

     - When `n := Nat.le`
         - return `mkNatLeOp`

     - When `n := Nat.ble` ∧ (← isOptimizeRecCall):
         - return `λ x y => decide' (x ≤ y)`

     - When `n := Nat.beq` ∧ (← isOptimizeRecCall):
         - return `λ x y => x == y`

     - When `n := Int.negSucc ∧ ¬ (← isInFunApp)`
         - return `λ n => Int.neg (Int.ofNat (1 + n))`

     - When `n := Int.le`
         - return `mkIntLeOp`

     - When `n := ite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) =>
                     Blaster.dite' α p (fun _ => t) (fun _ => e)`

     - When `n := dite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) =>
                     Blaster.dite' α p t e`

     - When `n := Decidable.decide`
         - return `λ (p : Prop) [h : Decidable p] => Blaster.decide' p`

     - When `¬ (← isInFunApp):
         - When `¬ hasImplicitArgs e`:
             - When `isRecursiveFun n` (i.e., a recursive function passed as argument):
                 - return `(← normOpaqueAndRecFun e #[] optimizer)`
             - When `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n ∧ ¬ isNotFoldable e`:
                 - return `optimizer (← getFunBody e)`    [proof: unfold step, see `pushUnfoldProofStep`]

     - When `(← isInFunApp) ∧ ¬ isNotFoldable e ∧ ¬ hasImplicitArgs e ∧ (← getFunBody e).isSome`:
          - return `← getFunBody e`    [proof: unfold step, see `pushUnfoldProofStep`]

     - Otherwise:
         - When `isResolvebleType e` :
             - return `mkExpr (← resolveTypeAbbrev e)`
         - Otherwise
             - return `mkExpr e`
-/
def normConst (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  match e with
  | Expr.const n l =>
       withLocalContext $ do
         match n with
         | ``Nat.zero => stackContinuity stack (← mkNatLitExpr 0)
         | _ =>
           if (← isPartialDef n) then throwEnvError "normConst: partial function not supported {n} !!!"
           if (← isUnsafeDef n) then throwEnvError "normConst: unsafe definition not supported {n} !!!"
           if let some r ← isToNormOpaqueFun n then return r
           let e' ← normConstLevel n l
           if let some r ← isHOF n e' then return r
           if (← isResolvableType e')
           then stackContinuity stack (← mkExpr (← resolveTypeAbbrev e'))
           else stackContinuity stack (← mkExpr e')

  | _ => throwEnvError "normConst: name expression expected but got {reprStr e}"

  where
    /-- Normalizing level in Expr.const due to normalization perform on sort (see normSort in Basic) -/
    @[always_inline, inline]
    normConstLevel (n : Name) (xs : List Level) : TranslateEnvT Expr := do
      return Expr.const n (← xs.mapM normLevel)

    /-- Apply the following normalization rules on opaque functions:
         - Nat.pred ==> λ n => n - 1    [proof: Nat.pred_eq_sub_one, see `pushOpaqueFunProofStep`]
         - Nat.succ ==> λ n => 1 + n    [proof: Nat.succ_eq_one_add, see `pushOpaqueFunProofStep`]
         - Nat.le ==> ≤
         - Nat.ble ==> λ x y => Blaster.decide' (x ≤ y) (if isOptimizeRecCall)
             [proof: Blaster.nat_ble_eq_decide', see `pushOpaqueFunProofStep`]
         - Nat.beq ==> λ x y => x == y (if isOptimizeRecCall)
         - Int.negSucc ==> λ n => Int.neg (Int.ofNat (1 + n)) (if ¬ isInFunApp)
         - Int.le ==> ≤    [proof: Blaster.int_le_eq_le]
         - ite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) => Blaster.dite' α p (fun _ => t) (fun _ => e)
             [proof: Blaster.ite_to_dite'_equiv, see `pushOpaqueFunProofStep`]
         - dite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) => Blaster.dite' α p t e
             [proof: Blaster.dite_equiv, see `pushOpaqueFunProofStep`]
         - Decidable.decide ==> λ (p : Prop) [h : Decidable p] => Blaster.decide' p
             [proof: Blaster.decide'_equiv, see `pushOpaqueFunProofStep`]
    -/
    @[always_inline, inline]
    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option OptimizeContinuity) := do
     match n with
     | ``Nat.pred =>
           let body ← mkExpr $ mkApp2 (← mkNatSubOp) (mkBVar 0) (← mkNatLitExpr 1)
           let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           stackContinuity stack (← mkExpr lam)

     | ``Nat.succ =>
           let body ← mkExpr $ mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) (mkBVar 0)
           let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           stackContinuity stack (← mkExpr lam)

     | ``Nat.le => stackContinuity stack (← mkNatLeOp)

     | ``Nat.ble =>
           if (← isOptimizeRecCall) then
             let leExpr ← mkExpr $ mkApp2 (← mkNatLeOp) (mkBVar 1) (mkBVar 0)
             let body ← mkExpr $ mkApp (← mkBlasterDecideConst) leExpr
             let lam1 ← mkExpr $ mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             stackContinuity stack (← mkExpr lam2)
           else stackContinuity stack (skipCache := true) e -- don't catch

     | ``Nat.beq =>
           if (← isOptimizeRecCall) then
             let body ← mkExpr $ mkApp2 (← mkNatBEqOp) (mkBVar 1) (mkBVar 0)
             let lam1 ← mkExpr $ mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             stackContinuity stack (← mkExpr lam2)
           else stackContinuity stack (skipCache := true) e -- don't catch

     | ``Int.negSucc =>
             if !(← isInFunApp) then
               let addExpr ← mkExpr $ mkApp2 (← mkNatAddOp) (← mkNatLitExpr 1) (mkBVar 0)
               let intExpr ← mkExpr $ mkApp (← mkIntOfNat) addExpr
               let body ← mkExpr $ mkApp (← mkIntNegOp) intExpr
               let lam := mkLambda (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
               stackContinuity stack (skipCache := true) (← mkExpr lam) -- don't catch
             else stackContinuity stack (skipCache := true) e -- don't catch

     | ``Int.le =>
             pushProofStep (.rewrite (mkConst ``Blaster.int_le_eq_le))
             stackContinuity stack (← mkIntLeOp)

     | ``ite =>
          let hName ← Term.mkFreshBinderName
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let thenExpr ← mkExpr $ mkLambda hName BinderInfo.default xs[1]! xs[3]!
            let notCond ← mkExpr $ mkApp (← mkPropNotOp) xs[1]!
            let elseExpr ← mkExpr $ mkLambda hName BinderInfo.default notCond xs[4]!
            let appExpr ← mkExpr $ mkApp4 (← mkBlasterDIteOp) xs[0]! xs[1]! thenExpr elseExpr
            let lam ← mkLambdaFVars xs appExpr
            stackContinuity stack (← mkExpr lam)

     | ``dite =>
         forallTelescope (← inferTypeEnv e) fun xs _ => do
           let appExpr ← mkExpr $ mkApp4 (← mkBlasterDIteOp) xs[0]! xs[1]! xs[3]! xs[4]!
           let lam ← mkLambdaFVars xs appExpr
           stackContinuity stack (← mkExpr lam)

     | ``Decidable.decide =>
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let appExpr ← mkExpr $ mkApp (← mkBlasterDecideConst) xs[0]!
            let lam ← mkLambdaFVars xs appExpr
            stackContinuity stack (← mkExpr lam)

     | _ => return none

    @[always_inline, inline]
    isHOF (f : Name) (e : Expr) : TranslateEnvT (Option OptimizeContinuity) := do
      if (← isInFunApp) then
        if (← hasImplicitArgs e) then return none
        if (← isNotFoldable e #[]) then return none
        if let some fbody ← getFunBody e then
          pushUnfoldProofStep e
          stackContinuity stack (skipCache := true) fbody -- don't catch
        else return none
      else
        if (← hasImplicitArgs e) then return none
        if (← isRecursiveFun f) then
          return (some $ Sum.inl $ .InitOpaqueRecExpr e #[] :: stack)
        if (← isNotFoldable e #[]) then return none
        -- non recursive function case
        if let some fbody ← getFunBody e then
          pushUnfoldProofStep e
          return (some $ Sum.inl $ .InitOptimizeExpr fbody :: stack)
        else return none

end Blaster.Optimize
