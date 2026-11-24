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
 | .succ l' =>
      let r ← normLevel l'
      if levelEq r l' then return l else return .succ r
 | .max l1 l2 =>
      let r1 ← normLevel l1
      let r2 ← normLevel l2
      if levelEq r1 l1 && levelEq r2 l2 then return l else return .max r1 r2
 | .imax l1 l2 =>
      let r1 ← normLevel l1
      let r2 ← normLevel l2
      if levelEq r1 l1 && levelEq r2 l2 then return l else return .imax r1 r2
 | _ => return l -- case for .param and .zero

/-- Normalize each level in `xs`, returning `xs` itself (no reallocation)
    when no level changes — the common case when no level mvars are present. -/
partial def normLevels (xs : List Level) : TranslateEnvT (List Level) := do
  match xs with
  | [] => return xs
  | x :: rest =>
      let x' ← normLevel x
      let rest' ← normLevels rest
      if levelEq x' x && levelsEq rest' rest then return xs
      else return x' :: rest'

/-- Push the proof step of the application `f ras` when its head is unfolded or normalized.
    Called before `f` and its operands are optimized (an operand may still be the metavariable of
    a beta-reduced lambda), so the steps of `Nat.succ`, `Nat.pred` and `Nat.ble` are point-free.
    A repeated application hits the cache and gets no second step: the first one rewrites all its
    occurrences.
     - Nat.succ x ==> 1 + x    [proof: Blaster.nat_succ_equiv]
     - Nat.pred x ==> x - 1    [proof: Blaster.nat_pred_equiv]
     - Nat.le x y ==> ¬ (y < x)    [proof: Blaster.nat_le_eq_not_lt, once `Blaster.nat_le_eq_le` applied]
     - Nat.ble x y ==> Blaster.decide' (¬ y < x) (if isOptimizeRecCall)    [proof: Blaster.nat_ble_equiv]
     - Int.le x y ==> ¬ (y < x)    [proof: Blaster.int_le_eq_not_lt, once `Blaster.int_le_eq_le` applied]
     - Decidable.decide p ==> Blaster.decide' p    [proof: Blaster.decide'_equiv]
     - ite c t e ==> Blaster.dite' c (fun _ => t) (fun _ => e)    [proof: Blaster.ite_to_dite'_equiv]
     - dite c t e ==> Blaster.dite' c t e    [proof: Blaster.dite_equiv]
     - Int.sub x y ==> x + -y    [proof: Int.sub_eq_add_neg]
    `normConst` pushes the point-free steps of `Nat.le`, `Int.le` and `Nat.beq`, and of `Nat.succ`,
    `Nat.pred` and `Nat.ble` when unapplied; `pushUnfoldProofStep` those of other unfolded definitions.
    A head that is the metavariable of a beta-reduced lambda argument is read through its value.
-/
@[always_inline, inline]
def pushOpaqueFunProofStep (f : Expr) (ras : Array Expr) : TranslateEnvT Unit := do
  match f with
  | .const n us => pushConstStep n us ras
  | .mvar .. =>
      let v ← getEnvMVarValue f
      if let .const n us := v.getAppFn then pushConstStep n us (v.getAppArgs ++ ras)
  | _ => return ()

  where
   @[always_inline, inline]
   pushConstStep (n : Name) (us : List Level) (ras : Array Expr) : TranslateEnvT Unit := do
    match n with
    -- point-free steps, so no arity check
    | ``Nat.succ => pushProofStep (.rewrite (mkConst ``Blaster.nat_succ_equiv))
    | ``Nat.pred => pushProofStep (.rewrite (mkConst ``Blaster.nat_pred_equiv))
    -- the point-free step of `normConst` spells `Nat.le x y` as `x ≤ y`
    | ``Nat.le =>
        if ras.size == 2 then
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.nat_le_eq_not_lt) ras[0]! ras[1]!))
    | ``Nat.ble =>
        if (← isOptimizeRecCall) then
          pushProofStep (.rewrite (mkConst ``Blaster.nat_ble_equiv))
    -- the point-free step of `normConst` spells `Int.le x y` as `x ≤ y`
    | ``Int.le =>
        if ras.size == 2 then
          pushProofStep (.rewrite (mkApp2 (mkConst ``Blaster.int_le_eq_not_lt) ras[0]! ras[1]!))
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
         - return `λ x y => ¬ (y < x)`

     - When `n := Nat.ble` ∧ (← isOptimizeRecCall):
         - return `λ x y => decide' (¬ y < x)`

     - When `n := Nat.beq` ∧ (← isOptimizeRecCall):
         - return `λ x y => x == y`

     - When `n := Int.negSucc ∧ ¬ (← isInFunApp)`
         - return `λ n => Int.neg (Int.ofNat (1 + n))`

     - When `n := Int.le`
         - return `λ x y => ¬ (y < x)`

     - When `n := ite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) =>
                     Blaster.dite' α p (fun _ => t) (fun _ => e)`

     - When `n := dite`
         - return `λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) =>
                     Blaster.dite' α p t e`

     - When `n := Decidable.decide`
         - return `λ (p : Prop) [h : Decidable p] => Blaster.decide' p`

     - When `isCtorName n`
         - return `mkExpr e`

     - When `¬ (← isInFunApp):
         - When `¬ isNotFun e ∧ ¬ hasImplicitArgs e`:
             - When `isRecursiveFun n` (i.e., a recursive function passed as argument):
                 - return `(← normOpaqueAndRecFun e #[] )`
             - When `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n ∧ ¬ isNotFoldable e`:
                 - return `optimizer (← getFunBody e)`    [proof: unfold step, see `pushUnfoldProofStep`]

     - When `(← isInFunApp) ∧ ¬ isNotFun e ∧ ¬ isNotFoldable e ∧ ¬ hasImplicitArgs e ∧ (← getFunBody e).isSome`:
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
      match n with
      | ``Nat.zero => stackContinuity stack (← mkNatLitExpr 0)
      | _ =>
        if (← isPartialDef n) then throwEnvError "normConst: partial function not supported {n} !!!"
        if (← isUnsafeDef n) then throwEnvError "normConst: unsafe definition not supported {n} !!!"
        if let some r ← isToNormOpaqueFun n then return r
        let e' ← normConstLevel n l
        if (← isCtorName n) then return ← stackContinuity stack e'
        if let some r ← isHOF n e' then return r
        if (← isResolvableType e')
        then stackContinuity stack (← resolveTypeAbbrev e')
        else stackContinuity stack e'

  | _ => throwEnvError "normConst: name expression expected but got {reprStr e}"

  where
    /-- Normalizing level in Expr.const due to normalization perform on sort (see normSort in Basic) -/
    @[always_inline, inline]
    normConstLevel (n : Name) (xs : List Level) : TranslateEnvT Expr := do
      let ls ← normLevels xs
      -- reuse the original node when levels are unchanged (avoids allocating
      -- a fresh const just to probe the hash-cons cache)
      if levelsEq ls xs then mkExpr e else mkExpr (Expr.const n ls)

    /-- Push the point-free step `h` of an opaque function passed as an argument, e.g. `List.map Nat.succ xs`:
        as the head of an application it gets its step from `pushOpaqueFunProofStep`. -/
    @[always_inline, inline]
    pushUnappliedStep (h : Expr) : TranslateEnvT Unit := do
      unless (← isInFunApp) do pushProofStep (.rewrite h)

    /-- Apply the following normalization rules on opaque functions:
         - Nat.pred ==> λ n => n - 1    [proof: Blaster.nat_pred_equiv]
         - Nat.succ ==> λ n => 1 + n    [proof: Blaster.nat_succ_equiv]
         - Nat.le ==> λ x y => ¬ (y < x)
             [proof: Blaster.nat_le_eq_le, then Blaster.nat_le_eq_not_lt, see `pushOpaqueFunProofStep`]
         - Nat.ble ==> λ x y => Blaster.decide' (¬ y < x) (if isOptimizeRecCall)
             [proof: Blaster.nat_ble_equiv]
         - Nat.beq ==> λ x y => x == y (if isOptimizeRecCall)    [proof: Blaster.nat_beq_eq_beq]
         - Int.negSucc ==> λ n => Int.neg (Int.ofNat (1 + n)) (if ¬ isInFunApp)
         - Int.le ==> λ x y => ¬ (y < x)
             [proof: Blaster.int_le_eq_le, then Blaster.int_le_eq_not_lt, see `pushOpaqueFunProofStep`]
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
           pushUnappliedStep (mkConst ``Blaster.nat_pred_equiv)
           let body ← mkApp2Expr (← mkNatSubOp) (← mkBVarExpr 0) (← mkNatLitExpr 1)
           let lam ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           stackContinuity stack lam

     | ``Nat.succ =>
           pushUnappliedStep (mkConst ``Blaster.nat_succ_equiv)
           let body ← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr 1) (← mkBVarExpr 0)
           let lam ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
           stackContinuity stack lam

     | ``Nat.le =>
          pushProofStep (.rewrite (mkConst ``Blaster.nat_le_eq_le))
          let ltExpr ← mkApp2Expr (← mkNatLtOp) (← mkBVarExpr 0) (← mkBVarExpr 1)
          let notExpr ← mkAppExpr (← mkPropNotOp) ltExpr
          let lam1 ← mkLambdaExpr `y BinderInfo.default (← mkNatType) notExpr
          let lam2 ← mkLambdaExpr `x BinderInfo.default (← mkNatType) lam1
          stackContinuity stack lam2

     | ``Nat.ble =>
           if (← isOptimizeRecCall) then
             pushUnappliedStep (mkConst ``Blaster.nat_ble_equiv)
             let leExpr ← mkAppExpr (← mkPropNotOp) (← mkApp2Expr (← mkNatLtOp) (← mkBVarExpr 0) (← mkBVarExpr 1))
             let body ← mkAppExpr (← mkBlasterDecideConst) leExpr
             let lam1 ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             stackContinuity stack lam2
           else stackContinuity stack (skipCache := true) e -- don't catch

     | ``Nat.beq =>
           if (← isOptimizeRecCall) then
             pushProofStep (.rewrite (mkConst ``Blaster.nat_beq_eq_beq))
             let body ← mkApp2Expr (← mkNatBEqOp) (← mkBVarExpr 1) (← mkBVarExpr 0)
             let lam1 ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
             let lam2 ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) lam1
             stackContinuity stack lam2
           else stackContinuity stack (skipCache := true) e -- don't catch

     | ``Int.negSucc =>
             if !(← isInFunApp) then
               let addExpr ← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr 1) (← mkBVarExpr 0)
               let intExpr ← mkAppExpr (← mkIntOfNat) addExpr
               let body ← mkAppExpr (← mkIntNegOp) intExpr
               let lam ← mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default (← mkNatType) body
               stackContinuity stack (skipCache := true) lam -- don't catch
             else stackContinuity stack (skipCache := true) (← mkIntNegSucc) -- don't catch

     | ``Int.le =>
          pushProofStep (.rewrite (mkConst ``Blaster.int_le_eq_le))
          let ltExpr ← mkIntLtExpr (← mkBVarExpr 0) (← mkBVarExpr 1)
          let notExpr ← mkAppExpr (← mkPropNotOp) ltExpr
          let lam1 ← mkLambdaExpr `y BinderInfo.default (← mkIntType) notExpr
          let lam2 ← mkLambdaExpr `x BinderInfo.default (← mkIntType) lam1
          stackContinuity stack lam2

     | ``ite =>
          let hName ← Term.mkFreshBinderName
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let thenExpr ← mkLambdaExpr hName BinderInfo.default xs[1]! xs[3]!
            let notCond ← mkAppExpr (← mkPropNotOp) xs[1]!
            let elseExpr ← mkLambdaExpr hName BinderInfo.default notCond xs[4]!
            let appExpr ← mkApp4Expr (← mkBlasterDIteOp) xs[0]! xs[1]! thenExpr elseExpr
            let lam ← mkLambdaFVarsExpr xs appExpr
            stackContinuity stack lam

     | ``dite =>
         forallTelescope (← inferTypeEnv e) fun xs _ => do
           let appExpr ← mkApp4Expr (← mkBlasterDIteOp) xs[0]! xs[1]! xs[3]! xs[4]!
           let lam ← mkLambdaFVarsExpr xs appExpr
           stackContinuity stack lam

     | ``Decidable.decide =>
          forallTelescope (← inferTypeEnv e) fun xs _ => do
            let appExpr ← mkAppExpr (← mkBlasterDecideConst) xs[0]!
            let lam ← mkLambdaFVarsExpr xs appExpr
            stackContinuity stack lam

     | _ => return none

    @[always_inline, inline]
    isHOF (f : Name) (e : Expr) : TranslateEnvT (Option OptimizeContinuity) := do
      if (← isNotFun e) then return none
      if (← hasImplicitArgs e) then return none
      if (← isInFunApp) then
        if (← isNotFoldable e #[]) then return none
        if let some fbody ← getFunBody e then
          pushUnfoldProofStep e
          -- don't catch we may not optimize lambda body when e appear as an parameter afterwards
          stackContinuity stack (skipCache := true) fbody
        else return none
      else
        if (← isRecursiveFun f) then
          return (some $ ← normRecFun e #[] e stack)
        if (← isNotFoldable e #[]) then return none
        -- non recursive function case
        if let some fbody ← getFunBody e then
          pushUnfoldProofStep e
          return (some $ Sum.inl $ .InitOptimizeExpr fbody :: stack)
        else return none

/-- Given a ctor application `C x₁ ... xₙ`,
     - When numParams(C) + numFields(C) ≤ n (i.e., fully applied Ctor)
          - return none
     - Otherwise:
         - When numParams(C) == n (i.e., only implicit arguments provided)
            - return none
         - Otherwise:
             - return `etaExpand (mkAppN f args)`
-/
def normPartialCtorApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  let ConstantInfo.ctorInfo info ← getConstEnvInfo n | return none
  if info.numParams + info.numFields ≤ args.size then return none
  if info.numParams == args.size then return none -- only implicit arguments provided
  etaExpand (← mkAppNExpr f args)

/-- Given a ctor application `C x₁ ... xₙ`,
      - try to normalize partially applied Ctor and add result on continuation stack
      - try to apply ctor normalization
         - When restart flag is set:
             - add optimized application on continuation stack
         - Otherwise:
             - proceed with stack continuity
-/
def optimizeConstApp (f : Expr) (args : Array Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  if let some r ← normPartialCtorApp? f args then return Sum.inl (.InitOptimizeExpr r :: stack)
  let e ← applyConstAppRules f args
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else stackContinuity stack e

  where
    applyConstAppRules (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
      match f with
      | Expr.const ``Int.negSucc _ => optimizeIntNegSucc f args
      | Expr.const ``String.mk _ => normStringValue f args
      | _ => mkAppNExpr f args

end Blaster.Optimize
