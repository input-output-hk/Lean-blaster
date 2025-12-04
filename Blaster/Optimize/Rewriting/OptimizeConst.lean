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
                 - return `optimizer (← getFunBody e)`

     - When `(← isInFunApp) ∧ ¬ isNotFoldable e ∧ ¬ hasImplicitArgs e ∧ (← getFunBody e).isSome`:
          - return `← getFunBody e`

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
         - Nat.pred ==> λ n => n - 1
         - Nat.succ ==> λ n => 1 + n
         - Nat.le ==> ≤
         - Nat.ble ==> λ x y => Blaster.decide' (x ≤ y) (if isOptimizeRecCall)
         - Nat.beq ==> λ x y => x == y (if isOptimizeRecCall)
         - Int.negSucc ==> λ n => Int.neg (Int.ofNat (1 + n)) (if ¬ isInFunApp)
         - Int.le ==> ≤
         - ite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t e : α) => Blaster.dite' α p (fun _ => t) (fun _ => e)
         - dite ==> λ (α : Sort u) (p : Prop) [h : Decidable p] (t : p → α) (e : ¬ p → α) => Blaster.dite' α p t e
         - Decidable.decide ==> λ (p : Prop) [h : Decidable p] => Blaster.decide' p
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

     | ``Int.le => stackContinuity stack (← mkIntLeOp)

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
          stackContinuity stack (skipCache := true) fbody -- don't catch
        else return none
      else
        if (← hasImplicitArgs e) then return none
        if (← isRecursiveFun f) then
          return (some $ Sum.inl $ .InitOpaqueRecExpr e #[] :: stack)
        if (← isNotFoldable e #[]) then return none
        -- non recursive function case
        if let some fbody ← getFunBody e then
          return (some $ Sum.inl $ .InitOptimizeExpr fbody :: stack)
        else return none

end Blaster.Optimize
