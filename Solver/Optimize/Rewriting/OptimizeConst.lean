import Lean
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta Elab

namespace Solver.Optimize

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - When `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - When `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - When `n := Nat.pred`
         - return `λ n => n - 1`
     - When `n := Nat.succ`
         - return `λ n => 1 + n`
     - When `n := Nat.le`
         - return `mkNatLeOp`
     - When `n := Nat.ble` ∧ (← isOptimizeRecCall):
         - return `λ x y => decide (x ≤ y)`
     - When `n := Nat.beq` ∧ (← isOptimizeRecCall):
         - return `λ x y => x == y`
     - When `n := Int.negSucc ∧ ¬ (← isInFunApp)`
         - return `λ n => Int.neg (Int.ofNat (1 + n))`
     - When `n := Int.le`
         - return `mkIntLeOp`
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
  | Expr.const n _ =>
       withLocalContext $ do
         match n with
         | ``Nat.zero => stackContinuity stack (← mkNatLitExpr 0)
         | _ =>
           if (← isPartialDef n) then throwEnvError "normConst: partial function not supported {n} !!!"
           if (← isUnsafeDef n) then throwEnvError "normConst: unsafe definition not supported {n} !!!"
           if let some e ← isGlobalConstant n then return Sum.inl e
           if let some e ← isToNormOpaqueFun n then return e
           if let some r ← isHOF n then return r
           if (← isResolvableType e)
           then stackContinuity stack (← mkExpr (← resolveTypeAbbrev e))
           else stackContinuity stack (← mkExpr e)

  | _ => throwEnvError "normConst: name expression expected but got {reprStr e}"

  where
    @[always_inline, inline]
    isGlobalConstant (c : Name) : TranslateEnvT (Option (List OptimizeStack)) := do
      if let ConstantInfo.opaqueInfo opVal ← getConstEnvInfo c then
        return (.InitOptimizeExpr opVal.value :: stack)
      else return none

    /-- Apply the following normalization rules on opaque functions:
         - Nat.pred ==> λ n => n - 1
         - Nat.succ ==> λ n => 1 + n
         - Nat.le ==> ≤
         - Nat.ble ==> λ x y => decide (x ≤ y) (if isOptimizeRecCall)
         - Nat.beq ==> λ x y => x == y (if isOptimizeRecCall)
         - Int.negSucc ==> λ n => Int.neg (Int.ofNat (1 + n)) (if ¬ isInFunApp)
         - Int.le ==> ≤
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
             let decLeExpr ← mkExpr $ mkApp2 (← mkNatDecLeOp) (mkBVar 1) (mkBVar 0)
             let body ← mkExpr $ mkApp2 (← mkDecideConst) leExpr decLeExpr
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

     | _ => return none

    @[always_inline, inline]
    isHOF (f : Name) : TranslateEnvT (Option OptimizeContinuity) := do
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

end Solver.Optimize
