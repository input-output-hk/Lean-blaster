import Lean
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta

namespace Solver.Optimize

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - When `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - When `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - When ¬ (← isInFunApp) (i.e., const expression is not a function application but is a HOF passed as argument)
        - When `n := Int.negSucc ∨ n := Nat.pred ∨ n := Nat.succ`:
           - return `optimize (← etaExpand e)`
        - When `n := Int.le`
           - return `mkIntLeOp`
        - When `n := Nat.le`
           - return `mkNatLeOp`
        - When `n := Nat.beq` ∧ (← isOptimizeRecCall):
           - return `mkNatEqOp`
        - When `n := Nat.ble` ∧ (← isOptimizeRecCall):
           - return `optimize (← etaExpand e)`
        - When `¬ hasImplicitArgs e`:
           - When `isRecursiveFun n` (i.e., a recursive function passed as argument):
              - return `(← normOpaqueAndRecFun e #[] optimizer)`
           - When `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n ∧ ¬ isNotFoldable e`:
              - return `optimizer (← getFunBody e)`
     - Otherwise:
         - When ¬ (← isInFunApp) ∧ isType e:
             return `mkExpr (← resolveTypeAbbrev e)`
         - Otherwise
            - return `mkExpr e`
-/
def normConst (e : Expr) ( stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
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
           -- catch if no normalization performed
           if !(← isInFunApp) && (← isResolvableType e) then
              stackContinuity stack (← mkExpr (← resolveTypeAbbrev e))
           else stackContinuity stack (← mkExpr e)

  | _ => throwEnvError "normConst: name expression expected but got {reprStr e}"

  where
    @[always_inline, inline]
    isGlobalConstant (c : Name) : TranslateEnvT (Option (List OptimizeStack)) := do
      if let ConstantInfo.opaqueInfo opVal ← getConstEnvInfo c then
        return (.InitOptimizeExpr opVal.value :: stack)
      else return none

    @[always_inline, inline]
    isNormOpaqueFun (n : Name) : Bool :=
      match n with
      | ``Int.negSucc
      | ``Nat.pred
      | ``Nat.succ
      | ``Int.le
      | ``Nat.le
      | ``Nat.ble
      | ``Nat.beq => true
      | _ => false

    @[always_inline, inline]
    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option OptimizeContinuity) := do
      if (← isInFunApp) && isNormOpaqueFun n then return ← stackContinuity stack e -- to avoid catching
      else match n with
           | ``Int.negSucc
           | ``Nat.pred
           | ``Nat.succ => return (some $ Sum.inl (.InitOptimizeExpr (← etaExpand e) :: stack))
           | ``Int.le => stackContinuity stack (← mkIntLeOp)
           | ``Nat.le => stackContinuity stack (← mkNatLeOp)
           | ``Nat.ble =>
                if (← isOptimizeRecCall)
                then return (some $ Sum.inl (.InitOptimizeExpr (← etaExpand e) :: stack))
                else return none
           | ``Nat.beq =>
                if (← isOptimizeRecCall)
                then stackContinuity stack (← mkNatBEqOp)
                else return none
           | _ => return none

    @[always_inline, inline]
    isHOF (f : Name) : TranslateEnvT (Option OptimizeContinuity) := do
      if (← isInFunApp) then return none
      if (← hasImplicitArgs e) then return none
      if (← isRecursiveFun f) then
         return (some $ Sum.inl $ .InitOpaqueRecExpr e #[] :: stack)
      if (← isNotFoldable e #[]) then return none
      -- non recursive function case
      if let some fbody ← getFunBody e then
        return (some $ Sum.inl $ .InitOptimizeExpr fbody :: stack)
      else return none

end Solver.Optimize
