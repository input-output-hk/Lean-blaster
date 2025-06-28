import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta

namespace Solver.Optimize

/-- Given `e := Expr.const n l, apply the following normalization rule:
     - When `n := Nat.zero` return `Expr.lit (Literal.natVal 0)`
     - When `ConstantIno.opaqueInfo opVal ← getConstInfo n` (i.e., n is a constant defined at top level)
        - return `optimizer opVal`
     - When !(← isInFunApp) (i.e., const expression is not a function application but is a HOF passed as argument)
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
        - When `¬ isNotFoldable e (recFunCheck := false) ∧ ¬ hasImplicitArgs e`:
           - When `isRecursiveFun n` (i.e., a recursive function passed as argument):
              - return `(← normOpaqueAndRecFun e #[] optimizer)`
           - When `(← getFunBody e).isSome ∧ ¬ isRecursiveFun n`:
              - return `optimizer (← getFunBody e)`
     - Otherwise:
         - When !(← isInFunApp) ∧ isType e:
             return `mkExpr (← resolveTypeAbbrev e)`
         - Otherwise
            - return `mkExpr e`
-/
partial def normConst (e : Expr) (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let Expr.const n _ := e | throwEnvError "normConst: name expression expected but got {reprStr e}"
  match n with
  | ``Nat.zero => mkNatLitExpr 0
  | _ =>
    if (← isPartialDef n) then throwEnvError "normConst: partial function not supported {n} !!!"
    if (← isUnsafeDef n) then throwEnvError "normConst: unsafe definition not supported {n} !!!"
    if let some e ← isGlobalConstant n then return e
    if let some e ← isToNormOpaqueFun n then
      trace[Optimize.const.opaque] "normalizing opaque function {n} => {reprStr e}"
      return e
    if let some r ← isHOF n then
      trace[Optimize.const.hof] "normalizing HOF {n} => {reprStr r}"
      return r
    -- catch if no normalization performed
    if !(← isInFunApp) && (← isResolvableType e)
    then mkExpr (← resolveTypeAbbrev e)
    else mkExpr e

  where
    isGlobalConstant (c : Name) : TranslateEnvT (Option Expr) := do
      let ConstantInfo.opaqueInfo opVal ← getConstEnvInfo c | return none
      trace[Optimize.const.global] "normalizing global constant {c} => {reprStr opVal.value}"
      optimizer opVal.value

    etaNormOpaqueFun (of : Expr) : TranslateEnvT Expr := do
      let rec visit (l : Expr) : TranslateEnvT Expr := do
        match l with
        | Expr.lam n t b bi =>
             withLocalDecl n bi (← optimizer t) fun x => do
               mkLambdaExpr x (← visit (b.instantiate1 x))
        | r => optimizeApp r.getAppFn' r.getAppArgs
      visit (← etaExpand of)

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

    isToNormOpaqueFun (n : Name) : TranslateEnvT (Option Expr) := do
      if (← isInFunApp) && isNormOpaqueFun n then return e -- to avoid catching
      match n with
      | ``Int.negSucc
      | ``Nat.pred
      | ``Nat.succ => etaNormOpaqueFun e
      | ``Int.le => mkIntLeOp
      | ``Nat.le => mkNatLeOp
      | ``Nat.ble =>
           if (← isOptimizeRecCall) then etaNormOpaqueFun e else return none
      | ``Nat.beq =>
           if (← isOptimizeRecCall) then mkNatBEqOp else return none
      | _ => return none

    isHOF (f : Name) : TranslateEnvT (Option Expr) := do
      if (← isInFunApp) then return none
      if (← isNotFoldable e #[] (recFunCheck := false)) then return none
      if (← hasImplicitArgs e) then return none
      if (← isRecursiveFun f) then
        -- catch fun expression after adding recursive definition in map
        return (← mkExpr (← normOpaqueAndRecFun e #[] optimizer))
      -- non recursive function case
      let some fbody ← getFunBody e | return none
      optimizer fbody

initialize
  registerTraceClass `Optimize.const.global
  registerTraceClass `Optimize.const.opaque
  registerTraceClass `Optimize.const.hof

end Solver.Optimize
