import Lean
import Blaster.Optimize.Rewriting.FunPropagation
import Blaster.Optimize.Rewriting.OptimizeBoolNot
import Blaster.Optimize.Rewriting.OptimizeBoolPropBinary
import Blaster.Optimize.Rewriting.OptimizeDecide
import Blaster.Optimize.Rewriting.OptimizeDecideBoolBinary
import Blaster.Optimize.Rewriting.OptimizeExists
import Blaster.Optimize.Rewriting.OptimizeInt
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeNat
import Blaster.Optimize.Rewriting.OptimizeString
import Blaster.Optimize.OptimizeStack

open Lean Meta

namespace Blaster.Optimize

/-- Given application `f x₁ ... xₙ`, perform the following:
     - When `isOpaqueRecFun f #[x₁ ... xₙ] ∧ allExplicitParamsAreCtor f #[x₁ ... xₙ]
          - When some auxFun ← unfoldOpaqueFunDef f #[x₁ ... xₙ]
             - When some body ← getFunBody auxFun.getAppFn'
                - return `Expr.beta body auxFun.getAppArgs`
             - Otherwise:
                - return ⊥
          - Otherwise:
              - return none
     - When `isRecursiveFun f ∧ ¬ isOpaqueFunExpr f #[x₁ ... xₙ] ∧ allExplicitParamsAreCtor f #[x₁ ... xₙ]
         - When some body ← getFunBody f:
             - return `Expr.beta body #[x₁ ... xₙ]`
         - Otherwise:
             - return ⊥
     - Otherwise:
         - return none
-/
def reduceApp? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if let some r ← isOpaqueRecReduction? f args then return r
 if (← isOpaqueFunExpr f args) then return none
 if let some r ← isFunRecReduction? f args then return r
 return none

 where
   isOpaqueRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     if !(← isOpaqueRecFun f args) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some auxFun ← unfoldOpaqueFunDef f args | return none
     let some fbody ← getFunBody auxFun.getAppFn'
       | throwEnvError "reduceApp?: recursive function body expected for {reprStr f}"
     return (betaLambda fbody auxFun.getAppArgs)

   isFunRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let Expr.const n _ := f | return none
     if !(← isRecursiveFun n) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some fbody ← getFunBody f
       | throwEnvError "reduceApp?: recursive function body expected for {reprStr f}"
     return (betaLambda fbody args)

/-- Perform constant propagation and apply simplification and normalization rules
    on application expressions.
-/
def optimizeAppAux (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  let args ← reorderOperands f args
  if let some e ← optimizePropNot? f args then return e
  if let some e ← optimizePropBinary? f args then return e
  if let some e ← optimizeBoolNot? f args then return e
  if let some e ← optimizeBoolBinary? f args then return e
  if let some e ← optimizeEquality? f args then return e
  if let some e ← optimizeNat? f args then return e
  if let some e ← optimizeInt? f args then return e
  if let some e ← optimizeExists? f args then return e
  if let some e ← optimizeDecide? f args then return e
  if let some e ← optimizeRelational? f args then return e
  if let some e ← optimizeString? f args then return e
  let appExpr := mkAppN f args
  if (← isResolvableType appExpr) then return (← resolveTypeAbbrev appExpr)
  return appExpr

/-- Perform the following:
     - apply normalization and simplification rrules on the given application expression
     - When restart flag is set:
        - add optimized application on continuation stack
     - Otherwise:
         - try tp apply function propagation over ite and match:
            - When propagation rules are triggered:
                - add result on continuation stack
            - Otherwise:
                - cache normalized application
                - proceed with stack continuity

    NOTE: skipPropCheck is set to `true` only when it is known beforehand that `f`
    is a recursive function for which `allExplicitParamsAreCtor f args (funPropagation := true)`
    returns `true`.
-/
def optimizeApp
  (f : Expr) (args: Array Expr)
  (stack : List OptimizeStack) (skipPropCheck := false) : TranslateEnvT OptimizeContinuity := do
  let e ← optimizeAppAux f args
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else
    match (← isFunPropagation? e) with
    | some r => return Sum.inl (.InitOptimizeExpr r :: stack)
    | none => stackContinuity stack (← mkExpr e) -- cache expression and proceed with continuity

  where
    @[always_inline, inline]
    isFunPropagation? (e : Expr) : TranslateEnvT (Option Expr) :=
      if e.isApp then
        let (f', args') := getAppFnWithArgs e
        funPropagation? f' args' skipPropCheck
      else return none

/-- Given application `f x₁ ... xₙ`,
     - When `isFunITE f` (i.e., f is a Blaster.dite' that return a function)
         - return none
     - when `isNotfun f`
         - return none
     - when `t₁ → ... → tₘ ← inferType f ∧ n < m`:
        - when ∀ i ∈ [1..n], ¬ isExplicit tᵢ:
           - return none
        - otherwise:
           - return `etaExpand (mkAppN f args)`
     - otherwise `none`
-/
def normPartialFun? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
 if isFunITE f then return none
 if (← isNotFun f) then return none
 let pInfo ← getFunEnvInfo f
 if pInfo.paramsInfo.size <= args.size then return none
 let nbImplicits := pInfo.paramsInfo.foldl (fun acc p => if !p.isExplicit then acc + 1 else acc) 0
 if nbImplicits == args.size then return none
 etaExpand (mkAppN f args)

 where
   isFunITE (e : Expr) : Bool :=
     match e with
     | Expr.const ``Blaster.dite' _ => args.size > 4
     | _ => false

/-- Given application `f x₁ ... xₙ` perform the following:
    - when `f` corresponds to a recursive definition `λ p₁ ... pₙ → body` the following actions are performed:
        - params ← getImplicitParameters f #[x₁ ... xₙ]
        - fᵢₙₛ ← getInstApp f params
        - When entry `fᵢₙₛ := fdef` exists in the instance cache and `fdef := fₙ` is in the recursive function map.
             - return `optimizeRecApp fₙ params`
        - when no entry for `fᵢₙₛ` exists in the instance cache:
           - fbody' ← optimizer (← generalizeRecCall f params (λ p₁ ... pₙ → body))`
           - call `storeRecFunDef` to update instance cache and check if recursive definition already exists in map, i.e.:
               fᵢ ← storeRecFunDef fᵢₙₛ fbody'
           - return `optimizeRecApp fᵢ params`
    - when `f` is not a recursive definition or is already in the recursive visited cache.
       - return `optimizeApp f x₁ ... xₙ`.
    Assumes that an entry exists for each opaque recursive function in `recFunMap` before
    optimization is performed (see function `cacheOpaqueRecFun`).
-/
def normOpaqueAndRecFun (s : OptimizeStack) (xs : List OptimizeStack) :
  TranslateEnvT OptimizeContinuity := withLocalContext $ do
  match s with
  | .InitOpaqueRecExpr uf uargs =>
      let Expr.const n _ := uf | return (← stackContinuity xs (← mkAppExpr uf uargs))
      let isOpaqueRec ← isOpaqueRecFun uf uargs
      if (← isRecursiveFun n) || isOpaqueRec
      then
        if (← allExplicitParamsAreCtor uf uargs (funPropagation := true)) then
          -- call fun propagation to avoid optimizing rec body
          -- if rec function is an opaqueRec call app optimization first
          -- before calling fun propagation
          optimizeApp uf uargs xs (skipPropCheck := true)
        else
          -- trace[Optimize.recFun] "normalizing rec function {n}"
          let (f, args) ← resolveOpaque uf uargs isOpaqueRec
          -- trace[Optimize.recFun] "resolved opaque instance {reprStr f} {reprStr args}"
          -- retrieve implicit arguments
          let params ← getImplicitParameters f args
          -- trace[Optimize.recFun] "implicit arguments for {n} ==> {reprStr params}"
          -- get instance application
          let instApp ← getInstApp f params
          if (← isVisitedRecFun instApp) then
            -- trace[Optimize.recFun] "rec function instance {instApp} is in visiting cache"
            optimizeRecApp uf f uargs params xs -- already cached
          else if let some r ← hasRecFunInst? instApp then
            -- trace[Optimize.recFun] "rec function instance {instApp} is already equivalent to {reprStr r}"
            optimizeRecApp uf r uargs params xs
          else
            cacheFunName instApp -- cache function name
            let some fbody ← getFunBody f
              | throwEnvError "normOpaqueAndRecFun: recursive function body expected for {reprStr f}"
            -- instantiating polymorphic parameters in fun body
            let fdef ← generalizeRecCall f params fbody
            -- trace[Optimize.recFun] "generalizing rec body for {n} got {reprStr fdef}"
            let subsInst ← opaqueInstApp uf uargs isOpaqueRec instApp
            -- optimize recursive fun definition and store
            return Sum.inl (.InitOptimizeExpr fdef :: .RecFunDefWaitForStorage uargs instApp subsInst params :: xs)
      else optimizeApp uf uargs xs -- optimizations on opaque functions

  | .RecFunDefStorage uargs instApp subsInst params optDef =>
        uncacheFunName instApp
        -- trace[Optimize.recFun] "optimized rec body for {reprStr subsInst} got {reprStr optDef}"
        let fn' ← storeRecFunDef subsInst params optDef
        -- trace[Optimize.recFun] "rec function instance {reprStr subsInst} is equivalent to {reprStr fn'}"
        optimizeRecApp subsInst fn' uargs params xs

  | _ => throwEnvError "normOpaqueAndRecFun: unexpected continuity {reprStr s} !!!"

 where

   /-- Given a function application f x₁ ... xₙ, flag `isOpaqueRec` and default instance application `instApp`
       perform the following:
         - When isOpaqueRec:
             - return `getInstApp (← getImplicitParameters f x₁ ... xₙ)`
         - Otherwise:
             - return instApp
   -/
   opaqueInstApp (f : Expr) (args : Array Expr) (isOpaqueRec : Bool) (instApp : Expr) : TranslateEnvT Expr := do
     if isOpaqueRec then
        getInstApp f (← getImplicitParameters f args)
     else return instApp

   /-- Given a function application f x₁ ... xₙ and flag `isOpaqueRec` perform the following:
         - When isOpaqueRec:
             let auxApp ← unfoldOpaqueFunDef f x₁ ... xₙ
              - when auxApp := λ α₀ → ... → λ αₖ → fₑ x₀ ... xₙ` (i.e., partially applied opaque relational function)
                 - return (fₑ, x₀ ... xₙ₋ₖ)
              - when auxApp := fₑ x₀ ... xₙ` (default case)
                 - return (fₑ, x₀ ...xₙ)
         - Otherwise:
              - return (f, x₁ ... xₙ)
   -/
   resolveOpaque (f : Expr) (args : Array Expr) (isOpaqueRec : Bool) : TranslateEnvT (Expr × Array Expr) := do
     if isOpaqueRec then
       let some auxApp ← unfoldOpaqueFunDef f args
         | throwEnvError "resolveOpaque: unfolded definition expected for {reprStr f}"
       if auxApp.isLambda then
         -- partially applied function
         let appCall := getLambdaBody auxApp
         let largs := appCall.getAppArgs
         return (appCall.getAppFn', largs.take (largs.size-auxApp.getNumHeadLambdas))
       else
         return (auxApp.getAppFn', auxApp.getAppArgs)
     else return (f, args)

   normRecOpaque (f : Expr) : Bool :=
     match f with
     | Expr.const ``Nat.beq _
     | Expr.const ``Nat.ble _ => true
     | _ => false

   /-- Given `rf` a function application instance (see function `getInstApp`) and `params` its
       implicit parameter inffo (see function `getImplicitParameters`), perform the following:
         let instanceArgs := [ params[i] | ∀ i ∈ [0..params.size-1] ∧ params[i].isInstance ]
        - When params.isEmpty :
            - return rf
        - When instanceArgs.isEmpty ∨ f =ₚₜᵣ rf (i.e., non ploymorphic function or rec call in fun body)
            - return `optimizeApp rf args`
        - When rf.isConst (i.e., polymorphic function equivalent to a non-polymorphic one)
            - return `optimizeApp rf [params[i] | ∀ i ∈ [0..params.size-1] ∧ ¬ params[i].instance]`
        - Otherwise:
            let auxApp := Expr.beta rf (getEffectiveParams params)
             - When `auxApp := λ α₀ → ... → λ αₖ → fₑ x₀ ... xₙ` (i.e., partially applied polymorphic function)
                 - return `optimizeApp fₑ x₀ ...xₙ₋ₖ`
             - When `auxApp := fₑ x₀ ... xₙ` (default case)
                 - return `optimizeApp fₑ x₀ ...xₙ`
   -/
   optimizeRecApp
     (uf rf : Expr) (uargs : Array Expr)
     (params : ImplicitParameters) (xs : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
     if params.isEmpty then
       return ← stackContinuity xs (← mkExpr rf (cacheResult := !(normRecOpaque rf))) -- catch fun expression
     if exprEq uf rf then
       -- case for when same recursive call
       -- trace[Optimize.recFun.app] "same recursive call case {reprStr rf} {reprStr uargs}"
       if rf.isConst then
         optimizeApp rf uargs xs
       else -- polyomrphic case: we need to remove the generic parameters
         let auxApp := rf.beta (← getEffectiveParams params)
         let (f, args) := getAppFnWithArgs auxApp
         optimizeApp f args xs
     else if rf.isConst then
         -- case when a polymorphic/non-polymorphic function is equivalent to another non-polymorphic one
         let eargs := Array.filterMap (λ p => if !p.isInstance then some p.effectiveArg else none) params
         -- trace[Optimize.recFun.app] "non-polymorphic equivalent case {reprStr rf} {reprStr eargs}"
         optimizeApp rf eargs xs
     else
       let auxApp := rf.beta (← getEffectiveParams params)
       if auxApp.isLambda then
         -- case for partially applied functions, i.e., some explicit arguments not provided
         let appCall := getLambdaBody auxApp
         let (f, largs) := getAppFnWithArgs appCall
         -- trace[Optimize.recFun.app] "partially applied case {reprStr appCall.getAppFn'} {reprStr largs[0:largs.size-auxApp.getNumHeadLambdas]}"
         optimizeApp f (largs.take (largs.size-auxApp.getNumHeadLambdas)) xs
       else
         -- trace[Optimize.recFun.app] "polymorphic equivalent case {reprStr auxApp.getAppFn'} {reprStr auxApp.getAppArgs}"
         let (f, args) := getAppFnWithArgs auxApp
         optimizeApp f args xs

initialize
  registerTraceClass `Optimize.recFun
  registerTraceClass `Optimize.recFun.app


end Blaster.Optimize
