import Lean
import Solver.Optimize.Rewriting.OptimizeExists
import Solver.Optimize.Rewriting.OptimizeInt
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Rewriting.OptimizeMatch
import Solver.Optimize.Rewriting.OptimizeNat
import Solver.Optimize.Rewriting.OptimizeString
import Solver.Optimize.Env

open Lean Meta

namespace Solver.Optimize

/-- Gievn `f x₁ ... xₙ` return `true` when the following conditions are satisfied:
     -  ∃ i ∈ [1..n], isExplicit xᵢ ∧
     -  ∀ i ∈ [1..n], isExplicit xᵢ → isConstructor xᵢ ∨ isProp (← inferType xₓ) ∨ isFunType (← inferType xᵢ)
    NOTE: that constructors may contain free variables.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : MetaM Bool := do
  let stop := args.size
  let fInfo ← getFunInfoNArgs f stop
  let rec loop (i : Nat) (atLeastOneExplicit : Bool := false) : MetaM Bool := do
    if i < stop then
      let e := args[i]!
      let t ← inferType e
      let aInfo := fInfo.paramInfo[i]!
      if aInfo.isExplicit
      then if (← isConstructor e <||> isProp t <||> isFunType t)
           then loop (i+1) true
           else pure false
      else loop (i+1) atLeastOneExplicit
    else pure atLeastOneExplicit
  loop 0


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
def reduceApp? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
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
       | throwEnvError f!"reduceApp?: recursive function body expected for {reprStr f}"
     return (Expr.beta fbody auxFun.getAppArgs)

   isFunRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let Expr.const n _ := f | return none
     if !(← isRecursiveFun n) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some fbody ← getFunBody f
       | throwEnvError f!"reduceApp?: recursive function body expected for {reprStr f}"
     return (Expr.beta fbody args)

/--  Given application `f x₀ ... xₙ`, perform the following:
     - When `f := ite`
          - When n = 5 ∧ optimizer x₁ = True ∨ optimizer x₁ = False
              - return `optimizeITE f x₀ ... xₙ`
          - When n != 5
              - return ⊥

     - When `f := dite`
          - When n = 5 ∧ optimizer x₁ = True ∨ optimizer x₁ = False
              - return `optimizeDITE f x₀ ... xₙ`
          - When n != 5
              - return ⊥

     - Otherwise:
         - return none

-/
def reduceITEChoice?
  (f : Expr) (args : Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  if let some r ← isITEReduction? n args then return r
  if let some r ← isDITEReduction? n args then return r
  return none

  where
   isITEReduction? (n : Name) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     match n with
     | ``ite =>
         if args.size != 5 then throwEnvError "isITEReduction?: exactly five arguments expected"
         let args ← args.modifyM 1 optimizer
         match args[1]! with
         | Expr.const ``True _ =>
             -- normalize then clause
             return (← optimizer args[3]!)
         | Expr.const ``False _ =>
             -- normalize else clause
             return (← optimizer args[4]!)
         | _ => return none
     | _ => return none

   isDITEReduction? (n : Name) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     match n with
     | ``dite =>
         if args.size != 5 then throwEnvError "isDITEReduction?: exactly five arguments expected"
         let args ← args.modifyM 1 optimizer
         match args[1]! with
         | Expr.const ``True _ =>
             -- normalize then clause
             return (← extractDependentITEExpr (← optimizer args[3]!))
         | Expr.const ``False _ =>
             -- normalize else clause
             return (← extractDependentITEExpr (← optimizer args[4]!))
         | _ => return none
     | _ => return none


/--  Given application `f x₀ ... xₙ`, perform the following:
     - When `f x₀ ... xₙ` is a match expression of the form
          match e₀, ..., eₙ with
          | p₍₀₎₍₁₎, ..., p₍₀₎₍ₙ₎ => t₀
            ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
        - return `whnfExpr (f x₀ ... xₙ)` only when `∀ i ∈ [1..n], isConstructor (optimizer eᵢ)`.

     - Otherwise:
         - return none

-/
def reduceMatchChoice?
  (f : Expr) (args : Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n l := f | return none
  if let some r ← isMatchReduction? n l args then return r
  return none

  where
   isMatchReduction? (n : Name) (l : List Level) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let some matcherInfo ← getMatcherRecInfo? n l | return none
     let mut margs := args
     for i in [:args.size] do
       if i ≥ matcherInfo.getFirstDiscrPos && i < matcherInfo.getFirstAltPos
       then margs ← margs.modifyM i optimizer
     let discrs := margs[matcherInfo.getFirstDiscrPos : matcherInfo.getFirstAltPos]
     -- NOTE: whnf simplifies match only when all the discriminators are constructors
     if !(← allMatchDiscrsAreCtor discrs) then return none
     let auxApp := mkAppN f margs
     let e ← whnfExpr auxApp
     if (← exprEq e auxApp) then return none
     return e

   /- Return `true` only when at least one of the match discriminators is a constructor
      that may also contain free variables.
      Concretely given a match expression of the form:
        match e₁, ..., eₙ with
        | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
        ...
        | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
      Return `true` when `∀ i ∈ [1..n], isConstructor eᵢ`.
   -/
   allMatchDiscrsAreCtor (discrs : Subarray Expr) : TranslateEnvT Bool := do
     for i in [:discrs.size] do
       if !(← isConstructor discrs[i]!) then return false
     return true

/-- Perform constant propagation and apply simplifcation and normalization rules
    on application expressions.
-/
def optimizeApp (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  if let some e ← optimizePropNot? f args then
    trace[Optimize.propNot] f!"PropNot: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizePropBinary? f args then
    trace[Optimize.propBinary] f!"PropBinary: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeBoolNot? f args then
    trace[Optimize.boolNot] f!"BoolNot: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeBoolBinary? f args then
    trace[Optimize.boolBinary] f!"BoolBinary: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeEquality? f args then
    trace[Optimize.equality] f!"Equality: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeIfThenElse? f args then
    trace[Optimize.ite] f!"IfThenElse: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeNat? f args then
    trace[Optimize.nat] f!"Nat: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeInt? f args then
    trace[Optimize.int] f!"Int: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← structEqMatch? f args then
    trace[Optimize.eqMatch] f!"EqMatch: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeExists? f args then
    trace[Optimize.exists] f!"Exists: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeDecide? f args then
    trace[Optimize.decide] f!"Decide: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeRelational? f args then
    trace[Optimize.relational] f!"Relational: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  if let some e ← optimizeString? f args then
    trace[Optimize.string] f!"String: {reprStr (mkAppN f args)} ==> {reprStr e}"
    return e
  trace[Optimize.app] f!"Unchanged: {reprStr (mkAppN f args)}"
  mkAppExpr f args

/-- Given application `f x₁ ... xₙ`,
     - when `isNotfun f`
         - return none
     - when `t₁ → ... → tₘ ← inferType f ∧ n < m`:
        - when ∀ i ∈ [1..n], ¬ isExplicit tᵢ:
           - return none
        - otherwise:
           - return `etaExpand (mkAppN f args)`
     - otherwise `none`
-/
def normPartialFun? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 if (← isNotFun f) then return none
 let fInfo ← getFunInfo f
 if fInfo.paramInfo.size <= args.size then return none
 let mut nbImplicits := 0
 for i in [:fInfo.paramInfo.size] do
   if !fInfo.paramInfo[i]!.isExplicit then
      nbImplicits := nbImplicits.add 1
 if nbImplicits == args.size then return none
 etaExpand (mkAppN f args)

 where
   isNotFun (e : Expr) : TranslateEnvT Bool :=
    isNotFoldable e #[] (opaqueCheck := false) (recFunCheck := false)

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
def normOpaqueAndRecFun
  (uf : Expr) (uargs: Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT Expr := do
 let Expr.const n _ := uf | return (← mkAppExpr uf uargs)
 let isOpaqueRec ← isOpaqueRecFun uf uargs
 if (← isRecursiveFun n) || isOpaqueRec
 then
   trace[Optimize.recFun] f!"normalizing rec function {n}"
   let (f, args) ← resolveOpaque uf uargs isOpaqueRec
   trace[Optimize.recFun] f!"resolved opaque instance {reprStr f} {reprStr args}"
   -- retrieve implicit arguments
   let params ← getImplicitParameters f args
   trace[Optimize.recFun] f!"implicit arguments for {n} ==> {reprStr params}"
   -- get instance application
   let instApp ← getInstApp f params
   if (← isVisitedRecFun instApp) then
     trace[Optimize.recFun] f!"rec function instance {instApp} is in visiting cache"
     optimizeRecApp f params -- already cached
   else
     if let some r ← hasRecFunInst? instApp then
        trace[Optimize.recFun] f!"rec function instance {instApp} is already equivalent to {reprStr r}"
        return (← optimizeRecApp r params)
     cacheFunName instApp -- cache function name
     let some fbody ← getFunBody f
       | throwEnvError f!"normOpaqueAndRecFun: recursive function body expected for {reprStr f}"
     -- instantiating polymorphic parameters in fun body
     let fdef ← generalizeRecCall f params fbody
     trace[Optimize.recFun] f!"generalizing rec body for {n} got {reprStr fdef}"
     -- optimize recursive fun definition and store
     let optDef ← optimizer fdef
     -- remove from visiting cache
     uncacheFunName instApp
     let subsInst ← opaqueInstApp uf uargs isOpaqueRec instApp
     let fn' ← storeRecFunDef subsInst params optDef
     trace[Optimize.recFun] f!"rec function instance {subsInst} is equivalent to {reprStr fn'}"
     optimizeRecApp fn' params
   else optimizeApp uf uargs -- optimizations on opaque functions

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
         | throwEnvError f!"resolveOpaque: unfolded definition expected for {reprStr f}"
       if auxApp.isLambda then
         -- partially applied function
         let appCall := getLambdaBody auxApp
         let largs := appCall.getAppArgs
         return (appCall.getAppFn', largs[0:largs.size-auxApp.getNumHeadLambdas])
       else
         return (auxApp.getAppFn', auxApp.getAppArgs)
     else return (f, args)

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
   optimizeRecApp (rf : Expr) (params : ImplicitParameters) : TranslateEnvT Expr := do
     if params.isEmpty then return rf
     if (← exprEq uf rf) then
       -- case for when same recurisve call
       trace[Optimize.recFun.app] f!"same recursive call case {reprStr rf} {reprStr uargs}"
       optimizeApp rf uargs
     else if rf.isConst then
         -- case when a polymorphic/non-polymorphic function is equivalent to another non-polymorphic one
         let eargs := Array.filterMap (λ p => if !p.isInstance then some p.effectiveArg else none) params
         trace[Optimize.recFun.app] f!"non-polymorphic equivalent case {reprStr rf} {reprStr eargs}"
         optimizeApp rf eargs
     else
       let eargs := getEffectiveParams params
       let auxApp := rf.beta eargs
       if auxApp.isLambda then
         -- case for partially applied functions, i.e., some explicit arguments not provided
         let appCall := getLambdaBody auxApp
         let largs := appCall.getAppArgs
         trace[Optimize.recFun.app] f!"partially applied case {reprStr appCall.getAppFn'} {reprStr largs[0:largs.size-auxApp.getNumHeadLambdas]}"
         optimizeApp appCall.getAppFn' largs[0:largs.size-auxApp.getNumHeadLambdas]
       else
         trace[Optimize.recFun.app] f!"polymorphic equivalent case {reprStr auxApp.getAppFn'} {reprStr auxApp.getAppArgs}"
         optimizeApp auxApp.getAppFn' auxApp.getAppArgs

initialize
  registerTraceClass `Optimize.recFun
  registerTraceClass `Optimize.recFun.app
  registerTraceClass `Optimize.app
  registerTraceClass `Optimize.propNot
  registerTraceClass `Optimize.propBinary
  registerTraceClass `Optimize.boolNot
  registerTraceClass `Optimize.boolBinary
  registerTraceClass `Optimize.equality
  registerTraceClass `Optimize.ite
  registerTraceClass `Optimize.nat
  registerTraceClass `Optimize.int
  registerTraceClass `Optimize.eqMatch
  registerTraceClass `Optimize.exists
  registerTraceClass `Optimize.decide
  registerTraceClass `Optimize.relational
  registerTraceClass `Optimize.string

end Solver.Optimize
