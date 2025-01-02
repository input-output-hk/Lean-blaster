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

/-- Determine if all explicit parameters of a function are constructors that
    may also contain free variables.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : MetaM Bool := do
  let stop := args.size
  let fInfo ← getFunInfoNArgs f stop
  let rec loop (i : Nat) (atLeastOneExplicit : Bool := false) : MetaM Bool := do
    if i < stop then
      let e := args[i]!
      let aInfo := fInfo.paramInfo[i]!
      if aInfo.isExplicit
      then if (← isConstructor e)
           then loop (i+1) true
           else pure false
      else loop (i+1) atLeastOneExplicit
    else pure atLeastOneExplicit
  loop 0


/-- Given application `f x₁ ... xₙ`, perform the following:
     - When `f x₁ ... xₙ` is a match expression of the form
          match e₁, ..., eₙ with
          | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
            ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
        - return `whnfExpr (f x₁ ... xₙ)` only when `∀ i ∈ [1..n], isConstructor eᵢ`.

     - When `isRecursiveFun f ∧ ¬ isOpaqueFunExpr f #[x₁ ... xₙ] ∧
             ∀ i ∈ [1..n], isExplicit x₁ → isConstructor xᵢ ∧ (← getFunBody f).isSome`
          let some body ← getFunBody f
         - return `Expr.beta body #[x₁ ... xₙ]`
     - Otherwise:
         - return none
-/
def reduceApp? (f : Expr) (args: Array Expr) : TranslateEnvT (Option Expr) := do
 if (← isOpaqueFunExpr f args) then return none
 if let some r ← isMatchReduction? f args then return r
 if let some r ← isFunRecReduction? f args then return r
 return none

 where
   isFunRecReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let Expr.const n _ := f | return none
     if !(← isRecursiveFun n) then return none
     if !(← allExplicitParamsAreCtor f args) then return none
     let some fbody ← getFunBody f
       | throwEnvError f!"reduceApp?: recursive function body expected for {reprStr f}"
     return (Expr.beta fbody args)

   isMatchReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     if !(← allMatchDiscrsAreCtor f args) then return none
     let auxApp := mkAppN f args
     let e ← whnfExpr auxApp
     if (← exprEq e auxApp) then return none
     return e

   /- Return `true` only when `f` corresponds to a match function and all the
      the match discriminators in `args` are constructors that may also
      contain free variable.
      Concretely given a match expression of the form:
        match e₁, ..., eₙ with
        | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
        ...
        | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
      Return `true` when `∀ i ∈ [1..n], isConstructor eᵢ`.
   -/
   allMatchDiscrsAreCtor (f : Expr) (nargs: Array Expr) : TranslateEnvT Bool := do
     let Expr.const n l := f | return false
     let some matcherInfo ← getMatcherRecInfo? n l | return false
     let args ← normRecursorArgs n nargs
     let discrs := args[matcherInfo.getFirstDiscrPos : matcherInfo.getFirstAltPos]
     for i in [:discrs.size] do
       if !(← isConstructor discrs[i]!) then return false
     return true

/-- Perform constant propagation and apply simplifcation and normalization rules
    on application expressions.
-/
def optimizeApp (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
  if let some e ← optimizePropNot? f args then return e
  if let some e ← optimizePropBinary? f args then return e
  if let some e ← optimizeBoolNot? f args then return e
  if let some e ← optimizeBoolBinary? f args then return e
  if let some e ← optimizeEquality? f args then return e
  if let some e ← optimizeIfThenElse? f args then return e
  if let some e ← optimizeNat? f args then return e
  if let some e ← optimizeInt? f args then return e
  if let some e ← structEqMatch? f args then return e
  if let some e ← optimizeExists? f args then return e
  if let some e ← optimizeDecide? f args then return e
  if let some e ← optimizeRelational? f args then return e
  if let some e ← optimizeString? f args then return e
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
   isNotFun (e : Expr) : MetaM Bool := do
    let Expr.const n _ := e | return true
    (isInstance n) <||> (isClassConstraint n) <||> (isMatchExpr n)

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
  (f : Expr) (args: Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT Expr := do
 let Expr.const n _ := f | return (← mkAppExpr f args)
 if (← isRecursiveFun n)
 then
   -- retrieve implicit arguments
   let params ← getImplicitParameters f args
   -- get instance application
   let instApp ← getInstApp f params
   if (← isVisitedRecFun instApp)
   then optimizeRecApp f params -- already cached
   else
     if let some r ← hasRecFunInst? instApp then
        return (← optimizeRecApp r params)
     cacheFunName instApp -- cache function name
     let some fbody ← getFunBody f
       | throwEnvError f!"normOpaqueAndRecFun: recursive function body expected for {reprStr f}"
     -- instantiating polymorphic parameters in fun body
     let fdef ← generalizeRecCall f params fbody
     -- optimize recursive fun definition and store
     let fn' ← storeRecFunDef instApp params (← optimizer fdef)
     -- only considering explicit args when instantiating
     -- as storeRecFunDef already handled implicit arguments
     -- NOTE: optimizations on cached opaque recursive functions required
     optimizeRecApp fn' params
   else optimizeApp f args -- optimizations on opaque functions

 where
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
     let instanceArgs := Array.filter (λ p => p.isInstance) params
     if (instanceArgs.isEmpty || (← exprEq f rf)) then
       -- case for non polymorphic function or recursive call in fun body
         optimizeApp rf args
     else if rf.isConst then
         -- case when a polymorphic function is equivalent to a non-polymorphic one
         let eargs := Array.filterMap (λ p => if !p.isInstance then some p.effectiveArg else none) params
         optimizeApp rf eargs
     else
       let eargs := getEffectiveParams params
       let auxApp := rf.beta eargs
       if auxApp.isLambda then
         -- case for partially applied functions, i.e., some explicit arguments not provided
         let appCall := getLambdaBody auxApp
         let largs := appCall.getAppArgs
         optimizeApp appCall.getAppFn' largs[0:largs.size-auxApp.getNumHeadLambdas]
       else optimizeApp auxApp.getAppFn' auxApp.getAppArgs

end Solver.Optimize
