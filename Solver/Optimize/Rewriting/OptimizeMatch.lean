import Lean
import Solver.Optimize.Rewriting.OptimizeITE

open Lean Meta Elab
namespace Solver.Optimize

structure MatchInfo where
  /-- Name of match -/
  name : Name
  /-- Name expression of match -/
  nameExpr : Expr
  /-- Match arguments -/
  args : Array Expr
  /-- match instantiation -/
  instApp : Expr
  /-- MatcherInfo for match -/
  mInfo : MatcherInfo

/-- Determine if `e` is an `match` expression and return its corresponding arguments, its instantiation
    and MatcherInfo.
    Otherwise return `none`.
-/
def isMatchArg? (e : Expr) : TranslateEnvT (Option MatchInfo) := do
 Expr.withApp e fun pm args => do
   let Expr.const n l := pm | return none
   let some mInfo ← getMatcherRecInfo? n l | return none
   let cInfo ← getConstInfo n
   let matchFun ← instantiateValueLevelParams cInfo l
   let instApp := Expr.beta matchFun (args.take mInfo.getFirstAltPos)
   return some { name := n, nameExpr := pm, args, instApp, mInfo}

mutual

private partial def isCstMatchPropAux (p : Expr) (k : Bool → TranslateEnvT Bool) : TranslateEnvT Bool := do
 if (← isConstructor p) then return (← k true)
 match ite? p with
   | some (_sort, _cond, _decide, e1, e2) =>
       isCstMatchPropAux e1 fun _b =>
         -- NOTE: No need to check for b as if it's false the continuation function is not called
         isCstMatchPropAux e2 k
   | none =>
     match dite? p with
     | some (_sort, _cond, _decide, e1, e2) =>
         isCstMatchPropAux (← extractDependentITEExpr e1) fun _b => do
           -- NOTE: No need to check for b as if it's false the continuation function is not called
           isCstMatchPropAux (← extractDependentITEExpr e2) k
     | none =>
        Expr.withApp p fun f args => do
          let Expr.const n l := f | return false
          let some matcherInfo ← getMatcherRecInfo? n l | return false
          let rhs := args[matcherInfo.getFirstAltPos : matcherInfo.arity]
          -- NOTE: we also need to cater for function as return type,
          -- i.e., match expression returns a function.
          if args.size > matcherInfo.arity then return false
          else isCstDiscrsProp rhs (rhs.size - 1) k

private partial def isCstDiscrsProp
  (rhs : Subarray Expr) (idx : Nat) (k : Bool → TranslateEnvT Bool) : TranslateEnvT Bool := do
  if idx == 0 then
    -- NOTE: here we can use getLambdaBody as `isCstDiscrsProp` is called only
    -- when match expression does not return a function as result.
    isCstMatchPropAux (getLambdaBody rhs[idx]!) k
  else
    isCstMatchPropAux (getLambdaBody rhs[idx]!) fun _b =>
     -- NOTE: No need to check for b as if it's false the continuation function is not called
       isCstDiscrsProp rhs (idx - 1) k
end

/--  Return `true` only when
      isConstructor p ∨
      ( p := if c then e₁ else e₂ ∧ isCstMatchProp e₁ ∧ isCstMatchProp e₂ ) ∨
      ( p := dite c (fun h : c => e₁) (fun h : ¬ c => e₂) ∧ isCstMatchProp e₁ ∧ isCstMatchProp e₂ ) ∨
      ( p := match e₁, ..., eₙ with
              | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
              ...
              | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
        ∧ ∀ i ∈ [1..m], isCstMatchProp t₁ )
-/
def isCstMatchProp (p : Expr) : TranslateEnvT Bool :=
  isCstMatchPropAux p (λ x => return x)

/-- Given `f x₁ ... xₙ` return `true` when the following conditions are satisfied:
     -  ∃ i ∈ [1..n], isExplicit xᵢ ∧
     -  ∀ i ∈ [1..n], isExplicit xᵢ → isConstructor xᵢ ∨ isProp (← inferType xₓ) ∨ isFunType (← inferType xᵢ)
    NOTE: constructors may contain free variables.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) : TranslateEnvT Bool := do
  let stop := args.size
  let fInfo ← getFunInfoNArgs f stop
  let rec loop (i : Nat) (atLeastOneExplicit : Bool := false) : TranslateEnvT Bool := do
    if i < stop then
      let e := args[i]!
      let t ← inferType e
      let aInfo := fInfo.paramInfo[i]!
      if aInfo.isExplicit
      then
        if (← isConstructor e <||> isProp t <||> isFunType t)
        then loop (i+1) true
        else pure false
      else loop (i+1) atLeastOneExplicit
    else pure atLeastOneExplicit
  loop 0

/-- Return `b` if `m := b` is already in the weak head cache.
    Otherwise, perform the following actions
      - When .reduced e ← reduceMatcher? m
          - update cache with `m := some e`
          - return `some e`
      - Otherwise
          - update cache with `m := none`
          - return `none`
    Assume that `m` is a match expression.
-/
def reduceMatch? (m : Expr) : TranslateEnvT (Option Expr) := do
   let env ← get
   match env.optEnv.whnfCache.get? m with
   | some b => return b
   | none =>
       let res ← tryReduction? m
       let optEnv := {env.optEnv with whnfCache := env.optEnv.whnfCache.insert m res}
       set {env with optEnv := optEnv}
       return res
   where
     tryReduction? (m : Expr) : TranslateEnvT (Option Expr) := do
      let .reduced e ← withReducible (reduceMatcher? m) | return none
      return e

/-- call reduceMatch? on `m` only when `m` corresponds to a match expression.
    Otherwise return `m`.
-/
def tryMatchReduction? (m : Expr) : TranslateEnvT Expr := do
   let Expr.const n _ := m.getAppFn' | return m
   if !(← isMatchExpr n) then return m
   match (← reduceMatch? m) with
   | some re => return re
   | none => return m


/-- Apply the following constant propagation rules on match expressions, such that:
    Given  match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

    - When ∀ i ∈ [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               `eⱼ := if c then d₁ else d₂` ∧
                (i ≠ j → gᵢ = eᵢ) ∧ (i = j → gᵢ = d₁) ∧
                (i ≠ j → hᵢ = eᵢ) ∧ (i = j → hᵢ = d₂)
      Return
         `if c then match₁ g₁, ..., gₙ with ... else match₁ h₁, ..., hₙ with ...`

    - When ∀ i ∈ [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               `eⱼ := dite c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
                (i ≠ j → gᵢ = eᵢ) ∧ (i = j → gᵢ = d₁) ∧
                (i ≠ j → hᵢ = eᵢ) ∧ (i = j → hᵢ = d₂)
      Return
         `dite c (fun h : c => match₁ g₁, ..., gₙ with ...) (fun h : ¬ c => match₁ h₁, ..., hₙ with ...)`

    - When ∀ i ∈ [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               eⱼ := match₂ f₁, ..., fₚ with
                    | fp₍₁₎₍₁₎, ..., fp₍₁₎₍ₚ₎ => t₁
                    ...
                    | fp₍ₘ₎₍₁₎, ..., fp₍ₘ₎₍ₚ₎ => tₘ ∧

               ∀ k ∈ [1..m],
                (i ≠ j → g₍ₖ₎₍ᵢ₎ = eᵢ) ∧ (i = j → g₍ₖ₎₍ᵢ₎ = tₖ)
       Return
         `match₂ f₁, ..., fₚ with
          | fp₍₁₎₍₁₎, ..., fp₍₁₎₍ₚ₎ =>
             match₁ g₍₁₎₍₁₎, ..., g₍₁₎₍ₙ₎ with ...
          ...
          | fp₍ₘ₎₍₁₎, ..., fp₍ₘ₎₍ₚ₎ =>
             match₁ g₍ₘ₎₍₁₎, ..., g₍ₘ₎₍ₙ₎ with ...`

-/
def constMatchPropagation?
  (cm : Expr) (cargs : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
  if !(← allDiscrsAreCstMatch cargs mInfo) then return none
  for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
    if let some r ← iteCstProp? cm cargs i mInfo then return r
    if let some r ← diteCstProp? cm cargs i mInfo then return r
    if let some r ← matchCstProp? cm cargs i mInfo then return r
  return none

  where
    allDiscrsAreCstMatch (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT Bool := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if !(← isCstMatchProp args[i]!) then return false
      return true

    /-- Implements ite over match rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
     if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArg]! then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to ite.
        let margs := args.take mInfo.arity
        let extra_args := args.extract mInfo.arity args.size
        let e1' ← tryMatchReduction? (← mkExpr (mkAppN f (margs.set! idxArg e1)) (cacheResult := false))
        let e2' ← tryMatchReduction? (← mkExpr (mkAppN f (margs.set! idxArg e2)) (cacheResult := false))
        -- NOTE: we also need to set the sort type for the pulled ite to meet
        -- the return type of the embedded match
        let retType ← inferType (mkAppN f margs)
        let iteExpr ← mkExpr (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
        if !extra_args.isEmpty
        then return ← mkExpr (mkAppN iteExpr extra_args) (cacheResult := false)
        else return iteExpr
      return none

    pushMatchInDIteExpr (f : Expr) (args : Array Expr) (idxDiscr : Nat) (ite_e : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      -- Anyway, we can't pattern match on a function
      lambdaTelescope ite_e fun params body => do
        let body' ← tryMatchReduction? (← mkExpr (mkAppN f (args.set! idxDiscr body)) (cacheResult := false))
        mkLambdaFVars params body'

    /-- Implements dite over match rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
      if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArg]! then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to dite.
        let margs := args.take mInfo.arity
        let extra_args := args.extract mInfo.arity args.size
        let e1' ← pushMatchInDIteExpr f margs idxArg e1
        let e2' ← pushMatchInDIteExpr f margs idxArg e2
        -- NOTE: we also need to set the sort type for the pulled dite to meet
        -- the return type of the embedded match
        let retType ← inferType (mkAppN f margs)
        let diteExpr ← mkExpr (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
        if !extra_args.isEmpty
        then return (← mkExpr (mkAppN diteExpr extra_args) (cacheResult := false))
        return diteExpr
      return none

    updateRhsWithMatch (f : Expr) (args : Array Expr) (idx : Nat) (rhs : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      -- Anyway, we can't pattern match on a function
      lambdaTelescope rhs fun params body => do
        let body' ← tryMatchReduction? (← mkExpr (mkAppN f (args.set! idx body)) (cacheResult := false))
        mkLambdaFVars params body'

    updateReturnType (pType : Expr) (eType : Expr) : TranslateEnvT Expr := do
      lambdaTelescope pType fun params _body => mkLambdaFVars params eType

    /-- Implements match over match rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
     if let some argInfo ← isMatchArg? args[idxArg]! then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to pulled match.
        let margs := args.take mInfo.arity
        let extra_args := args.extract mInfo.arity args.size
        let mut pargs' := argInfo.args
        let idxPType := argInfo.mInfo.getFirstDiscrPos - 1
        for k in [argInfo.mInfo.getFirstAltPos : argInfo.mInfo.arity] do
          pargs' := pargs'.set! k (← updateRhsWithMatch f margs idxArg argInfo.args[k]!)
          -- NOTE: we also need to set the return type for pulled over match
          -- to meet the return type of the embedded match.
          let retType ← inferType (mkAppN f margs)
          pargs' := pargs'.set! idxPType (← updateReturnType argInfo.args[idxPType]! retType)
        let pMatchExpr ← mkExpr (mkAppN argInfo.nameExpr pargs') (cacheResult := false)
        if !extra_args.isEmpty
        then return (← mkExpr (mkAppN pMatchExpr extra_args) (cacheResult := false))
        return pMatchExpr
      return none


/--  Given application `f x₀ ... xₙ`, perform the following:
     - When `f x₀ ... xₙ` is a match expression
          match e₀, ..., eₙ with
          | p₍₀₎₍₁₎, ..., p₍₀₎₍ₙ₎ => t₀
            ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
       perform the following actions:
        - e'₀, ..., e'ₙ := [optimizer eᵢ | ∀ i ∈ [0..n]]
        - When some re ← reduceMatch? `match e'₀, ..., e'ₙ with ...`
            - return `some re`
        - Otherwise:
            - constMatchPropagation? `match e'₀, ..., e'ₙ with ...`
     - Otherwise:
         - return none

-/
def reduceMatchChoice?
  (f : Expr) (args : Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n l := f | return none
  let some mInfo ← getMatcherRecInfo? n l | return none
  let mut margs := args
  for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
     margs ← margs.modifyM i optimizer
  if let some r ← reduceMatch? (mkAppN f margs) then return r
  constMatchPropagation? f margs mInfo


/-- Given a `match` application expression of the form
     `f.match.n [p₁, ..., pₙ, d₁, ..., dₖ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`,
    perform the following actions:
     - params ← getImplicitParameters f #[p₁, ..., pₙ]
     - genericArgs := [params[i].effectiveArg | i ∈ [0..params.size-1] ∧ p.isGeneric]
     - appType ← inferType(λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → f p₁, ..., pₙ), with `α₁ : Type₁, ..., αₘ : Typeₘ = genericArgs`
     - return `g.match.n α₁ ..., αₘ d₁ ... dₖ pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁ ... pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ`
       only when `appType := λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → g.match.n q₁ ... qₕ` exists in match cache.
     - Otherwise, perform the following:
        - Add `appType := λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → f.match.n p₁ ... pₙ` in match cache
        - return `f.match.n p₁, ..., pₙ d₁ ... dₖ pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁ ... pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ`
    Where:
     - p₁, ..., pₙ: correspond to the arguments instantiating polymorphic params.
     - d₁, ..., dₖ: correspond to the match expresson discriminators
     - pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ: correspond to the rhs for each pattern matching.
-/
def structEqMatch? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
 let Expr.const n dlevel := f | return none
 let some mInfo ← getMatcherInfo? n | return none
 let i_args := args.take mInfo.getFirstDiscrPos
 let params ← getImplicitParameters f i_args
 let genericArgs := Array.filterMap (λ p => if p.isGeneric then some p.effectiveArg else none) params
 let auxApp ← mkLambdaFVars genericArgs (mkAppN f i_args)
 let cInfo ← getConstInfo n
 let matchFun ← instantiateValueLevelParams cInfo dlevel
 let auxAppType ← mkLambdaFVars genericArgs (Expr.beta matchFun i_args)
 let env ← get
 match env.optEnv.matchCache.get? auxAppType with
 | some gmatch =>
    let altArgs := args.extract mInfo.getFirstDiscrPos args.size
    mkAppExpr (gmatch.beta genericArgs) altArgs
 | none =>
    let optEnv := {env.optEnv with matchCache := env.optEnv.matchCache.insert auxAppType auxApp}
    set {env with optEnv := optEnv}
    mkAppExpr f args

end Solver.Optimize
