import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Rewriting.Utils

open Lean Meta Elab
namespace Solver.Optimize

mutual

private partial def isCstMatchPropAux (p : Expr) (k : Bool → TranslateEnvT Bool) : TranslateEnvT Bool := do
 if (← isConstructor p) then return (← k true)
 match ite? p with
   | some (_sort, _cond, _decide, e1, e2) =>
       isCstMatchPropAux e1 fun b =>
         if b then isCstMatchPropAux e2 k else return false
   | none =>
     match dite? p with
     | some (_sort, _cond, _decide, e1, e2) =>
         isCstMatchPropAux (← extractDependentITEExpr e1) fun b => do
           if b then isCstMatchPropAux (← extractDependentITEExpr e2) k
                else return false
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
    isCstMatchPropAux (getLambdaBody rhs[idx]!) fun b =>
      if b then isCstDiscrsProp rhs (idx - 1) k else return false
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
partial def isCstMatchProp (p : Expr) : TranslateEnvT Bool :=
  isCstMatchPropAux p (λ x => return x)

/-- Given `f x₁ ... xₙ` return `true` when the following conditions are satisfied:
     -  ∃ i ∈ [1..n], isExplicit xᵢ ∧
     -  ∀ i ∈ [1..n], isExplicit xᵢ → isCstMatchProp xᵢ ∨ isProp (← inferType xₓ) ∨ isFunType (← inferType xᵢ)
    NOTE: that constructors may contain free variables.
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
        if (← isCstMatchProp e <||> isProp t <||> isFunType t)
        then loop (i+1) true
        else pure false
      else loop (i+1) atLeastOneExplicit
    else pure atLeastOneExplicit
  loop 0

/-- call reduceMatcher? on m and return result only when match expression has been reduced.
    Otherwise none.
    Assume that m is a match expression.
-/
def reduceMatch? (m : Expr) : TranslateEnvT (Option Expr) := do
   match (← withReducible $ reduceMatcher? m) with
   | .reduced e => return e
   | _ => return none

/--  Given application `f x₀ ... xₙ`, perform the following:
     - When `f x₀ ... xₙ` is a match expression of the form
          match e₀, ..., eₙ with
          | p₍₀₎₍₁₎, ..., p₍₀₎₍ₙ₎ => t₀
            ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
        - return `reduceMatch (f x₀ ... xₙ)` only when `∀ i ∈ [0..n], isConstructor (← optimizer eᵢ)`.

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
     -- NOTE: reduceMatcher? simplifies match only when all the discriminators are constructors
     if !(← allMatchDiscrsAreCtor discrs) then return none
     let auxApp := mkAppN f margs
     reduceMatch? auxApp

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


/-- Apply the following constant propagation rules on match expressions, such that:
    Given  match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

    - When ∀ i [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               `eⱼ := if c then d₁ else d₂` ∧
                (i ≠ j → gᵢ = eᵢ) ∧ (i = j → gᵢ = d₁) ∧
                (i ≠ j → hᵢ = eᵢ) ∧ (i = j → hᵢ = d₂)
      Return
         `if c then match₁ g₁, ..., gₙ with ... else match₁ h₁, ..., hₙ with ...`

    - When ∀ i [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               `eⱼ := dite c (fun h : c => d₁) (fun h : ¬ c => d₂)`
                (i ≠ j → gᵢ = eᵢ) ∧ (i = j → gᵢ = d₁) ∧
                (i ≠ j → hᵢ = eᵢ) ∧ (i = j → hᵢ = d₂)
      Return
         `dite c (fun h : c => match₁ g₁, ..., gₙ with ...) (fun h : ¬ c => match₁ h₁, ..., hₙ with ...)`

    - When ∀ i [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               eⱼ := match₂ f₁, ..., fₙ with
                    | fp₍₁₎₍₁₎, ..., fp₍₁₎₍ₙ₎ => t₁
                    ...
                    | fp₍ₘ₎₍₁₎, ..., fp₍ₘ₎₍ₙ₎ => tₘ

               ∀ k ∈ [1..m],
                (i ≠ j → g₍ₖ₎₍ᵢ₎ = eᵢ) ∧ (i = j → g₍ₖ₎₍ᵢ₎ = tₖ)
       Return
         `match₂ f₁, ..., fₙ with
          | fp₍₁₎₍₁₎, ..., fp₍₁₎₍ₙ₎ =>
             match₁ g₍₁₎₍₁₎, ..., g₍₁₎₍ₙ₎ with ...
          ...
          | fp₍ₘ₎₍₁₎, ..., fp₍ₘ₎₍ₙ₎ =>
             match₁ g₍ₘ₎₍₁₎, ..., g₍ₘ₎₍ₙ₎ with ...`

-/
def constMatchPropagation? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n l := f | return none
  let some mInfo ← getMatcherRecInfo? n l | return none
  let discrs := args[mInfo.getFirstDiscrPos : mInfo.getFirstAltPos]
  if !(← allDiscrsAreCstMatch discrs) then return none
  if let some r ← iteCstProp? f args mInfo then return r
  if let some r ← diteCstProp? f args mInfo then return r
  if let some r ← matchCstProp? f args mInfo then return r
  return none

  where
    allDiscrsAreCstMatch (discrs : Subarray Expr) : TranslateEnvT Bool := do
      for i in [:discrs.size] do
        if !(← isCstMatchProp discrs[i]!) then return false
      return true

    /-- Implements ite over match rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if let some (_psort, pcond, pdecide, e1, e2) := ite? args[i]! then
          -- NOTE: we also need to cater for function as return type,
          -- i.e., match expression returns a function. Hence, extra arguments are now applied to ite.
          let margs := args.take mInfo.arity
          let extra_args := args.extract mInfo.arity args.size
          let e1' ← mkExpr (mkAppN f (margs.set! i e1)) (cacheResult := false)
          let e2' ← mkExpr (mkAppN f (margs.set! i e2)) (cacheResult := false)
          -- NOTE: we also need to set the sort type for the pulled ite meet
          -- the return type of the embedded match
          let retType ← inferType (mkAppN f margs)
          let iteExpr := mkApp5 (← mkIteOp) retType pcond pdecide e1' e2'
          if !extra_args.isEmpty
          then return mkAppN iteExpr extra_args
          else return iteExpr
      return none

    pushMatchInDIteExpr (f : Expr) (args : Array Expr) (idxDiscr : Nat) (ite_e : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      lambdaTelescope ite_e fun params body => do
        let body' ← mkExpr (mkAppN f (args.set! idxDiscr body)) (cacheResult := false)
        mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    /-- Implements dite over match rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if let some (_psort, pcond, pdecide, e1, e2) := dite? args[i]! then
          -- NOTE: we also need to cater for function as return type,
          -- i.e., match expression returns a function. Hence, extra arguments are now applied to dite.
          let margs := args.take mInfo.arity
          let extra_args := args.extract mInfo.arity args.size
          let e1' ← pushMatchInDIteExpr f margs i e1
          let e2' ← pushMatchInDIteExpr f margs i e2
          -- NOTE: we also need to set the sort type for the pulled ite meet
          -- the return type of the embedded match
          let retType ← inferType (mkAppN f margs)
          let diteExpr := mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2'
          if !extra_args.isEmpty
          then return mkAppN diteExpr extra_args
          return diteExpr
      return none

    isMatchArg? (e : Expr) : TranslateEnvT (Option (Expr × Array Expr × MatcherInfo)) := do
      Expr.withApp e fun pm pargs => do
        let Expr.const n l := pm | return none
        let some mInfo ← getMatcherRecInfo? n l | return none
        return (pm, pargs, mInfo)

    updateRhsWithMatch (f : Expr) (args : Array Expr) (idx : Nat) (rhs : Expr) : TranslateEnvT Expr := do
      -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
      -- that rhs can't be a function (i.e., only constant or ite or a match)
      lambdaTelescope rhs fun params body => do
        let body' ← mkExpr (mkAppN f (args.set! idx body)) (cacheResult := false)
        mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    updateReturnType (pType : Expr) (eType : Expr) : TranslateEnvT Expr := do
      lambdaTelescope pType fun params _body => do
        mkExpr (← mkLambdaFVars params eType) (cacheResult := false)

    /-- Implements match over match rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if let some (pm, pargs, minfo) ← isMatchArg? args[i]! then
          -- NOTE: we also need to cater for function as return type,
          -- i.e., match expression returns a function. Hence, extra arguments are now applied to pulled match.
          let margs := args.take mInfo.arity
          let extra_args := args.extract mInfo.arity args.size
          let mut pargs' := pargs
          let idxPType := minfo.getFirstDiscrPos - 1
          for k in [minfo.getFirstAltPos : minfo.arity] do
            pargs' := pargs'.set! k (← updateRhsWithMatch f margs i pargs[k]!)
            -- NOTE: we also need to set the return type for pulled over match
            -- to meet the return type of the embedded match.
            let retType ← inferType (mkAppN f margs)
            pargs' := pargs'.set! idxPType (← updateReturnType pargs[idxPType]! retType)
          let pMatchExpr := mkAppN pm pargs'
          if !extra_args.isEmpty
          then return mkAppN pMatchExpr extra_args
          return pMatchExpr
      return none


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
