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
 let (pm, args) := getAppFnWithArgs e
 let Expr.const n l := pm | return none
 let some mInfo ← getMatcherRecInfo? n l | return none
 let cInfo ← getConstInfo n
 let matchFun ← instantiateValueLevelParams cInfo l
 let instApp := Expr.beta matchFun (args.take mInfo.getFirstAltPos)
 return some { name := n, nameExpr := pm, args, instApp, mInfo}

mutual

private partial def isCstMatchPropAux (p : Expr) (k : Bool → TranslateEnvT Bool) : TranslateEnvT Bool := do
 if (← isConstructor p) then k true
 else
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
             let (f, args) := getAppFnWithArgs p
             if let Expr.const n l := f then
               if let some matcherInfo ← getMatcherRecInfo? n l then
                 let rhs := args[matcherInfo.getFirstAltPos : matcherInfo.arity]
                 -- NOTE: we also need to cater for function as return type,
                 -- i.e., match expression returns a function.
                 if args.size > matcherInfo.arity then return false
                 else isCstDiscrsProp rhs (rhs.size - 1) k
               else return false
             else return false

private partial def isCstDiscrsProp
  (rhs : Subarray Expr) (idx : Nat) (k : Bool → TranslateEnvT Bool) : TranslateEnvT Bool :=
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
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) (funPropagation := false) : TranslateEnvT Bool := do
  let stop := args.size
  let fInfo ← getFunInfoNArgs f stop
  let rec loop (i : Nat) (atLeastOneExplicit : Bool := false) : TranslateEnvT Bool := do
    if i < stop then
      let e := args[i]!
      let t ← inferType e
      let aInfo := fInfo.paramInfo[i]!
      if aInfo.isExplicit
      then
        let cstProp ← if funPropagation then isCstMatchProp e else isConstructor e
        if (← pure cstProp <||> isProp t <||> isFunType t)
        then loop (i+1) true
        else pure false
      else loop (i+1) atLeastOneExplicit
    else pure atLeastOneExplicit
  loop 0

/-- Given `m := f x₁ ... xₙ` with `f` corresponding to a match function
    and `mInfo` the corresponding matcher info, perform the following:
     - When `¬ allMatchDiscrsAreCtor x₁ ... xₙ minfo`:
          - return none
     - When `m := b` is already in the weak head cache
         - return `b`
     - Otherwise:
      - When .reduced e ← reduceMatcher? m
          - update cache with `m := some e`
          - return `some e`
      - Otherwise
          - update cache with `m := none`
          - return `none`
    Assume that `m` is a match expression.
-/
def reduceMatch? (f : Expr) (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) := do
   if !(← allMatchDiscrsAreCtor args) then return none
   let m := mkAppN f args
   match (← get).optEnv.whnfCache.get? m with
   | some b => return b
   | none =>
       let res ← tryReduction? f args
       modify (fun env => { env with optEnv.whnfCache := env.optEnv.whnfCache.insert m res})
       return res

   where

    allMatchDiscrsAreCtor (args : Array Expr) : TranslateEnvT Bool := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if !(← isConstructor args[i]!) then return false
      return true

    commonMatchReduction?
      (auxApp : Expr) (args : Array Expr) (hs : Array Expr) : TranslateEnvT (Option Expr) := do
        let auxApp ← whnf (mkAppN auxApp hs)
        let auxAppFn := auxApp.getAppFn
        let mut idx := mInfo.getFirstAltPos
        for h in hs do
          if auxAppFn == h then
            let result := mkAppN args[idx]! auxApp.getAppArgs
            let result := mkAppN result (args.extract (mInfo.getFirstAltPos + mInfo.numAlts) args.size)
            return result.headBeta
          idx := idx + 1
        return none

    tryReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      -- NOTE: simplifies match only when all the discriminators are constructors
      let Expr.const n dlevel := f | return none
      let cInfo ← getConstInfo n
      let matchFun ← instantiateValueLevelParams cInfo dlevel
      let auxApp := mkAppN matchFun (args.take mInfo.getFirstAltPos)
      if (isCasesOnRecursor (← getEnv) n) then
        lambdaBoundedTelescope auxApp mInfo.numAlts fun hs _t =>
          commonMatchReduction? auxApp args hs
      else
        forallBoundedTelescope (← inferType auxApp) mInfo.numAlts fun hs _t =>
          commonMatchReduction? auxApp args hs

/-- Given `pType := λ α₁ → .. → λ αₙ → t` returns `λ α₁ → .. → λ αₙ → eType`
    This function is expected to be used only when updating a match return type
-/
def updateMatchReturnType (eType : Expr) (pType : Expr) : TranslateEnvT Expr := do
  lambdaTelescope pType fun params _body => mkLambdaFVars params eType

mutual

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
private partial def constMatchPropagation?
  (cm : Expr) (cargs : Array Expr) (mInfo : MatcherInfo)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if !(← allDiscrsAreCstMatch cargs mInfo) then k none
  else constMatchArgsPropagation? cm cargs mInfo mInfo.getFirstDiscrPos k

  where
    allDiscrsAreCstMatch (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT Bool := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if !(← isCstMatchProp args[i]!) then return false
      return true

private partial def constMatchArgsPropagation?
  (cm : Expr) (cargs : Array Expr) (mInfo : MatcherInfo) (idx : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if idx ≥ mInfo.getFirstAltPos then k none
  else
   iteCstProp? cm cargs idx mInfo fun ite_r =>
     match ite_r with
     | some _ => k ite_r
     | none =>
        diteCstProp? cm cargs idx mInfo fun dite_r =>
          match dite_r with
          | some _ => k dite_r
          | none =>
             matchCstProp? cm cargs idx mInfo fun match_r =>
              match match_r with
              | some _ => k match_r
              | none => constMatchArgsPropagation? cm cargs mInfo (idx + 1) k

/-- Implements ite over match rule -/
 private partial def iteCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArg]! then
    -- NOTE: we also need to cater for function as return type,
    -- i.e., match expression returns a function. Hence, extra arguments are now applied to ite.
    let margs := args.take mInfo.arity
    let extra_args := args.extract mInfo.arity args.size
    tryMatchReduction (mkAppN f (margs.set! idxArg e1)) mInfo fun e1_r =>
      match e1_r with
      | none => throwEnvError "iteCstProp?: unreachable case 1 !!!"
      | some e1' => do
         tryMatchReduction (mkAppN f (margs.set! idxArg e2)) mInfo fun e2_r =>
           match e2_r with
           | none => throwEnvError "iteCstProp?: unreachable case 2 !!!"
           | some e2' => do
              -- NOTE: we also need to set the sort type for the pulled ite to meet
              -- the return type of the embedded match
             let retType ← inferType (mkAppN f margs)
             let iteExpr := mkApp5 (← mkIteOp) retType pcond pdecide e1' e2'
             if !extra_args.isEmpty
             then k (some (mkAppN iteExpr extra_args))
             else k (some iteExpr)
  else k none


/-- Implements dite over match rule -/
 private partial def diteCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArg]! then
    -- NOTE: we also need to cater for function as return type,
    -- i.e., match expression returns a function. Hence, extra arguments are now applied to dite.
    let margs := args.take mInfo.arity
    let extra_args := args.extract mInfo.arity args.size
    pushMatchInDIteExpr f margs idxArg e1 mInfo fun e1_r =>
      match e1_r with
      | none => throwEnvError "diteCstProp?: unreacchable case 1 !!!"
      | some e1' => do
         pushMatchInDIteExpr f margs idxArg e2 mInfo fun e2_r =>
           match e2_r with
           | none => throwEnvError "diteCstProp?: unreacchable case 2 !!!"
           | some e2' => do
              -- NOTE: we also need to set the sort type for the pulled dite to meet
              -- the return type of the embedded match
              let retType ← inferType (mkAppN f margs)
              let diteExpr := mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2'
              if !extra_args.isEmpty
              then k (some (mkAppN diteExpr extra_args))
              else k (some diteExpr)
  else k none

 private partial def pushMatchInDIteExpr
  (f : Expr) (args : Array Expr) (idxDiscr : Nat) (ite_e : Expr)
  (mInfo : MatcherInfo) (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
  -- that then/else expression can't be a function or even quantified function
  -- (i.e., only constant or ite or a match)
  -- Anyway, we can't pattern match on a function
  lambdaTelescope ite_e fun params body => do
    tryMatchReduction (mkAppN f (args.set! idxDiscr body)) mInfo fun body_r => do
      match body_r with
      | none => throwEnvError "pushMatchInDIteExpr: unreachable case !!!"
      | some body' =>
          k (some (← mkLambdaFVars params body'))


 private partial def updateRhsWithMatch
  (f : Expr) (args : Array Expr) (idx : Nat) (rhs : Expr)
  (mInfo : MatcherInfo) (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  -- NOTE: here we can telescope as condition `allDiscrsAreCstMatch` guarantees
  -- that rhs can't be a function (i.e., only constant or ite or a match)
  -- Anyway, we can't pattern match on a function
  lambdaTelescope rhs fun params body => do
    tryMatchReduction (mkAppN f (args.set! idx body)) mInfo fun body_r => do
      match body_r with
      | none => throwEnvError "updateRhsWithMatch: unreachable case !!!"
      | some body' =>
         k (some (← mkLambdaFVars params body'))


/-- Implements match over match rule -/
 private partial def matchCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let some argInfo ← isMatchArg? args[idxArg]! then
     -- NOTE: we also need to cater for function as return type,
     -- i.e., match expression returns a function. Hence, extra arguments are now applied to pulled match.
     let margs := args.take mInfo.arity
     let extra_args := args.extract mInfo.arity args.size
     matchCstPropAux f margs extra_args idxArg mInfo argInfo argInfo.args argInfo.mInfo.getFirstAltPos k
  else k none

private partial def matchCstPropAux
  (f : Expr) (margs : Array Expr) (extra_args : Array Expr) (idxArg : Nat) (mInfo : MatcherInfo)
  (argInfo : MatchInfo) (pargs : Array Expr) (idx : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if idx ≥ argInfo.mInfo.arity then
    -- NOTE: we also need to set the return type for pulled over match
    -- to meet the return type of the embedded match.
    let idxType := argInfo.mInfo.getFirstDiscrPos - 1
    let retType ← inferType (mkAppN f margs)
    let pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
    let pMatchExpr := mkAppN argInfo.nameExpr pargs
    if !extra_args.isEmpty
    then k (some (mkAppN pMatchExpr extra_args))
    else k (some pMatchExpr)
  else
    updateRhsWithMatch f margs idxArg argInfo.args[idx]! mInfo fun rhs_r =>
      match rhs_r with
      | none => throwEnvError "matchCstPropAux: unreachable case !!!"
      | some rhs' =>
          matchCstPropAux f margs extra_args idxArg mInfo argInfo (pargs.set! idx rhs') (idx + 1) k

/-- try to successively call reduceMatch? and constMatchPropagation? on `m`.
    Assumes that `m` is a match expression.
-/
private partial def tryMatchReduction
  (m : Expr) (mInfo : MatcherInfo)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  let (f, args) := getAppFnWithArgs m
  match (← reduceMatch? f args mInfo) with
  | none =>
      constMatchPropagation? f args mInfo fun m_r =>
        match m_r with
        | none => k m
        | re => k re
  | re => k re

end

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
  if let some r ← reduceMatch? f margs mInfo then return r
  constMatchPropagation? f margs mInfo (λ x => return x)


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
 match (← get).optEnv.matchCache.get? auxAppType with
 | some gmatch =>
    let altArgs := args.extract mInfo.getFirstDiscrPos args.size
    mkAppExpr (gmatch.beta genericArgs) altArgs
 | none =>
    modify (fun env => { env with optEnv.matchCache := env.optEnv.matchCache.insert auxAppType auxApp })
    mkAppExpr f args

end Solver.Optimize
