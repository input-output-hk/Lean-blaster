import Lean
import Solver.Optimize.OptimizeStack
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Telescope

open Lean Meta Elab
namespace Solver.Optimize

private partial def isCstMatchPropAux (stack : List Expr) : TranslateEnvT Bool := do
  match stack with
  | [] => return true
  | p :: xs =>
    if (← isConstructor p) then isCstMatchPropAux xs
    else
     match ite? p with
     | some (_sort, _cond, _decide, e1, e2) => isCstMatchPropAux (e1 :: e2 :: xs)
     | none =>
         match dite? p with
         | some (_sort, _cond, _decide, e1, e2) =>
              isCstMatchPropAux ((← extractDependentITEExpr e1) :: (← extractDependentITEExpr e2) :: xs)
         | none =>
             let (f, args) := getAppFnWithArgs p
             let some mInfo ← isMatcher? f | return false
             -- NOTE: we also need to cater for function as return type,
             -- i.e., match expression returns a function.
             if args.size > mInfo.arity then return false
             isCstMatchPropAux (updateStackWithMatchRhs mInfo args xs mInfo.getFirstAltPos)

  where
    updateStackWithMatchRhs
      (mInfo : MatchInfo) (args : Array Expr)
      (stack : List Expr) (idx : Nat) : List Expr :=
      if idx >= mInfo.arity then stack
      else updateStackWithMatchRhs mInfo args (getLambdaBody args[idx]! :: stack) (idx + 1)

/--  Return `true` only when
      isConstructor p ∨g
      ( p := if c then e₁ else e₂ ∧ isCstMatchProp e₁ ∧ isCstMatchProp e₂ ) ∨
      ( p := dite c (fun h : c => e₁) (fun h : ¬ c => e₂) ∧ isCstMatchProp e₁ ∧ isCstMatchProp e₂ ) ∨
      ( p := match e₁, ..., eₙ with
              | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
              ...
              | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ
        ∧ ∀ i ∈ [1..m], isCstMatchProp t₁ )
-/
@[always_inline, inline]
  def isCstMatchProp (p : Expr) : TranslateEnvT Bool := do
    match (← get).optEnv.memCache.isCstMatchPropCache.get? p with
    | some b => return b
    | none =>
        let b ← isCstMatchPropAux [p]
        modify (fun env => { env with optEnv.memCache.isCstMatchPropCache :=
                                      env.optEnv.memCache.isCstMatchPropCache.insert p b})
        return b

/-- Given `f x₁ ... xₙ` return `true` when the following conditions are satisfied:
     -  ∃ i ∈ [1..n], isExplicit xᵢ ∧
     -  ∀ i ∈ [1..n], isExplicit xᵢ → isCstProp xᵢ ∨ isPropFunType f xₓ
     with
       - isCstProp e := isCstMatchProp e IF funpropagaton
         isCstProp e := isConstructor e  Otherwise
       - isPropFunType e := isProp e.Type ∨ isFunType e.Type
    NOTE: constructors may contain free variables.
-/
def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) (funPropagation := false) : TranslateEnvT Bool := do
  let pInfo ← getFunEnvInfo f
  let argsType := getForallBinderTypes (inferFunType pInfo.type args)
  let rec loop (i : Nat) (stop : Nat) (atLeastOneExplicitCstr : Bool := false) : TranslateEnvT Bool := do
    if i < stop then
      let e := args[i]!
      let p := pInfo.paramsInfo[i]!
      if i < pInfo.paramsInfo.size then
        if p.isExplicit
        then
          let cstProp ← if funPropagation then isCstMatchProp e else isConstructor e
          if (← pure cstProp <||> isPropFunType p argsType[i]!)
          then loop (i+1) stop (atLeastOneExplicitCstr || cstProp)
          else return false
        else loop (i+1) stop atLeastOneExplicitCstr
      else return atLeastOneExplicitCstr
    else return atLeastOneExplicitCstr
  loop 0 args.size

  where
    @[always_inline, inline]
    isPropFunType (p : ParamInfo) (t : Expr) : TranslateEnvT Bool := do
     if p.isProp then return true
     else isFunType t

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
def reduceMatch? (f : Expr) (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Option Expr) := do
 if !(← allMatchDiscrsAreCtor args mInfo.getFirstDiscrPos mInfo.getFirstAltPos) then return none
 let m := mkAppN f args
 match (← get).optEnv.whnfCache.get? m with
 | some b => return b
 | none =>
     let res ← tryReduction? args
     modify (fun env => { env with optEnv.whnfCache := env.optEnv.whnfCache.insert m res})
     return res

   where

    allMatchDiscrsAreCtor (args : Array Expr) (idx : Nat) (stop : Nat) : TranslateEnvT Bool := do
     if idx ≥ stop then return true
     else if !(← isConstructor args[idx]!) then return false
     else allMatchDiscrsAreCtor args (idx + 1) stop

    @[always_inline, inline]
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

    tryReduction? (args : Array Expr) : TranslateEnvT (Option Expr) := do
      -- NOTE: simplifies match only when all the discriminators are constructors
      let auxApp := betaLambda mInfo.instApp (args.take mInfo.getFirstAltPos)
      lambdaBoundedTelescope auxApp mInfo.numAlts fun hs _t =>
         commonMatchReduction? auxApp args hs

/-- Given `pType := λ α₁ → .. → λ αₙ → t` returns `λ α₁ → .. → λ αₙ → eType`
    This function is expected to be used only when updating a match return type
-/
def updateMatchReturnType (eType : Expr) (pType : Expr) : TranslateEnvT Expr := do
  lambdaTelescope pType fun params _body => mkLambdaFVars params eType

/-- Apply the following constant propagation rules on match expressions, such that:
    Given match₁ e₁, ..., eₙ with
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
  (cm : Expr) (cargs : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Option Expr) := withLocalContext $ do
  if !(← allDiscrsAreCstMatch mInfo.getFirstDiscrPos mInfo.getFirstAltPos)
  then return none
  else loop mInfo.getFirstDiscrPos mInfo.getFirstAltPos

  where
    loop (idx : Nat) (stop : Nat) : TranslateEnvT (Option Expr) := do
      if idx ≥ stop then return none
      else if let some r ← isIteArg idx then return r
      else if let some r ← isDiteArg idx then return r
      else if let some r ← isMatchArg idx then return r
      else loop (idx + 1) stop

    allDiscrsAreCstMatch (idx : Nat) (stop : Nat) : TranslateEnvT Bool := do
      if idx ≥ stop then return true
      else if !(← isCstMatchProp cargs[idx]!) then return false
      else allDiscrsAreCstMatch (idx + 1) stop


    @[always_inline, inline]
    isIteArg (idx : Nat) : TranslateEnvT (Option Expr) := do
      if let some (_psort, pcond, pdecide, e1, e2) := ite? cargs[idx]! then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to ite.
        let margs := cargs.take mInfo.arity
        let extra_args := cargs.extract mInfo.arity cargs.size
        -- NOTE: we also need to set the sort type for the pulled ite to meet
        -- the return type of the embedded match
        let retType := getLambdaBody margs[mInfo.getFirstDiscrPos - 1]!
        let e1_args := margs.set! idx e1
        let e1' := Option.getD (← reduceMatch? cm e1_args mInfo) (mkAppN cm e1_args)
        let e2_args := margs.set! idx e2
        let e2' := Option.getD (← reduceMatch? cm e2_args mInfo) (mkAppN cm e2_args)
        let iteExpr := mkApp5 (← mkIteOp) retType pcond pdecide e1' e2'
        if extra_args.isEmpty
        then return iteExpr
        else return mkAppN iteExpr extra_args
      else return none

    pushMatchInLambda (f : Expr) (args : Array Expr) (idxDiscr : Nat) (e : Expr) : TranslateEnvT Expr := do
       lambdaTelescope e fun xs b => do
         -- we can safely telescope as allDiscrsAreCstMatch guarantees dite and match are not functions
         let args := args.set! idxDiscr b
         let body' := Option.getD (← reduceMatch? f args mInfo) (mkAppN f args)
         mkLambdaFVars xs body'

    @[always_inline, inline]
    isDiteArg (idx : Nat) : TranslateEnvT (Option Expr) := do
      if let some (_psort, pcond, pdecide, e1, e2) := dite? cargs[idx]! then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to dite.
        let margs := cargs.take mInfo.arity
        let extra_args := cargs.extract mInfo.arity cargs.size
        -- NOTE: we also need to set the sort type for the pulled dite to meet
        -- the return type of the embedded match
        let retType := getLambdaBody margs[mInfo.getFirstDiscrPos - 1]!
        let e1' ← pushMatchInLambda cm margs idx e1
        let e2' ← pushMatchInLambda cm margs idx e2
        let diteExpr := mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2'
        if extra_args.isEmpty
        then return diteExpr
        else return mkAppN diteExpr extra_args
      else return none

    @[always_inline, inline]
    isMatchArg (idx : Nat) : TranslateEnvT (Option Expr) := do
      let (f, args) := getAppFnWithArgs cargs[idx]!
      if let some argInfo ← isMatcher? f then
        -- NOTE: we also need to cater for function as return type,
        -- i.e., match expression returns a function. Hence, extra arguments are now applied to pulled match.
        let margs := cargs.take mInfo.arity
        let extra_args := cargs.extract mInfo.arity cargs.size
        let mut pargs := args
        for i in [argInfo.getFirstAltPos : argInfo.arity] do
          pargs ← pargs.modifyM i (pushMatchInLambda cm margs idx)
        -- NOTE: we also need to set the return type for pulled over match
        -- to meet the return type of the embedded match.
        let idxType := argInfo.getFirstDiscrPos - 1
        let retType := getLambdaBody margs[mInfo.getFirstDiscrPos - 1]!
        pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
        let pMatchExpr := mkAppN argInfo.nameExpr pargs
        if extra_args.isEmpty
        then return pMatchExpr
        else return mkAppN pMatchExpr extra_args
      else return none

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
  (s : OptimizeStack) (xs : List OptimizeStack) : TranslateEnvT (Option OptimizeContinuity) := do
  match s with
  | .InitMatchChoiceExpr f args fInfo startArgIdx =>
       if let some mInfo ← isMatcher? f then
         let startIdx := mInfo.getFirstDiscrPos
         return some $ Sum.inl (.MatchChoiceOptimizeDiscrs f args fInfo startArgIdx startIdx mInfo :: xs)
       else return none

  | .MatchChoiceReduce f args _fInfo _startArgIdx mInfo =>
       if let some r ← withLocalContext $ do reduceMatch? f args mInfo then
         -- trace[Optimize.matchConstPropagation] "match constant propagation {reprStr f} {reprStr args} => {reprStr r}"
         return some $ Sum.inl (.InitOptimizeExpr r :: xs)
       else
         match (← constMatchPropagation? f args mInfo) with
         | some e =>
            -- trace[Optimize.matchConstPropagation] "match constant propagation {reprStr f} {reprStr args} => {reprStr e}"
            return some $ Sum.inl (.InitOptimizeExpr e :: xs)
         | none => return none

  | _ => throwEnvError "reducMatchChoice?: unexpected continuity {reprStr s} !!!"


@[always_inline, inline]
private def addPatternInContext
  (h : MatchContextMap) (discr : Expr)
  (pattern : Expr) (altArgs : Option (Array Expr)) : MatchContextMap :=
  match h.get? discr with
  | none => h.insert discr (Std.HashMap.emptyWithCapacity.insert pattern (mkMatchEntry altArgs))
  | some pMap => h.insert discr (pMap.insert pattern (mkMatchEntry altArgs))

 where
   mkMatchEntry (altArgs : Option (Array Expr)) : MatchEntry :=
    match altArgs with
    | none => .NotEqPattern
    | some args => .EqPattern args

def isFVarPattern (e : Expr) : Bool :=
 match e with
 | Expr.fvar .. => true
 | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) _n) pe) _h => isFVarPattern pe
 | _ => false

/-- Given match info `mInfo` and `args` the arguments of a match expression of the form:
      match₁ e₁, ..., eₙ with
      | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
        ...
      | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

    Given `rhs` the current match alternative to be optimized, i.e., `p₍ᵢ₎₍₁₎, ..., p₍₁₎₍ₙ₎ => tᵢ` and
    `altIdx` its index in `args`, perform the following actions:
      - let h := (← get).optEnv.options.matchInContext
      - let h1 := h ∪ [ eⱼ := pmᵢ ∪ p₍ᵢ₎₍ⱼ₎ := EqPattern (retrieveAltsArgs #[p₍ᵢ₎₍ⱼ₎]) | j ∈ [1..n] ∧ (h[eⱼ]? = some pmᵢ ∨ pmᵢ = []) ]
      - let h2 := h1 ∪ [ eⱼ := pmⱼ ∪ p₍ₖ₎₍ⱼ₎ := NotEqPattern |
                         k ∈ [1..i-1] ∧ ∃! j ∈ [1..n], (h1[eⱼ]? = some pmᵢ ∨ pmᵢ = []) ∧ ¬ isFVarPattern p₍ₖ₎₍ⱼ₎ ]
      - let se₁ ... seₚ := [eⱼ | j ∈ [1..n] ∧ isFVar p₍ᵢ₎₍ⱼ₎ ]
      - let sp₁ ... spₚ := [p₍ᵢ₎₍ⱼ₎ | j ∈ [1..n] ∧ isFVar p₍ᵢ₎₍ⱼ₎ ]
      - withMatchContext h2 $ optimizer tᵢ[sp₁/seᵢ] ... [spₚ/seₚ]
-/
@[always_inline, inline]
def optimizeMatchAlt
  (s : OptimizeStack) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
 match s with
 | .InitOptimizeMatchAlt args minfo altIdx rhs =>
      -- optimizing lambda params for rhs first
      match rhs with
      | Expr.lam n t b bi =>
           let typeOpt := .InitOptimizeExpr t
           let lamWait := .MatchRhsLambdaWaitForType n bi b
           return Sum.inl (typeOpt :: lamWait :: .MatchAltWaitForParamsRhs args minfo altIdx :: stack)
      | _ => return Sum.inl (.MatchAltOptimize args minfo altIdx rhs :: stack)

 | .MatchAltOptimize args mInfo altIdx rhs =>
     let currIdx := altIdx - mInfo.getFirstAltPos
     withLocalContext $ do
       let alts := getMatchAlts args mInfo
       let h ← addNotEqPatternToContext args mInfo alts (← get).optEnv.matchInContext 0 currIdx
       forallTelescope alts[currIdx]! fun xs b => do
       let lhs := b.getAppArgs
       lambdaBoundedTelescope rhs (max 1 (← retrieveAltsArgs lhs).altArgs.size) fun params body => do
         let mut mcontext := h
         let mut idxParams := 0
         let mut body := body
         for j in mInfo.getDiscrRange do
           let idxLhs := j - mInfo.getFirstDiscrPos
           let pattern := lhs[idxLhs]!
           let nextIdx := idxParams + (← retrieveAltsArgs #[pattern]).altArgs.size
           if !isFVarPattern pattern then
             -- add EqPattern in match context only when it's a constructor
             let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
             mcontext := addPatternInContext mcontext args[j]! patternExpr (some $ params.extract idxParams nextIdx)
           if pattern.isFVar then
             -- pattern should only be an fvar (i.e., not even a named pattern alias of an fvar
             body := Expr.replaceFVar body params[idxParams]! args[j]!
           idxParams := nextIdx
         let matchCtx ← mkMatchStackContext mcontext
         let lctx ← mkLocalDeclStackContext (← mkLocalContext)
         let bodyOpt := .InitOptimizeExpr body
         let altWait := .MatchAltWaitForExpr params :: .LocalDeclWaitForExpr lctx :: stack
         return Sum.inl (bodyOpt :: .MatchContextWaitForExpr matchCtx :: altWait)

 | _ => throwEnvError "reducMatchChoice?: unexpected continuity {reprStr s} !!!"


  where
   onlyOnePattern (lhs : Array Expr) (idx : Nat) (onlyOne : Bool) : TranslateEnvT Bool := do
     if h : idx ≥ lhs.size then return onlyOne
     else if !isFVarPattern lhs[idx] then
          if !onlyOne then onlyOnePattern lhs (idx + 1) true
          else return false
     else onlyOnePattern lhs (idx + 1) onlyOne

   updateNotEqContext
     (h : MatchContextMap) (idx : Nat) (start : Nat) (stop : Nat)
     (args : Array Expr) (lhs : Array Expr) (xs : Array Expr) : TranslateEnvT MatchContextMap := do
     if idx ≥ stop then return h
     else
       let pattern := lhs[idx - start]!
       if !isFVarPattern pattern then
          -- add NotEqPattern in match context only when it's a constructor
         let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
         updateNotEqContext (addPatternInContext h args[idx]! patternExpr none) (idx + 1) start stop args lhs xs
       else updateNotEqContext h (idx + 1) start stop args lhs xs

   addNotEqPatternToContext
     (args : Array Expr) (mInfo : MatchInfo) (alts : Array Expr) (h : MatchContextMap) (idx : Nat)
     (stopIdx : Nat) : TranslateEnvT MatchContextMap := do
     if idx ≥ stopIdx then return h
     else
       let h' ←
         forallTelescope alts[idx]! fun xs b => do
           let lhs := b.getAppArgs
           if ← onlyOnePattern lhs 0 false then
             -- add NotEqPattern when there is only one pattern that is a constructor
             updateNotEqContext h mInfo.getFirstDiscrPos mInfo.getFirstDiscrPos mInfo.getFirstAltPos args lhs xs
           else return h
       addNotEqPatternToContext args mInfo alts h' (idx + 1) stopIdx

/--  Apply the following reduction rules, such that:
     Given match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

     - When ∀ i ∈ [1..m], ¬ tᵢ.hasLooseBVars ∧ tᵢ = t₁
         - return `some t₁`

     - When ∃ i ∈ [1..m],
             ∀ j ∈ [1..n],
               eⱼ := pm ∈ matchInContext ∧ p₍ᵢ₎₍ⱼ₎ := EqPattern altArgs ∈ pm ∧ ¬ isFVarPattern p₍ᵢ₎₍ⱼ₎
          - return `some tᵢ`

     - When ∀ j ∈ [1..n], isFVar p₍ₘ₎₍ⱼ₎ ∧
            ∀ k ∈ [1..m-1],
              ∃ h ∈ [1..n],
                  ( eₕ := pm ∈ matchInContext ∧ p₍ₖ₎₍ₕ₎ := NotEqPattern ∈ pm )
           - return `some tₘ`

     - Otherwise:
         - return none
-/
def elimMatch?
  (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if let some re ← commonRhs? mInfo args then return re
  if let some re ← matchInHyps? mInfo args then return re
  lastPatternReduction? mInfo args

where

  @[always_inline, inline]
  commonRhs? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
    let firstRhs := getLambdaBody args[mInfo.getFirstAltPos]!
    -- Rhs can't be a function with loose BVars.
    if firstRhs.hasLooseBVars then return none
    for i in [mInfo.getFirstAltPos + 1 : mInfo.arity] do
      -- NOTE: No need to check for looseBVars as we are expecting equality
      if !(← exprEq (getLambdaBody args[i]!) firstRhs) then return none
    return firstRhs

  @[always_inline, inline]
  allPatternsInHyp
    (mInfo : MatchInfo) (args : Array Expr)
    (alt : Expr) (h : MatchContextMap) : TranslateEnvT (Bool × Array Expr) := do
    forallTelescope alt fun xs b => do
      let lhs := b.getAppArgs
      let mut patternArgs := #[]
      for j in mInfo.getDiscrRange do
        let idxLhs := j - mInfo.getFirstDiscrPos
        let pattern := lhs[idxLhs]!
        if isFVarPattern pattern then return (false, #[])
        let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
        match h.get? args[j]! with
        | none => return (false, #[])
        | some pm =>
           match pm.get? patternExpr with
           | some (.EqPattern altArgs) =>
               patternArgs := patternArgs ++ altArgs
           | _ => return (false, #[])
      return (true, patternArgs)

  @[always_inline, inline]
  matchInHyps? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
    let h := (← get).optEnv.matchInContext
    let alts := getMatchAlts args mInfo
    for i in [mInfo.getFirstAltPos : mInfo.arity] do
      let altIdx := i - mInfo.getFirstAltPos
      let (inContext, altArgs) ← allPatternsInHyp mInfo args alts[altIdx]! h
      if inContext then
        setRestart
        if altArgs.isEmpty
        then return getLambdaBody args[i]! -- case when there is no free variables in pattern.
        else return args[i]!.beta altArgs
    return none

  @[always_inline, inline]
  allFVarsPatterns (alt : Expr) : TranslateEnvT Bool := do
    -- NOTE: we avoid performing forallTelescope at this stage
    let lhs := alt.getForallBody.getAppArgs
    for h : i in [:lhs.size] do
      if !lhs[i].isBVar then
        return false
     return true

  @[always_inline, inline]
  existsNotEqPattern
    (mInfo : MatchInfo) (args : Array Expr)
    (alt : Expr) (h : MatchContextMap) : TranslateEnvT Bool := do
    forallTelescope alt fun xs b => do
      let lhs := b.getAppArgs
      for j in mInfo.getDiscrRange do
        let idxLhs := j - mInfo.getFirstDiscrPos
        let pattern := lhs[idxLhs]!
        if !isFVarPattern pattern then
          let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
          if let some pm := h.get? args[j]! then
            if let some .NotEqPattern := pm.get? patternExpr then return true
      return false

  @[always_inline, inline]
  lastPatternReduction? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let h := (← get).optEnv.matchInContext
     let alts := getMatchAlts args mInfo
     -- all last patterns are FVars
     if (← allFVarsPatterns alts[alts.size - 1]!) then
       for i in [:alts.size - 1] do
         if !(← existsNotEqPattern mInfo args alts[i]! h) then
           return none
       let discrs := args.extract mInfo.getFirstDiscrPos mInfo.getFirstAltPos
       setRestart
       return args[mInfo.arity - 1]!.beta discrs
     else return none


/-- Given a `match` application expression of the form
     `f.match_n #[p₁, ..., pₙ, rt, d₁, ..., dₖ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`,
    perform the following actions:
     - params ← getImplicitParameters f #[p₁, ..., pₙ]
     - let genFVars ← retrieveGenericFVars params
     - appType ← genericMatchType (λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → mInfo.instApp p₁, ..., pₙ, rt),
             with `α₁ : Type₁, ..., αₘ : Typeₘ = genFVars`
     - return `g.match.n α₁ ..., αₘ, rt, d₁ ... dₖ pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁ ... pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ`
       only when `appType := λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → g.match.n q₁ ... qₕ` exists in match cache.
     - Otherwise, perform the following:
        - Add `appType := λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → f.match.n p₁ ... pₙ` in match cache
        - return `f.match.n p₁, ..., pₙ, rt, d₁ ... dₖ pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁ ... pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ`
    Where:
     - p₁, ..., pₙ: correspond to the arguments instantiating polymorphic params.
     - rt : correspond to the match expression's return type
     - d₁, ..., dₖ: correspond to the match expresson discriminators
     - pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ: correspond to the rhs for each pattern matching.
-/
def structEqMatch
  (f : Expr) (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Expr × Array Expr) := do
  if mInfo.isCasesOn then
     return (f, args)
  else
    let i_args := args.take mInfo.getFirstDiscrPos
    let params ← getImplicitParameters f i_args
    let genFVars ← retrieveGenericFVars params
    let auxAppType ← genericMatchType genFVars (Expr.beta mInfo.instApp i_args)
    -- trace[Optimize.structEqMatch] "application type for {reprStr f} got {reprStr auxAppType}"
    match (← get).optEnv.matchCache.get? auxAppType with
    | some gmatch =>
        let altArgs := args.extract (mInfo.getFirstDiscrPos - 1) args.size
        let (f', extraArgs)  := getAppFnWithArgs (gmatch.beta genFVars)
        -- trace[Optimize.structEqMatch] "equivalence detected {reprStr f} ==> {reprStr f'}"
        return (f', extraArgs ++ altArgs)
    | none =>
        -- trace[Optimize.structEqMatch] "no equivalence for {reprStr f}"
        let auxApp ← mkLambdaFVars genFVars (mkAppN f (args.take (mInfo.getFirstDiscrPos - 1)))
        -- trace[Optimize.structEqMatch] "generic application for {reprStr f} got {reprStr auxApp}"
        modify (fun env => { env with optEnv.matchCache := env.optEnv.matchCache.insert auxAppType auxApp })
        return (f, args)

  where
    genericMatchType (genFVars : Array Expr) (e : Expr) : TranslateEnvT Expr := do
      lambdaTelescope e fun fvars _ => do
        mkForallFVars (genFVars ++ fvars) (← mkPropType)

/-- Apply simplification and normalization rules on match expressions.
    Assumes that `f x₁ ... xₙ` is a match application
-/
@[always_inline, inline]
def optimizeMatch
  (f : Expr) (args : Array Expr) (mInfo : MatchInfo) (xs : List OptimizeStack) :
  TranslateEnvT OptimizeContinuity := withLocalContext $ do
 -- check for match elimination rules first
 if let some r ← elimMatch? mInfo args then return (← stackContinuity xs r)
 -- check for match equivalence afterwards
 let (f', args') ← structEqMatch f args mInfo
 let some mInfo' ← isMatcher? f' |
   throwEnvError "MatchInfo expected for {reprStr f'} previous {reprStr f}!!!"
 --  normalize match expression to ite
 match (← normMatchExpr? args' mInfo') with
 | some mdef =>
    -- trace[Optimize.normMatch] "normalizing match to ite {reprStr f'} {reprStr args'} => {reprStr mdef}"
    return Sum.inl (.InitOptimizeExpr mdef :: xs)
 | _ => return (← stackContinuity xs (← mkAppExpr f' args'))


initialize
  registerTraceClass `Optimize.matchConstPropagation
  registerTraceClass `Optimize.structEqMatch
  registerTraceClass `Optimize.normMatch

end Solver.Optimize
