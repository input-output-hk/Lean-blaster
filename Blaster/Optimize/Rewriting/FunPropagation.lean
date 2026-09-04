import Lean
import Blaster.Optimize.Rewriting.NormalizeMatch
import Blaster.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab
namespace Blaster.Optimize

/-- Given application `f x₁ ... xₙ`, apply the following normalization rules:
     - When `f := Blaster.dite' c (fun h : c => t₁) (fun h : ¬ c => t₂)`
       Return
         Blaster.dite' c (fun h : c => t₁ x₁ ... xₙ) (fun h : ¬ c => t₂ x₁ ... xₙ)

     - When `f := match₁ e₁, ..., eₙ with
                  | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
                  ...
                  | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ`
       Return
         match₁ e₁, ..., eₙ with
         | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁ x₁ ... xₙ
         ...
         | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ x₁ ... xₙ
-/
def normChoiceApplication?
  (f : Expr) (args : Array Expr) (prevInApp : Bool) : TranslateEnvT (Option OptimizeStack) := do
    if let some r ← normDIteApp? f args then return r
    normMatchApp? f args

  where
    mkAppInDIteExpr (args : Array Expr) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => mkLambdaExpr n bi t (← mkAppRangeExpr body 4 args.size args)
      | _ =>
         -- case when then/else caluse is a quantified function
         if !(← isQuantifiedFun ite_e) then
            throwEnvError "mkAppNInDIteExpr: lambda/quantified function expected but got {reprStr ite_e}"
         -- Need to create a lambda term embedding the following application
         -- `fun h : ite_cond => ite_e h extra_args`.
         let auxApp ← mkAppRangeExpr (← mkAppExpr ite_e (← mkBVarExpr 0)) 4 args.size args
         mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default ite_cond auxApp

    normDIteApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option OptimizeStack) := do
      let Expr.const ``Blaster.dite' _ := f | return none
      if args.size ≤ 4 then return none
      let e1 ← mkAppInDIteExpr args args[1]! args[2]!
      let e2 ← mkAppInDIteExpr args (← mkAppExpr (← mkPropNotOp) args[1]!) args[3]!
      let dite_args := args.take 4
      let dite_args := dite_args.set! 2 e1
      let dite_args := dite_args.set! 3 e2
      -- update dite sort type
      -- NOTE: We expect that the ite sort is of form ∀ α₀ → ... → αₙ to avoid type inference,
      -- which is costly.
      let dite_args := dite_args.set! 0 (args[0]!.getForallBodyMaxDepth (args.size - 4))
      return some (.AppOptimizeImplicitArgs f dite_args 4 0 4 (← getFunEnvInfo f) prevInApp)

    mkAppInRhs (args : Array Expr) (beginIdx endIdx : Nat) (nbParams : Nat) (rhs : Expr) : TranslateEnvT Expr := do
      applyOnLambdaBoundedBody rhs nbParams (fun body => mkAppRangeExpr body beginIdx endIdx args)

    normMatchApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option OptimizeStack) := do
      let some argInfo ← isMatcher? f | return none
      if args.size ≤ argInfo.arity then return none
      let idxType := argInfo.getFirstDiscrPos - 1
      -- NOTE: We expect that the match sort is of form λ β₁ => ... => βₘ => ∀ α₁ → ... → αₙ to
      -- avoid type inference, which is costly.
      let retType := getAppliedMatchType args[idxType]! (args.size - argInfo.arity)
      let alts ← getMatchAlts args argInfo
      let mut margs := args.take argInfo.arity
      for i in [argInfo.getFirstAltPos : argInfo.arity] do
        let altIdx := i - argInfo.getFirstAltPos
        margs ← margs.modifyM i (mkAppInRhs args argInfo.arity args.size alts[altIdx]!.getNumHeadForalls)
      -- update match return type
      margs ← margs.modifyM idxType (updateMatchReturnType retType)
      return some (.AppOptimizeImplicitArgs f margs argInfo.arity 0 argInfo.arity (← getFunEnvInfo f) prevInApp)

/-- Apply the following propagation rules on any function application `fn e₁ ... eₙ`
    only when fn := Expr.const n l ∧ n ≠ Blaster.dite' ∧ propagate fn e₁ ... eₙ

    - When ∃ i ∈ [1..n],
            `eᵢ := Blaster.dite' c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `Blaster.dite' c then (fun h : c => fn g₁ ... gₙ) (fun h : ¬ c => fn h₁ ... hₙ)`

    - When ∃ i ∈ [1..n],
             eᵢ := match₂ f₁, ..., fₚ with
                  | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => t₁
                   ...
                  | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => tₘ ∧
             ∀ k ∈ [1..m],
               ∀ j ∈ [1..n], (i ≠ j → g₍ₖ₎₍ⱼ₎ = eⱼ) ∧ (i = j → g₍ₖ₎₍ⱼ₎ = tₖ)
       Return
         `match₂ f₁, ..., fₚ with
          | p₍₁₎₍₁₎, ..., p₍₁₎₍ₚ₎ => fn g₍₁₎₍₁₎, ..., g₍₁₎₍ₙ₎
          ...
          | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₚ₎ => fn g₍ₘ₎₍₁₎, ..., g₍ₘ₎₍ₙ₎`

    with:
      propagate fn e₁ ... eₙ :=
        isCtorExpr fn ∨
        allExplicitParamsAreCtor fn e₁ ... eₙ (funPropagation := true) ∨
        (fn = `Eq` ∧ n = 3 ∧ (isBoolValue? e₂).isSome )

    NOTE: skipPropCheck is set to `true` only when it is known beforehand that `cf`
    is a recursive function for which `allExplicitParamsAreCtor cf cargs (funPropagation := true)`
    returns `true`.

    NOTE: reorderArgs is set to `true` only when funPropagation? is called before optimizeApp.

    Assume that `fn` is a function (i.e., does not satisfy predicate isNotFun) or `fn` is a Ctor.
-/
def funPropagation?
  (cf : Expr) (cargs : Array Expr) (prevInApp : Bool)
  (reorderArgs := false) (resolveArgs := false) : TranslateEnvT (Option OptimizeStack) := do
  match cf with
  | Expr.const n _ =>
      if n == ``Blaster.dite' then return none
      if !(← propagate cf n cargs) then return none
      if reorderArgs
      then loop 0 cargs.size (← reorderOperands cf cargs)
      else loop 0 cargs.size cargs
  | _ => return none

  where
    @[always_inline, inline]
    hasMatchITEArgs (args : Array Expr) : TranslateEnvT Bool := do
      let matchCache := (← get).optEnv.memCache.isMatcherCache
      let rec go (idx : Nat) (stop : Nat) : Bool :=
        if idx ≥ stop then false
        else match args[idx]! with
             | .app (.app (.app (.app (Expr.const ``Blaster.dite' _) _) _) _) _ => true
             | .app f (.lam ..) => -- hack to only consider match
                  match f.getAppFn with
                  | Expr.const n _ => if matchCache.contains n then true else go (idx + 1) stop
                  | _ => go (idx + 1) stop
             | _ => go (idx + 1) stop
      return go 0 args.size

    loop (idx : Nat) (stop : Nat) (args : Array Expr) : TranslateEnvT (Option OptimizeStack) := do
      if idx ≥ stop then return none
      else if let some re ← diteCstProp? cf args idx then return re
      else if let some re ← matchCstProp? cf args idx then return re
      else loop (idx + 1) stop args

    @[always_inline, inline]
    propagate (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      if !(← hasMatchITEArgs args) then return false
      else if (← isCtorName n) then return true
      else if (← allExplicitParamsAreCtor f args (funPropagation := true)) then return true
      else
        match n with
        | ``Eq => if args.size != 3 then return false
                  else return isBoolCtor args[1]!
        | _ => return false

    pushFunInDIteExpr
      (f : Expr) (args : Array Expr) (idxField : Nat)
      (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => mkLambdaExpr n bi t (← mkAppNExprWithSetAt f args idxField body)
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← isQuantifiedFun ite_e) then
           throwEnvError "pushCtorInDIteExpr: lambda/quantified function expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => f x₁ ... xₙ`
           -- with x₁ ... xₙ = [ gᵢ | i ∈ [0 .. args.size-1] ∧
           --                        (idxField ≠ i → gᵢ = args[i]) ∧ (idxField = i → ite_e h)]
           let auxApp ← mkAppNExprWithSetAt f args idxField (← mkAppExpr ite_e (← mkBVarExpr 0))
           mkLambdaExpr (← Term.mkFreshBinderName) BinderInfo.default ite_cond auxApp

    /-- Implements dite over ctor rule -/
    @[always_inline, inline]
    diteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option OptimizeStack) := do
      -- NOTE: can't be an applied dite' function (e.g., applied to more than 4 arguments)
      if let some (_psort, pcond, e1, e2) := dite'? args[idxArg]! then
        let pInfo ← getFunEnvInfo f
        -- NOTE: We here prefer to instantiate the generic type kept in FunEnvInfo instead
        -- of calling inferTypeEnv as the latter is costly.
        -- NOTE: FunEnvInfo has already been added in the cache at this stage.
        let retType ← inferAppType pInfo.type args
        let e1' ← pushFunInDIteExpr f args idxArg pcond e1
        let e2' ← pushFunInDIteExpr f args idxArg (← mkAppExpr (← mkPropNotOp) pcond) e2
        -- NOTE: we need to propagate the reuse context to the new then and else expressions
        propagateReuseContext e1 e1' 0
        propagateReuseContext e2 e2' 0
        -- NOTE: we also need to set the sort type for the pulled dite' to meet the function's return type
        let dite_args := #[retType, pcond, e1', e2']
        let dite_op ← mkBlasterDIteOp
        let fInfo ← getFunEnvInfo dite_op
        setIsAppArg prevInApp
        if resolveArgs then
          return some (.AppOptimizeImplicitArgs dite_op dite_args 0 0 4 fInfo prevInApp)
        else return some (.AppOptimizeExplicitArgs dite_op dite_args 2 4 fInfo none prevInApp)
      else return none

    updateRhsWithFun
      (f : Expr) (args : Array Expr) (idxField : Nat) (nbParams : Nat)
      (rhs : Expr) : TranslateEnvT Expr := do
        applyOnLambdaBoundedBody rhs nbParams (fun body => mkAppNExprWithSetAt f args idxField body)

    /-- Implements match over ctor rule -/
    @[always_inline, inline]
    matchCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option OptimizeStack) := do
      if let some argInfo ← isMatcher? args[idxArg]!.getAppFn then
        -- NOTE: can't be an applied match (e.g., applied to more argInfo.mInfo.arity arguments)
        let pargs := args[idxArg]!.getAppArgs
        if pargs.size > argInfo.arity then return none
        else
          let idxType := argInfo.getFirstDiscrPos - 1
          let pInfo ← getFunEnvInfo f
          -- NOTE: We here prefer to instantiate the generic type kept in FunEnvInfo instead
          -- of calling inferTypeEnv as the latter is costly.
          -- NOTE: FunEnvInfo has already been added in the cache at this stage.
          let retType ← inferAppType pInfo.type args
          let alts ← getMatchAlts pargs argInfo
          -- NOTE: we also need to set the return type for pulled over match to meet the function's return type
          let mut pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
          for i in [argInfo.getFirstAltPos : argInfo.arity] do
            let altIdx := i - argInfo.getFirstAltPos
            -- NOTE: No need to propagate the reuse context as match name has not changed
            pargs ← pargs.modifyM i (updateRhsWithFun f args idxArg alts[altIdx]!.getNumHeadForalls)
          let fInfo ← getFunEnvInfo argInfo.nameExpr
          setIsAppArg prevInApp
          if resolveArgs then
            return some (.AppOptimizeImplicitArgs argInfo.nameExpr pargs 0 0 argInfo.arity fInfo prevInApp)
          else
            return some (.AppOptimizeExplicitArgs
                          argInfo.nameExpr pargs
                          argInfo.getFirstAltPos
                          argInfo.arity fInfo argInfo prevInApp)
      else return none

end Blaster.Optimize
