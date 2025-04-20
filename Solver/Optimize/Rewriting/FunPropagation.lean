import Lean
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab
namespace Solver.Optimize


/-- Given `pType := λ α₁ → .. → λ αₙ → t` returns `λ α₁ → .. → λ αₙ → eType`
    This function is expected to be used only when updating a match return type
-/
private def updateReturnType (pType : Expr) (eType : Expr) : TranslateEnvT Expr := do
  lambdaTelescope pType fun params _body => do
    mkExpr (← mkLambdaFVars params eType) (cacheResult := false)

/-- Given application `f x₁ ... xₙ`, apply the following normalization rules:
     - When `f := if c then t₁ else t₂`
       Return
         if c then t₁ x₁ ... xₙ else t₂ x₁ ... xₙ

     - When `f := dite c (fun h : c => t₁) (fun h : ¬ c => t₂)`
       Return
         dite c (fun h : c => t₁ x₁ ... xₙ) (fun h : ¬ c => t₂ x₁ ... xₙ)

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
def normChoiceApplication? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if let some r ← normIteApp? f args then return r
  if let some r ← normDIteApp? f args then return r
  normMatchApp? f args

  where
    normIteApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const ``ite _ := f | return none
      if args.size ≤ 5 then return none
      let extra_args := args.extract 5 args.size
      let e1 ← mkExpr (mkAppN args[3]! extra_args) (cacheResult := false)
      let e2 ← mkExpr (mkAppN args[4]! extra_args) (cacheResult := false)
      let ite_args := args.take 5
      let ite_args := ite_args.set! 3 e1
      let ite_args := ite_args.set! 4 e2
      -- Update ite sort type
      let ite_args := ite_args.set! 0 (← inferType e1)
      some <$> mkExpr (mkAppN f ite_args) (cacheResult := false)

    mkAppInDIteExpr (extra_args : Array Expr) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi =>
          withLocalDecl n bi t fun x => do
            let body' ← mkExpr (mkAppN (body.instantiate1 x) extra_args) (cacheResult := false)
            mkExpr (← mkLambdaFVars #[x] body') (cacheResult := false)
      | _ =>
        -- case when then/else caluse is a quantified function
        if !(← inferType ite_e).isForall then
          throwEnvError f!"mkAppNInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
        -- Need to create a lambda term embedding the following application
        -- `fun h : ite_cond => ite_e h extra_args`.
        withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
          let body ← mkExpr (mkAppN (mkApp ite_e x) extra_args) (cacheResult := false)
          mkExpr (← mkLambdaFVars #[x] body) (cacheResult := false)

    normDIteApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const ``dite _ := f | return none
      if args.size ≤ 5 then return none
      let extra_args := args.extract 5 args.size
      let e1 ← mkAppInDIteExpr extra_args args[1]! args[3]!
      let e2 ← mkAppInDIteExpr extra_args (← optimizeNot (← mkPropNotOp) #[args[1]!]) args[4]!
      let dite_args := args.take 5
      let dite_args := dite_args.set! 3 e1
      let dite_args := dite_args.set! 4 e2
      -- update dite sort type
      let dite_args := dite_args.set! 0 (← inferType (mkAppN f args))
      some <$> mkExpr (mkAppN f dite_args) (cacheResult := false)

    mkAppInRhs (extra_args : Array Expr) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
      let altArgsRes ← retrieveAltsArgs lhs
      let nbParams := altArgsRes.altArgs.size
      lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
        let body' ← mkExpr (mkAppN body extra_args) (cacheResult := false)
        mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    withMatchAlts (n : Name) (instApp : Expr) (f : Array Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
      if (isCasesOnRecursor (← getEnv) n)
      then lambdaTelescope instApp fun xs _t => f xs
      else forallTelescope (← inferType instApp) fun xs _t => f xs

    normMatchApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const n l := f | return none
      let some mInfo ← getMatcherRecInfo? n l | return none
      let cInfo ← getConstInfo n
      let matchFun ← instantiateValueLevelParams cInfo l
      let instApp := Expr.beta matchFun (args.take mInfo.getFirstAltPos)
      if args.size ≤ mInfo.arity then return none
      let extra_args := args.extract mInfo.arity args.size
      let idxType := mInfo.getFirstDiscrPos - 1
      withMatchAlts n instApp $ fun alts => do
        let mut margs := args.take mInfo.arity
        for k in [mInfo.getFirstAltPos : mInfo.arity] do
          let altIdx := k - mInfo.getFirstAltPos
          let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
          margs := margs.set! k (← mkAppInRhs extra_args lhs args[k]!)
          -- update match return type
          let retType ← inferType (mkAppN f args)
          margs := margs.set! idxType (← updateReturnType args[idxType]! retType)
        mkExpr (mkAppN f margs) (cacheResult := false)

/-- Apply the following propagation rules on any function application `fn e₁ ... eₙ`
    only when fn := Expr.const n _ ∧ n ≠ ite ∧ n ≠ dite ∧ ¬ isMatchExpr n ∧
              propagate fn e₁ ... eₙ

    - When ∃ i ∈ [1..n],
            `eᵢ := if c then d₁ else d₂` ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `if c then fn g₁ ... gₙ else fn h₁ ... hₙ`

    - When ∃ i ∈ [1..n],
            `eᵢ := dite c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
             ∀ j ∈ [1..n],
                (i ≠ j → gⱼ = eⱼ) ∧ (i = j → gⱼ = d₁) ∧
                (i ≠ j → hⱼ = eⱼ) ∧ (i = j → hⱼ = d₂)
      Return
         `dite c then (fun h : c => fn g₁ ... gₙ) (fun h : ¬ c => fn h₁ ... hₙ)`

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
-/
def funPropagation? (ne : Expr) : TranslateEnvT (Option Expr) := do
  Expr.withApp ne fun cf cargs => do
    let Expr.const n _ := cf | return none
    if n == ``ite || n == ``dite || (← isMatchExpr n) then return none
    if !(← propagate cf n cargs) then return none
    for i in [0 : cargs.size] do
      if let some r ← iteCstProp? cf cargs i then
        uncacheExpr ne
        return r
      if let some r ← diteCstProp? cf cargs i then
        uncacheExpr ne
        return r
      if let some r ← matchCstProp? cf cargs i then
        uncacheExpr ne
        return r
    return none

  where
    propagate (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      if (← isCtorName n) then return true
      if (← allExplicitParamsAreCtor f args (funPropagation := true)) then return true
      match n with
      | ``Eq =>
        if args.size != 3 then return false
        match args[1]! with
        | Expr.const ``true _
        | Expr.const ``false _ => return true
        | _ => return false
      | _ => return false

    /-- Implements ite over ctor rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
      -- NOTE: can't be an applied ite function (e.g., applied to more than 5 arguments)
      if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArgs]! then
        let e1' ← mkExpr (mkAppN f (args.set! idxArgs e1)) (cacheResult := false)
        let e2' ← mkExpr (mkAppN f (args.set! idxArgs e2)) (cacheResult := false)
        -- NOTE: we also need to set the sort type for the pulled ite to meet the function's return type
        let retType ← inferType (mkAppN f args)
        return ← mkExpr (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
      return none

    pushFunInDIteExpr (f : Expr) (args : Array Expr) (idxField : Nat) (ite_cond : Expr) (ite_e : Expr) :
     TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi =>
          withLocalDecl n bi t fun x => do
            let body' ← mkExpr (mkAppN f (args.set! idxField (body.instantiate1 x))) (cacheResult := false)
            mkExpr (← mkLambdaFVars #[x] body') (cacheResult := false)
      | _ =>
        -- case when then/else caluse is a quantified function
        if !(← inferType ite_e).isForall then
          throwEnvError f!"pushCtorInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
        -- Need to create a lambda term embedding the following application
        -- `fun h : ite_cond => f x₁ ... xₙ`
        -- with x₁ ... xₙ = [ gᵢ | i ∈ [0 .. args.size  - 1] ∧
        --                        (idxField ≠ i → gᵢ = args[i]) ∧ (idxField = i → ite_e h)]
        withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
          let body ← mkExpr (mkAppN f (args.set! idxField (mkApp ite_e x))) (cacheResult := false)
          mkExpr (← mkLambdaFVars #[x] body) (cacheResult := false)

    /-- Implements dite over ctor rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
      -- NOTE: can't be an applied dite function (e.g., applied to more than 5 arguments)
      if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArgs]! then
        let e1' ← pushFunInDIteExpr f args idxArgs pcond e1
        let e2' ← pushFunInDIteExpr f args idxArgs (← optimizeNot (← mkPropNotOp) #[pcond]) e2
        -- NOTE: we also need to set the sort type for the pulled dite to meet the function's return type
        let retType ← inferType (mkAppN f args)
        return ← mkExpr (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2') (cacheResult := false)
      return none

    updateRhsWithFun
      (f : Expr) (args : Array Expr) (idxField : Nat)
      (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
        let altArgsRes ← retrieveAltsArgs lhs
        let nbParams := altArgsRes.altArgs.size
        lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
          let body' ← mkExpr (mkAppN f (args.set! idxField body)) (cacheResult := false)
          mkExpr (← mkLambdaFVars params body') (cacheResult := false)

    withMatchAlts (mInfo : MatchInfo) (f : Array Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
      if (isCasesOnRecursor (← getEnv) mInfo.name)
      then lambdaTelescope mInfo.instApp fun xs _t => f xs
      else forallTelescope (← inferType mInfo.instApp) fun xs _t => f xs

    /-- Implements match over ctor rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (idxArgs : Nat) : TranslateEnvT (Option Expr) := do
     if let some argInfo ← isMatchArg? args[idxArgs]! then
       -- NOTE: can't be an applied match (e.g., applied to more argInfo.mInfo.arity arguments)
       if argInfo.args.size > argInfo.mInfo.arity then return none
       let idxType := argInfo.mInfo.getFirstDiscrPos - 1
       let mExpr ←
         withMatchAlts argInfo $ fun alts => do
           let mut pargs' := argInfo.args
           for k in [argInfo.mInfo.getFirstAltPos : argInfo.mInfo.arity] do
             let altIdx := k - argInfo.mInfo.getFirstAltPos
             let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
             pargs' := pargs'.set! k (← updateRhsWithFun f args idxArgs lhs argInfo.args[k]!)
             -- NOTE: we also need to set the return type for pulled over match to meet the function's return type
             let retType ← inferType (mkAppN f args)
             pargs' := pargs'.set! idxType (← updateReturnType argInfo.args[idxType]! retType)
           mkExpr (mkAppN argInfo.nameExpr pargs') (cacheResult := false)
       return mExpr
      return none

end Solver.Optimize
