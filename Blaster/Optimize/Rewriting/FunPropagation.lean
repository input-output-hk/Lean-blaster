import Lean
import Blaster.Optimize.Rewriting.NormalizeMatch
import Blaster.Optimize.Rewriting.OptimizeMatch

open Lean Meta Elab
namespace Blaster.Optimize

/-- Given,
     - `t := λ β₁ => ... => βₘ => ∀ α₁ → ∀ α₂ → ... → αₙ` corresponding to a match expression
        returning functions as rhs; and
     - `nbArgs ∈ [0..n]` corresponding to the number of extra arguments applied to the match expression; and
     - α'₁, ..., α'ₘ := [ αᵢ | i ∈ [nbArgs, n] ]
    Return:
      - ∀ α'₁ → ∀ α'₂ → ... → α'ₘ
    Note that the returned type will correspond to αₙ when nbArgs = n.
-/
def getAppliedMatchType (t : Expr) (nbArgs : Nat) : Expr :=
  (getLambdaBody t).getForallBodyMaxDepth nbArgs


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
  (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := withLocalContext $ do
    if let some r ← normDIteApp? f args then return r
    normMatchApp? f args

  where
    mkAppInDIteExpr (extra_args : Array Expr) (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => return Expr.lam n t (mkAppN body extra_args) bi
      | _ =>
         -- case when then/else caluse is a quantified function
         if !(← isQuantifiedFun ite_e) then
            throwEnvError "mkAppNInDIteExpr: lambda/quantified function expected but got {reprStr ite_e}"
         -- Need to create a lambda term embedding the following application
         -- `fun h : ite_cond => ite_e h extra_args`.
         withLocalDecl' (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
           let auxApp := mkAppN (ite_e.beta #[x]) extra_args
           mkLambdaFVars #[x] auxApp

    normDIteApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      let Expr.const ``Blaster.dite' _ := f | return none
      if args.size ≤ 4 then return none
      let extra_args := args.extract 4 args.size
      let e1 ← mkAppInDIteExpr extra_args args[1]! args[2]!
      let e2 ← mkAppInDIteExpr extra_args (mkApp (← mkPropNotOp) args[1]!) args[3]!
      let dite_args := args.take 4
      let dite_args := dite_args.set! 2 e1
      let dite_args := dite_args.set! 3 e2
      -- update dite sort type
      -- NOTE: We expect that the ite sort is of form ∀ α₀ → ... → αₙ to avoid type inference,
      -- which is costly.
      let dite_args := dite_args.set! 0 (args[0]!.getForallBodyMaxDepth (args.size - 4))
      return (mkAppN f dite_args)

    mkAppInRhs (extra_args : Array Expr) (lhs : Array Expr) (rhs : Expr) : TranslateEnvT Expr := do
      let altArgsRes ← retrieveAltsArgs lhs
      let nbParams := altArgsRes.altArgs.size
      applyOnLambdaBoundedBody rhs (max 1 nbParams) (fun body => return mkAppN body extra_args)

    normMatchApp? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      let some argInfo ← isMatcher? f | return none
      if args.size ≤ argInfo.arity then return none
      let extra_args := args.extract argInfo.arity args.size
      let idxType := argInfo.getFirstDiscrPos - 1
      -- NOTE: We expect that the match sort is of form λ β₁ => ... => βₘ => ∀ α₁ → ... → αₙ to
      -- avoid type inference, which is costly.
      let retType := getAppliedMatchType args[idxType]! (args.size - argInfo.arity)
      let alts := getMatchAlts args argInfo
      let mut margs := args.take argInfo.arity
      for i in [argInfo.getFirstAltPos : argInfo.arity] do
        let altIdx := i - argInfo.getFirstAltPos
        let lhs ← forallTelescope alts[altIdx]! fun _ b => pure b.getAppArgs
        margs ← margs.modifyM i (mkAppInRhs extra_args lhs)
      -- update match return type
      margs ← margs.modifyM idxType (updateMatchReturnType retType)
      return mkAppN f margs

/-- Apply the following propagation rules on any function application `fn e₁ ... eₙ`
    only when fn := Expr.const n l ∧ n ≠ Blaster.dite' ∧ ¬ isNotFun fn ∧ propagate fn e₁ ... eₙ

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
-/
def funPropagation? (cf : Expr) (cargs : Array Expr) (skipPropCheck := false) (reorderArgs := false) : TranslateEnvT (Option Expr) :=
 withLocalContext $ do
  match cf with
  | Expr.const n _ =>
      if skipPropCheck then loop 0 cargs
      else
        if n == ``Blaster.dite' || (← isNotFun cf) then return none
        if !(← propagate cf n cargs) then return none
        if reorderArgs
        then loop 0 (← reorderOperands cf cargs)
        else loop 0 cargs
  | _ => return none

  where

    loop (idx : Nat) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      if idx ≥ args.size then return none
      else if let some re ← diteCstProp? cf args idx then return re
      else if let some re ← matchCstProp? cf args idx then return re
      else loop (idx + 1) args

    propagate (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      if (← isCtorName n) then return true
      if (← allExplicitParamsAreCtor f args (funPropagation := true)) then return true
      match n with
      | ``Eq => if args.size != 3 then return false
                return isBoolCtor args[1]!
      | _ => return false

    pushFunInDIteExpr
      (f : Expr) (args : Array Expr) (idxField : Nat)
      (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi => return Expr.lam n t (mkAppN f (args.set! idxField body)) bi
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← isQuantifiedFun ite_e) then
           throwEnvError "pushCtorInDIteExpr: lambda/quantified function expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => f x₁ ... xₙ`
           -- with x₁ ... xₙ = [ gᵢ | i ∈ [0 .. args.size-1] ∧
           --                        (idxField ≠ i → gᵢ = args[i]) ∧ (idxField = i → ite_e h)]
           withLocalDecl' (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
             mkLambdaFVars #[x] (mkAppN f (args.set! idxField (ite_e.beta #[x])))

    /-- Implements dite over ctor rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option Expr) := do
      -- NOTE: can't be an applied dite' function (e.g., applied to more than 4 arguments)
      if let some (_psort, pcond, e1, e2) := dite'? args[idxArg]! then
        let pInfo ← getFunEnvInfo f
        -- NOTE: We here prefer to instantiate the generic type kept in FunEnvInfo instead
        -- of calling inferTypeEnv as the latter is costly.
        -- NOTE: FunEnvInfo has already been added in the cache at this stage.
        let retType := inferAppType pInfo.type args
        let e1' ← pushFunInDIteExpr f args idxArg pcond e1
        let e2' ← pushFunInDIteExpr f args idxArg (mkApp (← mkPropNotOp) pcond) e2
        -- NOTE: we also need to set the sort type for the pulled dite' to meet the function's return type
        return (mkApp4 (← mkBlasterDIteOp) retType pcond e1' e2')
      else return none

    updateRhsWithFun
      (f : Expr) (args : Array Expr) (idxField : Nat) (lhs : Array Expr)
      (rhs : Expr) : TranslateEnvT Expr := do
        let altArgsRes ← retrieveAltsArgs lhs
        let nbParams := altArgsRes.altArgs.size
        applyOnLambdaBoundedBody rhs (max 1 nbParams) (fun body => return mkAppN f (args.set! idxField body))

    /-- Implements match over ctor rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option Expr) := do
      let (pf, pargs) := getAppFnWithArgs args[idxArg]!
      let some argInfo ← isMatcher? pf | return none
      -- NOTE: can't be an applied match (e.g., applied to more argInfo.mInfo.arity arguments)
      if pargs.size > argInfo.arity then return none
      let idxType := argInfo.getFirstDiscrPos - 1
      let pInfo ← getFunEnvInfo f
      -- NOTE: We here prefer to instantiate the generic type kept in FunEnvInfo instead
      -- of calling inferTypeEnv as the latter is costly.
      -- NOTE: FunEnvInfo has already been added in the cache at this stage.
      let retType := inferAppType pInfo.type args
      let alts := getMatchAlts pargs argInfo
      let mut pargs := pargs
      for i in [argInfo.getFirstAltPos : argInfo.arity] do
        let altIdx := i - argInfo.getFirstAltPos
        let lhs ← forallTelescope alts[altIdx]! fun _ b => pure b.getAppArgs
        pargs ← pargs.modifyM i (updateRhsWithFun f args idxArg lhs)
      -- NOTE: we also need to set the return type for pulled over match to meet the function's return type
      pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
      return (mkAppN argInfo.nameExpr pargs)

end Blaster.Optimize
