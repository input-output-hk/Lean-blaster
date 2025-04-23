import Lean
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeApp

open Lean Meta Elab
namespace Solver.Optimize

mutual
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
private partial def normChoiceApplicationAux?
  (f : Expr) (args : Array Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  normIteApp? f args fun ite_r =>
   match ite_r with
   | some _ => k ite_r
   | none =>
      normDIteApp? f args fun dite_r =>
       match dite_r with
       | some _ => k dite_r
       | none => normMatchApp? f args k

private partial def normIteApp?
  (f : Expr) (args : Array Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let Expr.const ``ite _ := f then
    if args.size ≤ 5 then k none
    else
      let extra_args := args.extract 5 args.size
      tryNormChoiceApp (mkAppN args[3]! extra_args) fun e1_r =>
        match e1_r with
        | none => throwEnvError "normIteApp?: unreachable case 1 !!!"
        | some e1 =>
            tryNormChoiceApp (mkAppN args[4]! extra_args) fun e2_r => do
              match e2_r with
              | none => throwEnvError "normIteApp?: unreachable case 2 !!!"
              | some e2 =>
                  let ite_args := args.take 5
                  let ite_args := ite_args.set! 3 e1
                  let ite_args := ite_args.set! 4 e2
                  -- Update ite sort type
                  let ite_args := ite_args.set! 0 (← inferType e1)
                  k (some (mkAppN f ite_args))
  else k none

private partial def mkAppInDIteExpr
  (extra_args : Array Expr) (ite_cond : Expr) (ite_e : Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  match ite_e with
  | Expr.lam n t body bi =>
      withLocalDecl n bi t fun x => do
        let auxApp := mkAppN (body.instantiate1 x) extra_args
        tryNormChoiceApp auxApp fun body_r => do
          match body_r with
          | none => throwEnvError "mkAppInDIteExpr: unreachable case 1 !!!"
          | some body' =>
             k (some (← mkLambdaFVars #[x] body'))
  | _ =>
    -- case when then/else caluse is a quantified function
    if !(← inferType ite_e).isForall then
      throwEnvError f!"mkAppNInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
    else
      -- Need to create a lambda term embedding the following application
      -- `fun h : ite_cond => ite_e h extra_args`.
      withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
        let auxApp := mkAppN (mkApp ite_e x) extra_args
        tryNormChoiceApp auxApp fun body_r => do
          match body_r with
          | none => throwEnvError "mkAppInDIteExpr: unreachable case 2 !!!"
          | some body =>
             k (some (← mkLambdaFVars #[x] body))

private partial def normDIteApp?
  (f : Expr) (args : Array Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let Expr.const ``dite _ := f then
    if args.size ≤ 5 then k none
    else
      let extra_args := args.extract 5 args.size
      mkAppInDIteExpr extra_args args[1]! args[3]! fun e1_r => do
        match e1_r with
        | none => throwEnvError "normDIteApp: unreachable case 1 !!!"
        | some e1 =>
            mkAppInDIteExpr extra_args (← optimizeNot (← mkPropNotOp) #[args[1]!]) args[4]! fun e2_r => do
              match e2_r with
              | none => throwEnvError "normDIteApp: unreachable case 2 !!!"
              | some e2 =>
                  let dite_args := args.take 5
                  let dite_args := dite_args.set! 3 e1
                  let dite_args := dite_args.set! 4 e2
                  -- update dite sort type
                  let dite_args := dite_args.set! 0 (← inferType (mkAppN f args))
                  k (some (mkAppN f dite_args))
  else k none

private partial def mkAppInRhs
  (extra_args : Array Expr) (lhs : Array Expr) (rhs : Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  let altArgsRes ← retrieveAltsArgs lhs
  let nbParams := altArgsRes.altArgs.size
  lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
    let auxApp := mkAppN body extra_args
    tryNormChoiceApp auxApp fun body_r => do
      match body_r with
      | none => throwEnvError "mkAppInRhs: unreachable case !!!"
      | some body' =>
         k (some (← mkLambdaFVars params body'))

private partial def normMatchApp?
  (f : Expr) (args : Array Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let Expr.const n l := f then
    if let some mInfo ← getMatcherRecInfo? n l then
      let cInfo ← getConstInfo n
      let matchFun ← instantiateValueLevelParams cInfo l
      let instApp := Expr.beta matchFun (args.take mInfo.getFirstAltPos)
      if args.size ≤ mInfo.arity then k none
      else
        let extra_args := args.extract mInfo.arity args.size
        withMatchAlts n instApp $ fun alts => do
          normMatchAppAux f args extra_args mInfo alts (args.take mInfo.arity) mInfo.getFirstAltPos k
    else k none
  else k none

  where
    withMatchAlts
      (n : Name) (instApp : Expr)
      (f : Array Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
        if (isCasesOnRecursor (← getEnv) n)
        then lambdaTelescope instApp fun xs _t => f xs
        else forallTelescope (← inferType instApp) fun xs _t => f xs

private partial def normMatchAppAux
  (f : Expr) (args : Array Expr) (extra_args : Array Expr) (mInfo : MatcherInfo)
  (alts : Array Expr) (margs : Array Expr) (idx : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if idx ≥ mInfo.arity then
    -- update match return type
    let idxType := mInfo.getFirstDiscrPos - 1
    let retType ← inferType (mkAppN f args)
    let margs' := margs.set! idxType (← updateMatchReturnType args[idxType]! retType)
    k (some (mkAppN f margs'))
  else
    let altIdx := idx - mInfo.getFirstAltPos
    let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
    mkAppInRhs extra_args lhs args[idx]! fun rhs_r =>
      match rhs_r with
      | none => throwEnvError "normMatchAppAux: unreachable case !!!"
      | some rhs' =>
         normMatchAppAux f args extra_args mInfo alts (margs.set! idx rhs') (idx + 1) k

/-- try to successively call reduceApp? and getUnfoldFunDef? before calling normChoiceApplicationAux?. -/
private partial def tryNormChoiceApp
  (e : Expr) (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  Expr.withApp e fun f args => do
    match (← reduceApp? f args) with
    | none =>
       match (← getUnfoldFunDef? f args) with
       | none =>
          normChoiceApplicationAux? f args fun f_r =>
           match f_r with
           | none => k e
           | some _ => k f_r
       | re => k re
    | re => k re
end

/-- See normChoiceApplicationAux? -/
def normChoiceApplication? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) :=
  normChoiceApplicationAux? f args (λ x => return x)

mutual
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
private partial def funPropagationAux?
  (ne : Expr) (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  Expr.withApp ne fun cf cargs => do
    match cf with
    | Expr.const n _ =>
        if n == ``ite || n == ``dite || (← isMatchExpr n)
        then k none
        else if !(← propagate cf n cargs)
             then k none
             else funArgsPropagation? ne cf cargs 0 cargs.size k
    | _ => k none

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

private partial def funArgsPropagation?
  (ne : Expr) (cf : Expr) (cargs : Array Expr) (idx : Nat) (stop : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if idx ≥ stop then k none
  else
   iteCstProp? cf cargs idx fun ite_r =>
    match ite_r with
    | some _ => do
        uncacheExpr ne
        k ite_r
    | none =>
       diteCstProp? cf cargs idx fun dite_r =>
         match dite_r with
         | some _ => do
             uncacheExpr ne
             k dite_r
         | none =>
            matchCstProp? cf cargs idx fun match_r =>
              match match_r with
              | some _ => do
                  uncacheExpr ne
                  k match_r
              | none => funArgsPropagation? ne cf cargs (idx + 1) stop k

/-- Implements ite over ctor rule -/
private partial def iteCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  -- NOTE: can't be an applied ite function (e.g., applied to more than 5 arguments)
  if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArg]! then
    tryAppReduction (mkAppN f (args.set! idxArg e1)) fun e1_r =>
     match e1_r with
     | none => throwEnvError "iteCstProp? unreachable case 1 !!!"
     | some e1' => do
        tryAppReduction (mkAppN f (args.set! idxArg e2)) fun e2_r =>
          match e2_r with
          | none => throwEnvError "iteCstProp? unreachable case 2 !!!"
          | some e2' => do
             -- NOTE: we also need to set the sort type for the pulled ite to meet the function's return type
             let retType ← inferType (mkAppN f args)
             k (some (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2'))
  else k none

private partial def pushFunInDIteExpr
  (f : Expr) (args : Array Expr) (idxField : Nat) (ite_cond : Expr) (ite_e : Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  match ite_e with
  | Expr.lam n t body bi =>
      withLocalDecl n bi t fun x => do
        let auxApp := mkAppN f (args.set! idxField (body.instantiate1 x))
        tryAppReduction auxApp fun body_r => do
          match body_r with
          | none => throwEnvError "pushFunInDIteExpr: unreachable case 1 !!!"
          | some body' =>
              k (some (← mkLambdaFVars #[x] body'))
  | _ =>
    -- case when then/else caluse is a quantified function
    if !(← inferType ite_e).isForall then
      throwEnvError f!"pushCtorInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
    else
      -- Need to create a lambda term embedding the following application
      -- `fun h : ite_cond => f x₁ ... xₙ`
      -- with x₁ ... xₙ = [ gᵢ | i ∈ [0 .. args.size  - 1] ∧
      --                        (idxField ≠ i → gᵢ = args[i]) ∧ (idxField = i → ite_e h)]
      withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
        let auxApp := mkAppN f (args.set! idxField (mkApp ite_e x))
        tryAppReduction auxApp fun body_r => do
          match body_r with
          | none => throwEnvError "pushFunInDIteExpr: unreachable case 2 !!!"
          | some body =>
             k (some (← mkLambdaFVars #[x] body))

/-- Implements dite over ctor rule -/
private partial def diteCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  -- NOTE: can't be an applied dite function (e.g., applied to more than 5 arguments)
  if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArg]! then
    pushFunInDIteExpr f args idxArg pcond e1 fun e1_r => do
     match e1_r with
     | none => throwEnvError "diteCstProp?: unreachable case 1 !!!"
     | some e1' =>
        pushFunInDIteExpr f args idxArg (← optimizeNot (← mkPropNotOp) #[pcond]) e2 fun e2_r => do
          match e2_r with
          | none => throwEnvError "diteCstProp?: unreachable case 2 !!!"
          | some e2' =>
             -- NOTE: we also need to set the sort type for the pulled dite to meet the function's return type
             let retType ← inferType (mkAppN f args)
             k (some (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2'))
  else k none

private partial def updateRhsWithFun
  (f : Expr) (args : Array Expr) (idxField : Nat) (lhs : Array Expr) (rhs : Expr)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  let altArgsRes ← retrieveAltsArgs lhs
  let nbParams := altArgsRes.altArgs.size
  lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
    let auxApp := mkAppN f (args.set! idxField body)
    tryAppReduction auxApp fun body_r => do
      match body_r with
      | none => throwEnvError "updateRhsWithFun: unreachable case !!!"
      | some body' =>
          k (some (← mkLambdaFVars params body'))

/-- Implements match over ctor rule -/
private partial def matchCstProp?
  (f : Expr) (args : Array Expr) (idxArg : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if let some argInfo ← isMatchArg? args[idxArg]! then
    -- NOTE: can't be an applied match (e.g., applied to more argInfo.mInfo.arity arguments)
    if argInfo.args.size > argInfo.mInfo.arity then k none
    else
      withMatchAlts argInfo $ fun alts => do
        matchCstPropAux f args idxArg argInfo alts argInfo.args argInfo.mInfo.getFirstAltPos k
  else k none

  where
    withMatchAlts
      (mInfo : MatchInfo) (f : Array Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
      if (isCasesOnRecursor (← getEnv) mInfo.name)
      then lambdaTelescope mInfo.instApp fun xs _t => f xs
      else forallTelescope (← inferType mInfo.instApp) fun xs _t => f xs

private partial def matchCstPropAux
  (f : Expr) (args : Array Expr) (idxArg : Nat)
  (argInfo : MatchInfo) (alts : Array Expr) (pargs : Array Expr) (idx : Nat)
  (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  if idx ≥ argInfo.mInfo.arity then
    -- NOTE: we also need to set the return type for pulled over match to meet the function's return type
    let idxType := argInfo.mInfo.getFirstDiscrPos - 1
    let retType ← inferType (mkAppN f args)
    let pargs' := pargs.set! idxType (← updateMatchReturnType argInfo.args[idxType]! retType)
    k (some (mkAppN argInfo.nameExpr pargs'))
  else
    let altIdx := idx - argInfo.mInfo.getFirstAltPos
    let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
    updateRhsWithFun f args idxArg lhs argInfo.args[idx]! fun rhs_r =>
      match rhs_r with
      | none => throwEnvError "matchCstPropAux: unreachable case !!!"
      | some rhs' =>
         matchCstPropAux f args idxArg argInfo alts (pargs.set! idx rhs') (idx + 1) k

/-- try to successively call reduceApp? and getUnfoldFunDef? before calling funPropagationAux?. -/
private partial def tryAppReduction
  (e : Expr) (k : Option Expr → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  let (f, args) := getAppFnWithArgs e
  match (← reduceApp? f args) with
  | none =>
     match (← getUnfoldFunDef? f args) with
     | none =>
        let optExpr ← optimizeApp f args
        funPropagationAux? optExpr fun f_r =>
         match f_r with
         | none => k (some optExpr)
         | some _ => k f_r
     | re => k re
  | re => k re

end

/-- See funPropagationAux? -/
def funPropagation? (ne : Expr) : TranslateEnvT (Option Expr) :=
  funPropagationAux? ne (λ x => return x)


end Solver.Optimize
