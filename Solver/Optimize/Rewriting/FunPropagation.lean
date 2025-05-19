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
        let auxApp := mkAppN (ite_e.beta #[x]) extra_args
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
  let (f, args) := getAppFnWithArgs e
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


/-- Return result of reduceApp? when successful. Otherwise return `mkAppN f args`. -/
def tryAppReduction (f : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  match (← reduceApp? f args) with
  | none => return (mkAppN f args)
  | some re => return re

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
def funPropagation? (cf : Expr) (cargs : Array Expr) : TranslateEnvT (Option Expr) := do
  match cf with
  | Expr.const n _ =>
      if n == ``ite || n == ``dite || (← isMatchExpr n) then return none
      if !(← propagate cf n cargs) then return none
      for i in [:cargs.size] do
        if let some re ← iteCstProp? cf cargs i then return re
        if let some re ← diteCstProp? cf cargs i then return re
        if let some re ← matchCstProp? cf cargs i then return re
      return none
  | _ => return none

  where
    isAppReduceTrue (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      match n with
      | ``Eq => if args.size == 3
                then exprEq args[1]! args[2]!
                else return false
      | ``BEq
      | ``LE.le
      | ``LT.lt =>
             if args.size == 4 && (← isOpaqueRelational n args)
             then exprEq args[2]! args[3]!
             else return false
      | _ => return false

    propagate (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      if (← isAppReduceTrue n args) then return false
      if (← isCtorName n) then return true
      if (← allExplicitParamsAreCtor f args (funPropagation := true)) then return true
      match n with
      | ``Eq =>
        if args.size != 3 then return false
        else return (isBoolCtor args[1]! || isBoolCtor args[2]!)
      | _ => return false

    /-- Implements ite over ctor rule -/
    iteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option Expr) := do
      -- NOTE: can't be an applied ite function (e.g., applied to more than 5 arguments)
      if let some (_psort, pcond, pdecide, e1, e2) := ite? args[idxArg]! then
        let retType ← inferType (mkAppN f args)
        let e1' ← tryAppReduction f (args.set! idxArg e1)
        let e2' ← tryAppReduction f (args.set! idxArg e2)
        -- NOTE: we also need to set the sort type for the pulled ite to meet the function's return type
        return (mkApp5 (← mkIteOp) retType pcond pdecide e1' e2')
      else return none

    pushFunInDIteExpr
      (f : Expr) (args : Array Expr) (idxField : Nat)
      (ite_cond : Expr) (ite_e : Expr) : TranslateEnvT Expr := do
      match ite_e with
      | Expr.lam n t body bi =>
           withLocalDecl n bi t fun x => do
            let body' ← tryAppReduction f (args.set! idxField (body.instantiate1 x))
            mkLambdaFVars #[x] body'
      | _ =>
         -- case when then/else clause is a quantified function
         if !(← inferType ite_e).isForall then
           throwEnvError f!"pushCtorInDIteExpr: lambda/function expression expected but got {reprStr ite_e}"
         else
           -- Need to create a lambda term embedding the following application
           -- `fun h : ite_cond => f x₁ ... xₙ`
           -- with x₁ ... xₙ = [ gᵢ | i ∈ [0 .. args.size-1] ∧
           --                        (idxField ≠ i → gᵢ = args[i]) ∧ (idxField = i → ite_e h)]
           withLocalDecl (← Term.mkFreshBinderName) BinderInfo.default ite_cond fun x => do
             let body ← tryAppReduction f (args.set! idxField (ite_e.beta #[x]))
             mkLambdaFVars #[x] body

    /-- Implements dite over ctor rule -/
    diteCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option Expr) := do
      -- NOTE: can't be an applied dite function (e.g., applied to more than 5 arguments)
      if let some (_psort, pcond, pdecide, e1, e2) := dite? args[idxArg]! then
        let retType ← inferType (mkAppN f args)
        let e1' ← pushFunInDIteExpr f args idxArg pcond e1
        let e2' ← pushFunInDIteExpr f args idxArg (← optimizeNot (← mkPropNotOp) #[pcond]) e2
        -- NOTE: we also need to set the sort type for the pulled dite to meet the function's return type
        return (mkApp5 (← mkDIteOp) retType pcond pdecide e1' e2')
      else return none

    updateRhsWithFun
      (f : Expr) (args : Array Expr) (idxField : Nat) (lhs : Array Expr)
      (rhs : Expr) : TranslateEnvT Expr := do
        let altArgsRes ← retrieveAltsArgs lhs
        let nbParams := altArgsRes.altArgs.size
        lambdaBoundedTelescope rhs (max 1 nbParams) fun params body => do
          let body' ← tryAppReduction f (args.set! idxField body)
          mkLambdaFVars params body'

    withMatchAlts (mInfo : MatchInfo) (f : Array Expr → TranslateEnvT Expr) : TranslateEnvT Expr := do
      if (isCasesOnRecursor (← getEnv) mInfo.name)
      then lambdaTelescope mInfo.instApp fun xs _t => f xs
      else forallTelescope (← inferType mInfo.instApp) fun xs _t => f xs

    /-- Implements match over ctor rule -/
    matchCstProp? (f : Expr) (args : Array Expr) (idxArg : Nat) : TranslateEnvT (Option Expr) := do
      if let some argInfo ← isMatchArg? args[idxArg]!
      then
        -- NOTE: can't be an applied match (e.g., applied to more argInfo.mInfo.arity arguments)
        if argInfo.args.size > argInfo.mInfo.arity
        then return none
        else
          let idxType := argInfo.mInfo.getFirstDiscrPos - 1
          let retType ← inferType (mkAppN f args)
          withMatchAlts argInfo $ fun alts => do
            let mut pargs := argInfo.args
            for i in [argInfo.mInfo.getFirstAltPos : argInfo.mInfo.arity] do
              let altIdx := i - argInfo.mInfo.getFirstAltPos
              let lhs ← forallTelescope (← inferType alts[altIdx]!) fun _ b => pure b.getAppArgs
              pargs ← pargs.modifyM i (updateRhsWithFun f args idxArg lhs)
            -- NOTE: we also need to set the return type for pulled over match to meet the function's return type
            pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
            return (mkAppN argInfo.nameExpr pargs)
      else return none

end Solver.Optimize
