import Lean
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Telescope

open Lean Meta Elab
namespace Solver.Optimize


@[always_inline, inline]
def withMatchAlts (mInfo : MatchInfo) (f : Array Expr → TranslateEnvT α) : TranslateEnvT α := do
 if (isCasesOnRecursor (← getEnv) mInfo.name)
 then lambdaTelescope mInfo.instApp fun xs _t => f xs
 else forallTelescope (← inferType mInfo.instApp) fun xs _t => f xs

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
             if let Expr.const n l := f then
               if let some mInfo ← getMatcherRecInfo? n l then
                 -- NOTE: we also need to cater for function as return type,
                 -- i.e., match expression returns a function.
                 if args.size > mInfo.arity then return false
                 else isCstMatchPropAux (updateStackWithMatchRhs mInfo args xs mInfo.getFirstAltPos)
               else return false
             else return false

  where
    updateStackWithMatchRhs
      (mInfo : MatcherInfo) (args : Array Expr)
      (stack : List Expr) (idx : Nat) : List Expr :=
      if idx >= mInfo.arity then stack
      else updateStackWithMatchRhs mInfo args (getLambdaBody args[idx]! :: stack) (idx + 1)


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
@[always_inline, inline]
  def isCstMatchProp (p : Expr) : TranslateEnvT Bool := isCstMatchPropAux [p]

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

    tryReduction? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
      -- NOTE: simplifies match only when all the discriminators are constructors
      let Expr.const n dlevel := f | return none
      let cInfo ← getConstEnvInfo n
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

structure LambdaStackContext where
  params : Array Expr -- lambda parameters both from lambdaTelescope
  body : Expr -- body obtained after pushing match in Dite/match rhs
  context : LocalContext -- local context obtained from lambdaTelescope

inductive ConstMatchStack where
  | CMatchInit (cm : Expr) (cargs : Array Expr) (mInfo : MatcherInfo)
  | CMatchIteThen (rtype : Expr) (cond : Expr) (pdecide : Expr)
                  (mInfo : MatcherInfo) (extra_args : Array Expr) (e1 : Expr) (e2 : Expr)
  | CMatchIteElse (rtype : Expr) (cond : Expr) (pdecide : Expr)
                  (mInfo : MatcherInfo) (extra_args : Array Expr) (e1' : Expr) (e2 : Expr)
  | CMatchIteReturn (rtype : Expr) (cond : Expr) (pdecide : Expr)
                    (extra_args : Array Expr) (e1 : Expr) (e2 : Expr)
  | CMatchDIteThen (rtype : Expr) (cond : Expr) (pdecide : Expr)
                   (mInfo : MatcherInfo) (extra_args : Array Expr)
                   (e1 : LambdaStackContext) (e2 : LambdaStackContext)
  | CMatchDIteElse (rtype : Expr) (cond : Expr) (pdecide : Expr)
                   (mInfo : MatcherInfo) (extra_args : Array Expr)
                   (e1 : Expr) (e2 : LambdaStackContext)
  | CMatchDIteReturn (rtype : Expr) (cond : Expr) (pdecide : Expr)
                     (extra_args : Array Expr) (e1 : Expr) (e2 : Expr)
  | CMatchRHS (f : Expr) (margs : Array Expr) (extra_args : Array Expr) (idxArg : Nat)
              (mInfo : MatcherInfo) (argInfo : MatchInfo) (pargs : Array Expr)
              (rhs : LambdaStackContext) (idxRhs : Nat)
  | CMatchArgsPropagation (cm : Expr) (cargs : Array Expr) (mInfo : MatcherInfo) (idx : Nat)


/-- Helper function for constMatchpropagation? -/
private partial def constMatchPropagationAux? (stack : List ConstMatchStack) : TranslateEnvT (Option Expr) := do
  match stack with
  | .CMatchInit cm cargs mInfo :: xs =>
       if !(← allDiscrsAreCstMatch cargs mInfo) then
         match ← stackContinuity xs none with
         | none => return none
         | some stack' => constMatchPropagationAux? stack'
       else constMatchPropagationAux? ( .CMatchArgsPropagation cm cargs mInfo mInfo.getFirstDiscrPos :: xs)

  | .CMatchArgsPropagation cm cargs mInfo idx :: xs =>
       if idx ≥ mInfo.getFirstAltPos then
         match ← stackContinuity xs none with
         | none => return none
         | some stack' => constMatchPropagationAux? stack'
       else if let some (_psort, pcond, pdecide, e1, e2) := ite? cargs[idx]! then
         -- NOTE: we also need to cater for function as return type,
         -- i.e., match expression returns a function. Hence, extra arguments are now applied to ite.
         let margs := cargs.take mInfo.arity
         let extra_args := cargs.extract mInfo.arity cargs.size
         -- NOTE: we also need to set the sort type for the pulled ite to meet
         -- the return type of the embedded match
         let retType ← inferType (mkAppN cm margs)
         let e1' := mkAppN cm (margs.set! idx e1)
         let e2' := mkAppN cm (margs.set! idx e2)
         constMatchPropagationAux? ( .CMatchIteThen retType pcond pdecide mInfo extra_args e1' e2' :: xs)
       else if let some (_psort, pcond, pdecide, e1, e2) := dite? cargs[idx]! then
         -- NOTE: we also need to cater for function as return type,
         -- i.e., match expression returns a function. Hence, extra arguments are now applied to dite.
         let margs := cargs.take mInfo.arity
         let extra_args := cargs.extract mInfo.arity cargs.size
         -- NOTE: we also need to set the sort type for the pulled dite to meet
         -- the return type of the embedded match
         let retType ← inferType (mkAppN cm margs)
         let e1' ← mkLambdaStackContext cm margs idx e1
         let e2' ← mkLambdaStackContext cm margs idx e2
         constMatchPropagationAux? ( .CMatchDIteThen retType pcond pdecide mInfo extra_args e1' e2' :: xs)
       else if let some argInfo ← isMatcher? cargs[idx]! then
         -- NOTE: we also need to cater for function as return type,
         -- i.e., match expression returns a function. Hence, extra arguments are now applied to pulled match.
         let margs := cargs.take mInfo.arity
         let extra_args := cargs.extract mInfo.arity cargs.size
         let idxRhs := argInfo.mInfo.getFirstAltPos
         let rhs ← mkLambdaStackContext cm margs idx argInfo.args[idxRhs]!
         constMatchPropagationAux? ( .CMatchRHS cm margs extra_args idx mInfo argInfo argInfo.args rhs idxRhs :: xs)
       else constMatchPropagationAux? (.CMatchArgsPropagation cm cargs mInfo (idx + 1) :: xs)

  | .CMatchIteThen rtype cond pdecide mInfo extra_args e1 e2 :: xs =>
      let (f, args) := getAppFnWithArgs e1
      match (← reduceMatch? f args mInfo) with
      | some re => constMatchPropagationAux? (.CMatchIteElse rtype cond pdecide mInfo extra_args re e2 :: xs)
      | none => constMatchPropagationAux? (.CMatchInit f args mInfo :: stack)

  | .CMatchIteElse rtype cond pdecide mInfo extra_args e1' e2 :: xs =>
      let (f, args) := getAppFnWithArgs e2
      match (← reduceMatch? f args mInfo) with
      | some re => constMatchPropagationAux? (.CMatchIteReturn rtype cond pdecide extra_args e1' re :: xs)
      | none => constMatchPropagationAux? (.CMatchInit f args mInfo :: stack)

  | .CMatchIteReturn rtype cond pdecide extra_args e1 e2 :: xs =>
      let iteExpr := mkApp5 (← mkIteOp) rtype cond pdecide e1 e2
      let res := if extra_args.isEmpty then iteExpr else mkAppN iteExpr extra_args
      match ← stackContinuity xs (some res) with
      | none => return res
      | some stack' => constMatchPropagationAux? stack'

  | .CMatchDIteThen rtype cond pdecide mInfo extra_args e1 e2 :: xs =>
       let (f, args) := getAppFnWithArgs e1.body
       match (← reduceMatch? f args mInfo) with
       | some re =>
           let e1' ← withLCtx' e1.context $ mkLambdaFVars e1.params re
           constMatchPropagationAux? (.CMatchDIteElse rtype cond pdecide mInfo extra_args e1' e2 :: xs)
       | none => constMatchPropagationAux? (.CMatchInit f args mInfo :: stack)

  | .CMatchDIteElse rtype cond pdecide mInfo extra_args e1' e2 :: xs =>
       let (f, args) := getAppFnWithArgs e2.body
       match (← reduceMatch? f args mInfo) with
       | some re =>
           let e2' ← withLCtx' e2.context $ mkLambdaFVars e2.params re
           constMatchPropagationAux? (.CMatchDIteReturn rtype cond pdecide extra_args e1' e2' :: xs)
       | none => constMatchPropagationAux? (.CMatchInit f args mInfo :: stack)

  | .CMatchDIteReturn rtype cond pdecide extra_args e1 e2 :: xs =>
      let diteExpr := mkApp5 (← mkDIteOp) rtype cond pdecide e1 e2
      let res := if extra_args.isEmpty then diteExpr else (mkAppN diteExpr extra_args)
      match ← stackContinuity xs (some res) with
      | none => return res
      | some stack' => constMatchPropagationAux? stack'

  | .CMatchRHS cm margs extra_args idxArg mInfo argInfo pargs rhs idxRhs :: xs =>
        if idxRhs ≥ argInfo.mInfo.arity then
          -- NOTE: we also need to set the return type for pulled over match
          -- to meet the return type of the embedded match.
          let idxType := argInfo.mInfo.getFirstDiscrPos - 1
          let retType ← inferType (mkAppN cm margs)
          let pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
          let pMatchExpr := mkAppN argInfo.nameExpr pargs
          let res := if extra_args.isEmpty then pMatchExpr else mkAppN pMatchExpr extra_args
          match ← stackContinuity xs (some res) with
          | none => return res
          | some stack' => constMatchPropagationAux? stack'
        else
          let (f, args) := getAppFnWithArgs rhs.body
          match (← reduceMatch? f args mInfo) with
          | some re =>
              let rhs' ← withLCtx' rhs.context $ mkLambdaFVars rhs.params re
              let nextRhs ←
                if idxRhs + 1 ≥ argInfo.mInfo.arity then pure rhs
                else mkLambdaStackContext cm margs idxArg argInfo.args[idxRhs + 1]!
              constMatchPropagationAux?
                (.CMatchRHS cm margs extra_args idxArg mInfo argInfo (pargs.set! idxRhs rhs') nextRhs (idxRhs + 1)  :: xs)
          | none => constMatchPropagationAux? (.CMatchInit f args mInfo :: stack)

  | _ => throwEnvError "constMatchPropagationAux? : unexpected continuity !!!"


  where
    allDiscrsAreCstMatch (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT Bool := do
      for i in [mInfo.getFirstDiscrPos : mInfo.getFirstAltPos] do
        if !(← isCstMatchProp args[i]!) then return false
      return true

    mkLambdaStackContext
      (f : Expr) (args : Array Expr) (idxDiscr : Nat) (e : Expr) : TranslateEnvT LambdaStackContext := do
      lambdaTelescope e fun xs b =>
        return { params := xs , body := mkAppN f (args.set! idxDiscr b), context := ← getLCtx }

    @[always_inline, inline]
    iteResult
      (rtype : Expr) (cond : Expr) (pdecide : Expr)
      (extra_args : Array Expr) (e1 : Expr) (e2 : Expr) : TranslateEnvT Expr := do
      let iteExpr := mkApp5 (← mkIteOp) rtype cond pdecide e1 e2
      if !extra_args.isEmpty
      then return mkAppN iteExpr extra_args
      else return iteExpr

    @[always_inline, inline]
    stackContinuity (stack : List ConstMatchStack) (res : Option Expr) : TranslateEnvT (Option (List ConstMatchStack)) := do
      match stack with
      | [] => return none

      | .CMatchIteThen rtype cond pdecide mInfo extra_args e1 e2 :: xs =>
           let e1' := Option.getD res e1
           return (.CMatchIteElse rtype cond pdecide mInfo extra_args e1' e2 :: xs)

      | .CMatchIteElse rtype cond pdecide _mInfo extra_args e1 e2 :: xs =>
          return (.CMatchIteReturn rtype cond pdecide extra_args e1 (Option.getD res e2) :: xs)

      | .CMatchDIteThen retType pcond pdecide mInfo extra_args e1 e2 :: xs =>
           let e1' ← withLCtx' e1.context $ mkLambdaFVars e1.params (Option.getD res e1.body)
           return (.CMatchDIteElse retType pcond pdecide mInfo extra_args e1' e2 :: xs)

      | .CMatchDIteElse rtype cond pdecide _mInfo extra_args e1 e2 :: xs =>
          let e2' ← withLCtx' e2.context $ mkLambdaFVars e2.params (Option.getD res e2.body)
          return (.CMatchDIteReturn rtype cond pdecide extra_args e1 e2' :: xs)

      | .CMatchRHS cm margs extra_args idxArg mInfo argInfo pargs rhs idxRhs :: xs =>
           let rhs' ← withLCtx' rhs.context $ mkLambdaFVars rhs.params (Option.getD res rhs.body)
           let nextRhs ←
               if idxRhs + 1 ≥ argInfo.mInfo.arity then pure rhs
               else mkLambdaStackContext cm margs idxArg argInfo.args[idxRhs + 1]!
           return (.CMatchRHS cm margs extra_args idxArg mInfo argInfo (pargs.set! idxRhs rhs') nextRhs (idxRhs + 1) :: xs)

      | _ => throwEnvError "constMatchPropagationAux?.stackContinuity: unexpected continuity !!!"


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
@[always_inline, inline]
def constMatchPropagation?
  (f : Expr) (args : Array Expr) (mInfo : MatcherInfo) : TranslateEnvT (Option Expr) :=
     constMatchPropagationAux? [.CMatchInit f args mInfo]


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
  constMatchPropagation? f margs mInfo

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
      - withMatchContext h2 $ optimizer tᵢ
-/
@[always_inline, inline]
partial def optimizeMatchAlt
  (mInfo : MatchInfo) (args : Array Expr)
  (optimizer : Expr -> TranslateEnvT Expr) (altIdx : Nat) (rhs : Expr) : TranslateEnvT Expr := do
  let currIdx := altIdx - mInfo.mInfo.getFirstAltPos
  let h ← addNotEqPatternToContext (← get).optEnv.matchInContext 0 currIdx
  withMatchAlts mInfo $ fun alts => do
    forallTelescope (← inferType alts[currIdx]!) fun xs b => do
      let lhs := b.getAppArgs
      lambdaBoundedTelescope (← optimizeLambdaTypes rhs) (max 1 (← retrieveAltsArgs lhs).altArgs.size) fun params body => do
        let mut mcontext := h
        let mut idxParams := 0
        for j in [mInfo.mInfo.getFirstDiscrPos : mInfo.mInfo.getFirstAltPos] do
          let idxLhs := j - mInfo.mInfo.getFirstDiscrPos
          let pattern := lhs[idxLhs]!
          let nextIdx := idxParams + (← retrieveAltsArgs #[pattern]).altArgs.size
          if !isFVarPattern pattern then
            -- add EqPattern in match context only when it's a constructor
            let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
            mcontext := addPatternInContext mcontext args[j]! patternExpr (some $ params.extract idxParams nextIdx)
          idxParams := nextIdx
        withMatchContext mcontext $ do
           mkExpr (← mkLambdaFVars params (← optimizer body))

  where

   onlyOnePattern (lhs : Array Expr) : TranslateEnvT Bool := do
     let mut onlyOne := false
     for i in [:lhs.size] do
       if !isFVarPattern lhs[i]! then
         if !onlyOne then
           onlyOne := true
         else return false
     return onlyOne

   addNotEqPatternToContext (h : MatchContextMap) (idx : Nat) (stopIdx : Nat) : TranslateEnvT MatchContextMap := do
     if idx ≥ stopIdx then
       return h
     else
       let h' ← withMatchAlts mInfo $ fun alts => do
         forallTelescope (← inferType alts[idx]!) fun xs b => do
           let lhs := b.getAppArgs
           let mut mcontext := h
           if ← onlyOnePattern lhs then
             -- add NotEqPattern when there is only one pattern that is a constructor
             for j in [mInfo.mInfo.getFirstDiscrPos : mInfo.mInfo.getFirstAltPos] do
               let idxLhs := j - mInfo.mInfo.getFirstDiscrPos
               let pattern := lhs[idxLhs]!
               if !isFVarPattern pattern then
                 -- add NotEqPattern in match context only when it's a constructor
                 let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
                 mcontext := addPatternInContext mcontext args[j]! patternExpr none
           return mcontext
       addNotEqPatternToContext h' (idx + 1) stopIdx

   optimizeLambdaTypes (e : Expr) : TranslateEnvT Expr := do
     match e with
     | Expr.lam n t b bi =>
        let t' ← optimizer t
        withLocalDecl n bi t' fun x => do
          mkLambdaFVars #[x] (← optimizeLambdaTypes (b.instantiate1 x))
     | _ => return e

/--  Apply the following reduction rules, such that:
     Given match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

     - When ∀ i ∈ [1..m], ¬ tᵢ.hasLooseBVars ∧ tᵢ = t₁
         - return `some t₁`

     - When ∀ j ∈ [1..n],
             eⱼ := pm ∈ matchInContext ∧ p₍₁₎₍ⱼ₎ := EqPattern altArgs ∈ pm ∧ ¬ isFVarPattern p₍₁₎₍ⱼ₎
          - return `some t₁`

     - When ∀ j ∈ [1..n],
            eⱼ := pm ∈ matchInContext ∧ p₍₂₎₍ⱼ₎ := EqPattern altArgs ∈ pm ∧ ¬ isFVarPattern p₍₂₎₍ⱼ₎
          - return `some t₂`
     ...
     - When ∀ j ∈ [1..n],
            eⱼ := pm ∈ matchInContext ∧ p₍ₘ₎₍ⱼ₎ := EqPattern altArgs ∈ pm ∧ ¬ isFVarPattern p₍ₘ₎₍ⱼ₎
          - return `some tₘ`

     - When ∀ j ∈ [1..n], isFVar p₍ₘ₎₍ⱼ₎ ∧
            ∀ k ∈ [1..m-1],
              ∃ h ∈ [1..n],
                  ( eₕ := pm ∈ matchInContext ∧ p₍ₖ₎₍ₕ₎ := NotEqPattern ∈ pm )
           - return `some tₘ`

     - Otherwise:
         - return none
-/
def elimMatch?
  (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let some mInfo ← isMatcher? (mkAppN f args) | return none
  if let some re ← commonRhs? mInfo args then return re
  if let some re ← matchInHyps? mInfo args then return re
  lastPatternReduction? mInfo args

where

  @[always_inline, inline]
  commonRhs? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
    let firstRhs := getLambdaBody args[mInfo.mInfo.getFirstAltPos]!
    -- Rhs can't be a function with loose BVars.
    if firstRhs.hasLooseBVars then return none
    for i in [mInfo.mInfo.getFirstAltPos + 1 : mInfo.mInfo.arity] do
      -- NOTE: No need to check for looseBVars as we are expecting equality
      if !(← exprEq (getLambdaBody args[i]!) firstRhs) then return none
    return firstRhs

  @[always_inline, inline]
  allPatternsInHyp
    (mInfo : MatchInfo) (args : Array Expr)
    (alt : Expr) (h : MatchContextMap) : TranslateEnvT (Bool × Array Expr) := do
    forallTelescope (← inferType alt) fun xs b => do
      let lhs := b.getAppArgs
      let mut patternArgs := #[]
      for j in [mInfo.mInfo.getFirstDiscrPos : mInfo.mInfo.getFirstAltPos] do
        let idxLhs := j - mInfo.mInfo.getFirstDiscrPos
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
    withMatchAlts mInfo $ fun alts => do
     for i in [mInfo.mInfo.getFirstAltPos : mInfo.mInfo.arity] do
       let altIdx := i - mInfo.mInfo.getFirstAltPos
       let (inContext, altArgs) ← allPatternsInHyp mInfo args alts[altIdx]! h
       if inContext then
         if altArgs.isEmpty
         then return getLambdaBody args[i]! -- case when there is no free variables in pattern.
         else return args[i]!.beta altArgs
     return none

  @[always_inline, inline]
  allFVarsPatterns (alt : Expr) : TranslateEnvT Bool := do
    -- NOTE: we avoid performing forallTelescope at this stage
    let lhs := (← inferType alt).getForallBody.getAppArgs
    for i in [:lhs.size] do
      if !lhs[i]!.isBVar then
        return false
     return true

  @[always_inline, inline]
  existsNotEqPattern
    (mInfo : MatchInfo) (args : Array Expr)
    (alt : Expr) (h : MatchContextMap) : TranslateEnvT Bool := do
    forallTelescope (← inferType alt) fun xs b => do
      let lhs := b.getAppArgs
      for j in [mInfo.mInfo.getFirstDiscrPos : mInfo.mInfo.getFirstAltPos] do
        let idxLhs := j - mInfo.mInfo.getFirstDiscrPos
        let pattern := lhs[idxLhs]!
        if !isFVarPattern pattern then
          let patternExpr ← mkForallFVars xs (usedOnly := true) pattern
          if let some pm := h.get? args[j]! then
            if let some .NotEqPattern := pm.get? patternExpr then return true
      return false

  @[always_inline, inline]
  lastPatternReduction? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option Expr) := do
     let h := (← get).optEnv.matchInContext
     withMatchAlts mInfo $ fun alts => do
       -- all last patterns are FVars
        if (← allFVarsPatterns alts[alts.size - 1]!) then
          for i in [:alts.size - 1] do
            if !(← existsNotEqPattern mInfo args alts[i]! h) then
              return none
          let discrs := args.extract mInfo.mInfo.getFirstDiscrPos mInfo.mInfo.getFirstAltPos
          return args[mInfo.mInfo.arity - 1]!.beta discrs
        else return none

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
 if isCasesOnRecursor (← getEnv) n then return none
 let some mInfo ← getMatcherRecInfo? n dlevel | return none
 let i_args := args.take mInfo.getFirstDiscrPos
 let params ← getImplicitParameters f i_args
 let genericArgs := Array.filterMap (λ p => if p.isGeneric then some p.effectiveArg else none) params
 let auxApp ← mkLambdaFVars genericArgs (mkAppN f i_args)
 let cInfo ← getConstEnvInfo n
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
