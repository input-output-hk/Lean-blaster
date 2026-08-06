import Lean
import Blaster.Optimize.RetentionCounters
import Blaster.Optimize.OptimizeStack
import Blaster.Optimize.Rewriting.NormalizeMatch
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Telescope

open Lean Meta Elab Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

@[always_inline, inline]
partial def eraseMatchRhsRewriteCache (mInfo : MatchInfo) : TranslateEnvT Unit := do
  let rec visit (idx : USize) (stop : USize) (offset : USize) : TranslateEnvT Unit := do
    if idx ≥ stop then return ()
    else
      freeRewriteCacheReuse mInfo.nameExpr (idx - offset)
      visit (idx + 1) stop offset
  let ⟨_, _, _, _, _, _, _, _, _, memCache, ⟨_, _, _, _, curCtx, _, _, _, _, _⟩, _, _, _⟩ := (← get).optEnv
  if (← memCache.contextReuseCache.findRaw mInfo.nameExpr 0 curCtx).isSome then
    let start := mInfo.getFirstAltPos.toUSize
    visit start mInfo.arity.toUSize start
  else return ()

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

/-- Given `f x₁ ... xₙ` return `true` when the following conditions are satisfied:
     -  ∃ i ∈ [1..n], isExplicit xᵢ ∧
     -  ∀ i ∈ [1..n], isExplicit xᵢ → isCstProp xᵢ ∨ isPropFunType f xₓ
     with
       - isCstProp e := isCstMatchProp e IF funpropagaton
         isCstProp e := isNormConstructor e  Otherwise
       - isPropFunType e := isProp e.Type ∨ isFunType' e.Type
    NOTE: constructors may contain free variables.
-/
@[always_inline, inline]
partial def allExplicitParamsAreCtor (f : Expr) (args: Array Expr) (funPropagation := false) : TranslateEnvT Bool := do
  let pInfo ← getFunEnvInfo f
  let rec loop
    (i : Nat) (stop : Nat) (pInfoSize : Nat)
    (atLeastOneExplicitCstr : Bool := false) : TranslateEnvT Bool := do
    if i < stop then
      let e := args[i]!
      let p := pInfo.paramsInfo[i]!
      if i < pInfoSize then
        if p.isExplicit
        then
          if funPropagation then
            let res ← isCstIteMatch e
             if (← pure res <||> isPropFunType p e)
             then loop (i+1) stop pInfoSize (atLeastOneExplicitCstr || res && (← isIteOrMatch e))
             else return false
          else
             let cstProp ← isNormConstructor e
             if (← pure cstProp <||> isPropFunType p e)
             then loop (i+1) stop pInfoSize (atLeastOneExplicitCstr || cstProp)
             else return false
        else loop (i+1) stop pInfoSize atLeastOneExplicitCstr
      else return atLeastOneExplicitCstr
    else return atLeastOneExplicitCstr
  loop 0 args.size pInfo.paramsInfo.size

  where
    @[always_inline, inline]
    isFunExpr (e : Expr) : TranslateEnvT Bool := do
      match e with
      | Expr.lam .. => return true
      | Expr.fvar fv => return isFunType' (← fv.getEnvType)
      | Expr.const n _ =>
           let cInfo ← getConstEnvInfo n
           return isFunType' cInfo.type
      | Expr.app .. =>
          let (f', args') := getAppFnWithArgs e
          let fInfo ← getFunEnvInfo f'
          return isFunType' (← inferAppType fInfo.type args')
      | Expr.proj .. =>
          if e.hasMVar
          then return false
          else return isFunType' (← inferTypeEnv e)
      | _ => return false

    @[always_inline, inline]
    isPropFunType (p : ParamInfo) (e : Expr) : TranslateEnvT Bool := do
     if p.isProp then return true
     isFunExpr e

def getNamedPatternExpr (p : Expr) : TranslateEnvT Expr := do
 match p with
 | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) _pn) pe) _ph => getNamedPatternExpr pe
 | Expr.app f a => Expr.updateAppExpr! p (← getNamedPatternExpr f) (← getNamedPatternExpr a)
 | _ => return p

inductive MatchResult where
  | NoMatch : MatchResult -- result when cannot unify
  | UnifyMatch : MatchResult -- result unifies such that all mvars in pattern match have been assigned
  | PotentialMatch : MatchResult -- result unifies but not all mvars in pattern match have been assigned
deriving Repr, Inhabited


def joinMatchResult (x : MatchResult) (y : MatchResult) : MatchResult :=
 match x, y with
 | p@.NoMatch, _
 | _, p@.NoMatch => p
 | p@.PotentialMatch, _
 | _, p@.PotentialMatch => p
 | _, _ => x

/-- Performs unification on lhs and rhs
     - Return `UnifyMatch` when both `lhs` and `rhs` can unify up to metavariable
     - Return `PotentialMatch` when `lhs` unifies with `rhs` before lhs reduces to a ground term (i.e., a unary constructor or a metavariable), e.g.,
         - `lhs := some (.Int.ofNat y)` and `rhs := some x`
     - Return `NoMatch` when `lhs` cannot be unified with `rhs`.
-/
partial def isPatternMatch (lhs : Expr) (rhs : Expr) : TranslateEnvT MatchResult := do
 if exprEq lhs rhs then return .UnifyMatch
 else
  match lhs with
  | Expr.mvar _ =>
      -- assign mvar with rhs
      assignMVar lhs rhs
      return .UnifyMatch

  | Expr.lit l =>
        match rhs with
        | Expr.lit _ => return .NoMatch -- top-level `exprEq lhs rhs` already ruled out equality
        | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n2))) _pn  =>
            match l with
            | .natVal n1 => if n1 < n2
                            then return .NoMatch
                            else return .PotentialMatch
            | _ => return .NoMatch -- unreachable case
        | Expr.app (Expr.const ``String.mk _) _ =>
            match l with
            | .strVal s => isPatternMatch (← stringToCtor s) rhs
            | _ => return .NoMatch -- unreachable case
        | _ => return .PotentialMatch -- case when rhs is an expression

  | Expr.fvar _ =>
       -- NOTE: fvar in pattern match can only correspond to polymorphic types
       -- Rhs is expected to be the same fvar (captured by physical equality)
       return .NoMatch

  | Expr.const _ _ =>
       match rhs with
       | Expr.const n2 _ =>
            -- top-level `exprEq lhs rhs` already ruled out physical equality
            if (← isCtorName n2) then return .NoMatch
            else return .PotentialMatch -- case when rhs is an expression
       | _ =>
           if ← isCtorExpr rhs.getAppFn
           then return .NoMatch
           else return .PotentialMatch -- case when rhs is an expression

  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) pn) pe) _ph =>
       -- assigning named pattern mvars
       assignMVar pn (← getNamedPatternExpr pe)
       isPatternMatch pe rhs

  | Expr.app f1 a1 =>
        match rhs with
        | Expr.lit (.natVal n2) =>
             match f1 with
             | Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n1)) =>
                   if n2 < n1
                   then return .NoMatch
                   else isPatternMatch a1 (← mkNatLitExpr (Nat.sub n2 n1))
             | _ => return .NoMatch -- unreachable: Nat constructor expected
        | Expr.lit (.strVal s) =>
             match f1 with
             | Expr.const ``String.mk _ => isPatternMatch lhs (← stringToCtor s)
             | _ => return .NoMatch -- unreachable: String constructor expected
        | Expr.const n _ =>
           if (← isCtorName n)
           then return .NoMatch
           else return .PotentialMatch -- case when rhs is an expression

        | Expr.app f2 a2 =>
             match f1, f2 with
             | Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n1)),
               Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n2)) =>
                if n1 < n2 then
                  isPatternMatch a1 (← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr (Nat.sub n2 n1)) a2)
                else if n1 == n2 then
                  isPatternMatch a1 a2
                else isPatternMatch (← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr (Nat.sub n1 n2)) a1) a2

             | Expr.const ``Int.ofNat _, Expr.const ``Int.neg _ =>
                  match a2 with
                  | Expr.app (Expr.const ``Int.ofNat _) _ => return .NoMatch
                  | _ => return .PotentialMatch -- case when rhs is an expression

             | Expr.const ``Int.neg _, Expr.const ``Int.ofNat _ => return .NoMatch

             | Expr.const ``Int.negSucc _, Expr.const ``Int.neg _ =>
                  match a2 with
                  | Expr.app (Expr.const ``Int.ofNat _) n2 => isPatternMatch a1 n2
                  | _ => return .PotentialMatch -- case when rhs is an expression

             | Expr.const ``Int.neg _, Expr.const ``Int.negSucc _ =>
                  match a1 with
                  | Expr.app (Expr.const ``Int.ofNat _) n1 => isPatternMatch n1 a2
                  | _ => return .NoMatch -- unreachable
             | _, _=>
                if exprEq f1 f2 then isPatternMatch a1 a2
                else
                  let p ← isPatternMatch f1 f2
                  match p with
                  | .UnifyMatch => isPatternMatch a1 a2
                  | .PotentialMatch => return joinMatchResult p (← isPatternMatch a1 a2)
                  | .NoMatch => return p

        | _ => return .PotentialMatch -- case when rhs is an fvar/mvar/let/forallE

  | _ => return .NoMatch -- unreachable: only const, app, mvar, fvar and lit expected as pattern match


@[always_inline, inline]
def isNoMatchResult (x : MatchResult) : Bool :=
  match x with
  | .NoMatch => true
  | _ => false

@[always_inline, inline]
def isUnifyMatchResult (x : MatchResult) : Bool :=
  match x with
  | .UnifyMatch => true
  | _ => false

@[always_inline, inline]
def isPotentialMatchResult (x : MatchResult) : Bool :=
  match x with
  | .PotentialMatch => true
  | _ => false

@[always_inline, inline]
def patternMatchDiscrs (alt : Expr) (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT (Array Expr × MatchResult) := do
 let rec visit_discrs?
  (lhs : Array Expr) (args : Array Expr)
  (idx : Nat) (stop : Nat) (matchHit : MatchResult) : TranslateEnvT MatchResult := do
  if idx ≥ stop then return matchHit
  else
    let idxLhs := idx - mInfo.getFirstDiscrPos
    let pattern := lhs[idxLhs]!
    let unifyRes ← isPatternMatch pattern args[idx]!
    if isNoMatchResult unifyRes
    then return unifyRes
    else visit_discrs? lhs args (idx + 1) stop (joinMatchResult matchHit unifyRes)
 let altsMeta ← forallMetaTelescopeEnv alt
 let lhs := altsMeta.instExpr.getAppArgs
 let matchHit ← visit_discrs? lhs args mInfo.getFirstDiscrPos mInfo.getFirstAltPos .UnifyMatch
 return (altsMeta.mvarArgs, matchHit)


@[always_inline, inline]
def instantiateUnifiedMVars (mvars : Array Expr) : TranslateEnvT (Array Expr) := do
 let mAssignments := (← get).optEnv.mAssignments
 let rec visit (idx : Nat) (stop : Nat) (mvars : Array Expr) : TranslateEnvT (Array Expr) := do
    if idx ≥ stop then
      return mvars
    else
      let val := mAssignments.getD mvars[idx]! instCacheMiss
      if !exprEq val instCacheMiss then
        if val.hasMVar
        then visit (idx + 1) stop (mvars.set! idx (← instantiateSharedMVars' val mAssignments))
        else visit (idx + 1) stop (mvars.set! idx val)
      else visit (idx + 1) stop mvars
  visit 0 mvars.size mvars

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
    Assume that `normChoiceApplication` has already applied to push extra arguments in match rhs`
-/
def reduceMatch? (args : Array Expr) (mInfo : MatchInfo) (resolveArgs := false) : TranslateEnvT (Option BetaLambdaResult) := do
 let args ← resolveArgsWithEqualityStack args
 if !(← allMatchDiscrsAreCtor args mInfo.getFirstDiscrPos mInfo.getFirstAltPos) then return none
 let alts ← getMatchAlts args mInfo
 visit_alts? args alts mInfo.getFirstAltPos mInfo.arity false

   where
    visit_alts?
      (args : Array Expr) (alts : Array Expr)
      (idx : Nat) (stop : Nat) (isPrevPotentialMatch : Bool) : TranslateEnvT (Option BetaLambdaResult) := do
      if idx ≥ stop then return none
      else
        let altIdx := idx - mInfo.getFirstAltPos
        let (mvarArgs, matchHit) ← patternMatchDiscrs alts[altIdx]! args mInfo
        if isUnifyMatchResult matchHit && !isPrevPotentialMatch then
          -- erase context
          eraseMatchRhsRewriteCache mInfo
          betaLambdaEnv args[idx]! (← instantiateUnifiedMVars mvarArgs)
        else visit_alts? args alts (idx + 1) stop (isPrevPotentialMatch || isPotentialMatchResult matchHit)

    allMatchDiscrsAreCtor (args : Array Expr) (idx : Nat) (stop : Nat) : TranslateEnvT Bool := do
     if idx ≥ stop then return true
     else if !(← isNormConstructor args[idx]!) then return false
     else allMatchDiscrsAreCtor args (idx + 1) stop

    resolveArgsWithEqualityStack (args : Array Expr) : TranslateEnvT (Array Expr) := do
     let ⟨_, _, _, _, _, _, _, ⟨_, equalityMap⟩, _, _, ⟨_, _, _, _, _, _, active, _, _, _⟩, _, _, _⟩ := (← get).optEnv
     let rec visit (idx : Nat) (stop : Nat) (args : Array Expr) : TranslateEnvT (Array Expr) := do
       if idx ≥ stop then return args
       else
         match (← ContextMap.findRaw equalityMap active args[idx]!) with
         | some r => visit (idx + 1) stop (args.set! idx r)
         | none => visit (idx + 1) stop args
     if resolveArgs then visit mInfo.getFirstDiscrPos mInfo.getFirstAltPos args
     else return args


/-- Apply the following constant propagation rules on match expressions, such that:
    Given match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

    - When ∀ i ∈ [1..n], isCstMatchProp eᵢ ∧
             ∃ j ∈ [1..n],
               `eⱼ := Blaster.dite' c (fun h : c => d₁) (fun h : ¬ c => d₂)` ∧
                (i ≠ j → gᵢ = eᵢ) ∧ (i = j → gᵢ = d₁) ∧
                (i ≠ j → hᵢ = eᵢ) ∧ (i = j → hᵢ = d₂)
      Return
         `Blaster.dite' c (fun h : c => match₁ g₁, ..., gₙ with ...) (fun h : ¬ c => match₁ h₁, ..., hₙ with ...)`

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

    Assume that `normChoiceApplication` has already applied to push extra arguments in match rhs`
-/
def constMatchPropagation?
  (cm : Expr) (cargs : Array Expr) (mInfo : MatchInfo)
  (prevInApp : Bool) (resolveArgs := false) : TranslateEnvT (Option OptimizeStack) := do
  if !(← allDiscrsAreCstMatch mInfo.getFirstDiscrPos mInfo.getFirstAltPos)
  then return none
  else loop mInfo.getFirstDiscrPos mInfo.getFirstAltPos

  where
    loop (idx : Nat) (stop : Nat) : TranslateEnvT (Option OptimizeStack) := do
      if idx ≥ stop then return none
      else if let some r ← isDiteArg idx then return r
      else if let some r ← isMatchArg idx then return r
      else loop (idx + 1) stop

    allDiscrsAreCstMatch (idx : Nat) (stop : Nat) (atLeastOneMatchITE := false) : TranslateEnvT Bool := do
      if idx ≥ stop then return atLeastOneMatchITE
      else
        let p := cargs[idx]!
        let res ← isCstIteMatch p
        if res then
          allDiscrsAreCstMatch (idx + 1) stop (atLeastOneMatchITE || (← isIteOrMatch p))
        else return false


    pushMatchInLambda (f : Expr) (args : Array Expr) (idxDiscr : Nat) (e : Expr) : TranslateEnvT Expr := do
       -- NOTE: we can safely telescope as allDiscrsAreCstMatch guarantees match/ite are not functions
       lambdaTelescope e fun fvars body => do
         mkLambdaFVarsExpr fvars (← mkAppRangeExprWithSetAt f 0 args.size args idxDiscr body)

    pushMatchInDIteExpr (f : Expr) (args : Array Expr) (idxDiscr : Nat) (e : Expr) : TranslateEnvT Expr := do
      match e with
      | Expr.lam n t body bi =>
           if body.hasLooseBVars
           then pushMatchInLambda f args idxDiscr e
           else mkLambdaExpr n bi t (← mkAppRangeExprWithSetAt f 0 args.size args idxDiscr body)
      | _ => throwEnvError "pushMatchInDIteExpr: lambda term expected !!!"

    @[always_inline, inline]
    isDiteArg (idx : Nat) : TranslateEnvT (Option OptimizeStack) := do
      if let some (_psort, pcond, e1, e2) := dite'? cargs[idx]! then
        -- retention diagnostics (p0c): dite pull-out duplicates the outer
        -- match into both branches
        if ← Retention.enabledIO then
          Retention.p0cDitePull.modify (· + 1)
          Retention.p0cOuterAlts.modify (· + (mInfo.arity - mInfo.getFirstAltPos))
        -- erase context
        eraseMatchRhsRewriteCache mInfo
        -- NOTE: we also need to set the sort type for the pulled dite to meet
        -- the return type of the embedded match
        let retType := getAppliedMatchType cargs[mInfo.getFirstDiscrPos - 1]! 0
        let e1' ← pushMatchInDIteExpr cm cargs idx e1
        let e2' ← pushMatchInDIteExpr cm cargs idx e2
        -- NOTE: we need to propagate the reuse context to the new then and else expressions
        propagateReuseContext e1 e1' 0
        propagateReuseContext e2 e2' 0
        let dite_op ← mkBlasterDIteOp
        let pInfo ← getFunEnvInfo dite_op
        let dite_args := #[retType, pcond, e1', e2']
        setIsAppArg prevInApp
        if resolveArgs
        then return some (.AppOptimizeImplicitArgs dite_op dite_args 0 0 4 pInfo prevInApp)
        else
          -- all arguments have already been optimized for both pulled ite and parent match
          -- we only trigger optimization for then and else (e.g., stop at 4)
          return some (.AppOptimizeExplicitArgs dite_op dite_args 2 4 pInfo none prevInApp)
      else return none

    @[always_inline, inline]
    isMatchArg (idx : Nat) : TranslateEnvT (Option OptimizeStack) := do
      if let some argInfo ← isMatcher? cargs[idx]!.getAppFn then
        -- retention diagnostics (p0c): case-of-case pull-out duplicates
        -- the outer match into every alternative of the inner match
        if ← Retention.enabledIO then
          Retention.p0cMatchPull.modify (· + 1)
          Retention.p0cInnerAlts.modify (· + (argInfo.arity - argInfo.getFirstAltPos))
          Retention.p0cOuterAlts.modify (· + (mInfo.arity - mInfo.getFirstAltPos))
        -- erase context
        eraseMatchRhsRewriteCache mInfo
        let mut pargs := cargs[idx]!.getAppArgs
        for i in [argInfo.getFirstAltPos : argInfo.arity] do
          -- NOTE: No need to propagate reuse context as match name has not changed
          pargs ← pargs.modifyM i (pushMatchInLambda cm cargs idx)
        -- NOTE: we also need to set the return type for pulled over match
        -- to meet the return type of the embedded match.
        let idxType := argInfo.getFirstDiscrPos - 1
        let retType := getAppliedMatchType cargs[mInfo.getFirstDiscrPos - 1]! 0
        pargs ← pargs.modifyM idxType (updateMatchReturnType retType)
        let pInfo ← getFunEnvInfo argInfo.nameExpr
        setIsAppArg prevInApp
        if resolveArgs
        then return some (.AppOptimizeImplicitArgs argInfo.nameExpr pargs 0 0 pargs.size pInfo prevInApp)
        else
          -- all arguments have already been optimized for both pulled and parent match
          -- we only trigger optimization for alts (e.g., stop at argInfo.arity)
          return some (.AppOptimizeExplicitArgs
                        argInfo.nameExpr pargs argInfo.getFirstAltPos
                        argInfo.arity pInfo argInfo prevInApp)
      else return none

/-- Given a match expression perform the following:
    - try reduceMatch?
    - try constMatchpropagation?.
    - try normMatchExpr? only when flag matchToIte is set
-/
@[always_inline, inline]
def matchReduction?
  (f : Expr) (args : Array Expr) (mInfo : MatchInfo) (prevInApp : Bool)
  (matchToIte := false) (resolveArgs := false) : TranslateEnvT (Option OptimizeStack) := do
    -- try match reduction first
    if let some r ← reduceMatch? args mInfo resolveArgs then
      return some (.InitOptimizeExpr r.betaReduced r.prevMVarIdDecls)
    -- try to apply match constant propagation rules
    if let some r ← constMatchPropagation? f args mInfo prevInApp resolveArgs then return r
    if matchToIte then
      match ← normMatchExpr? args mInfo with
      | none => return none
      | some r => return some (.InitOptimizeExpr r)
    else return none

@[always_inline, inline]
private def addNotEqPatternInContext (nextCtxId : CtxId) (discr : Expr) (pattern : Expr) : TranslateEnvT Unit := do
  match (← get).optEnv.matchInContext.get? discr with
  | none =>
       let pset ← IO.mkRef (HashSet.emptyWithCapacity.insert pattern : HashSet PtrExpr)
       let refEntry ← IO.mkRef [(nextCtxId, pset)]
       modifyOptEnv
         fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, matchInContext, o10, o11, o12, o13, o14⟩ =>
          ⟨o1, o2, o3, o4, o5, o6, o7, o8, matchInContext.insert discr refEntry, o10, o11, o12, o13, o14⟩
  | some refEntry =>
       let rec findAndUpdate (xs : List (ContextEntry (IO.Ref NotEqPatterns))) : TranslateEnvT Unit := do
         match xs with
         | [] =>
              let pset ← IO.mkRef (HashSet.emptyWithCapacity.insert pattern : HashSet PtrExpr)
              refEntry.modify (λ l => (nextCtxId, pset) :: l)
         | (ctxId, refSet) :: xs' =>
              if nextCtxId == ctxId then
                refSet.modify (λ pset => pset.insert pattern)
              else findAndUpdate xs'
       findAndUpdate (← refEntry.get)

@[always_inline, inline]
private def propagateNotEqPatternContext (discr : Expr) (nextCtxId : CtxId) : TranslateEnvT Unit := do
  let ⟨_, ⟨_, _, _, _, _, _, _, ⟨_, equalityMap⟩, matchInContext, _, _, _, _, _⟩⟩ ← get
  match ← ContextMap.findRaw' equalityMap nextCtxId discr with
  | none => return ()
  | some v =>
     match ← ContextMap.findRaw' matchInContext nextCtxId discr with
     | none => return ()
     | some pset =>
        let refEntry ← IO.mkRef [(nextCtxId, pset)]
        modifyOptEnv
          fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, matchInContext, o10, o11, o12, o13, o14⟩ =>
              ⟨o1, o2, o3, o4, o5, o6, o7, o8, matchInContext.insert v refEntry, o10, o11, o12, o13, o14⟩

def isFVarPattern (e : Expr) : Bool :=
 match e with
 | Expr.fvar .. => true
 | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) _n) pe) _h => isFVarPattern pe
 | _ => false


def addNamedPatternToEqualityMap (p : Expr) (nextCtxId : CtxId) (updatedCtx : Bool) : TranslateEnvT Bool := do
  match p with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) pn) pe) _ph =>
       let pe' ← removeNamedPatternExpr pe
       updateEqualityMap pn pe' nextCtxId
       addNamedPatternToEqualityMap pe nextCtxId true
  | Expr.app f a =>
       addNamedPatternToEqualityMap a nextCtxId (← addNamedPatternToEqualityMap f nextCtxId updatedCtx)
  | _ => return updatedCtx

@[always_inline, inline]
partial def unifyAndUpdateEqMap (lhs : Expr) (rhs : Expr) (nextCtxId : CtxId) (updatedCtx : Bool) : TranslateEnvT Bool := do
  let rec visit (lhs : Expr) (rhs : Expr) (stk : List (Expr × Expr)) (updatedCtx : Bool) : TranslateEnvT Bool := do
    match lhs with
    | Expr.lit l =>
          match rhs with
          | Expr.lit _ =>
               if exprEq lhs rhs then
                 match stk with
                 | [] => return updatedCtx
                 | (lhs', rhs') :: xs => visit lhs' rhs' xs updatedCtx
               else return updatedCtx

          | Expr.app (Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n2))) pn =>
               match l with
               | .natVal n1 =>
                     if n1 < n2
                     then return updatedCtx
                     else
                       updateEqualityMap pn (← mkNatLitExpr (Nat.sub n1 n2)) nextCtxId
                       match stk with
                       | [] => return true
                       | (lhs', rhs') :: xs => visit lhs' rhs' xs true
               | _ => return updatedCtx -- unreachable case

          | Expr.app (Expr.const ``String.mk _) _ =>
               match l with
               | .strVal s => visit (← stringToCtor s) rhs stk updatedCtx
               | _ => return updatedCtx -- unreachable case

          | _ =>
              -- case when rhs is an expression/fvar
              updateEqualityMap rhs lhs nextCtxId
              match stk with
              | [] => return true
              | (lhs', rhs') :: xs => visit lhs' rhs' xs true

    | Expr.fvar _ =>
          match rhs with
          | Expr.fvar _ =>
               let isNotEq := !exprEq lhs rhs
               let updatedCtx := updatedCtx || isNotEq
               if isNotEq then -- polymorphic type case when exprEq is satisfied
                 updateEqualityMap lhs rhs nextCtxId
               match stk with
               | [] => return updatedCtx
               | (lhs', rhs') :: xs => visit lhs' rhs' xs updatedCtx
          | _ =>
             updateEqualityMap lhs rhs nextCtxId
             match stk with
             | [] => return true
             | (lhs', rhs') :: xs => visit lhs' rhs' xs true

    | Expr.const n1 _ =>
         match rhs with
         | Expr.const n2 _ =>
            if exprEq lhs rhs then
              match stk with
              | [] => return updatedCtx
              | (lhs', rhs') :: xs => visit lhs' rhs' xs updatedCtx
            else if (← isCtorName n1) && !(← isCtorName n2) then
              updateEqualityMap rhs lhs nextCtxId
              match stk with
              | [] => return true
              | (lhs', rhs') :: xs => visit lhs' rhs' xs true
            else return updatedCtx
         | _ =>
           if ← isCtorExpr rhs.getAppFn
           then return updatedCtx
           else
              -- case when rhs is an expression/fvar
              updateEqualityMap rhs lhs nextCtxId
              match stk with
              | [] => return true
              | (lhs', rhs') :: xs => visit lhs' rhs' xs true

    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``namedPattern _) _t) pn) pe) _ph =>
        updateEqualityMap pn (← removeNamedPatternExpr pe) nextCtxId
        visit pe rhs stk true

    | Expr.app f1 a1 =>
          match rhs with
          | Expr.lit (.natVal n2) =>
               match f1 with
               | Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n1)) =>
                    if n2 < n1
                    then return updatedCtx
                    else visit a1 (← mkNatLitExpr (Nat.sub n2 n1)) stk updatedCtx
               | _ => return updatedCtx -- unreachable: Nat constructor expected

          | Expr.lit (.strVal s) =>
               match f1 with
               | Expr.const ``String.mk _ => visit lhs (← stringToCtor s) stk updatedCtx
               | _ => return updatedCtx -- unreachable: String constructor expected

          | Expr.const n _ =>
               if (← isCtorName n) then
                 return updatedCtx
               else
                 updateEqualityMap rhs (← removeNamedPatternExpr lhs) nextCtxId
                 match stk with
                 | [] => return updatedCtx
                 | (lhs', rhs') :: xs => visit lhs' rhs' xs updatedCtx

          | Expr.app f2 a2 =>
              match f1, f2 with
              | Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n1)),
                Expr.app (Expr.const ``Nat.add _) (Expr.lit (Literal.natVal n2)) =>
                  if n1 < n2 then
                    visit a1 (← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr (Nat.sub n2 n1)) a2) stk updatedCtx
                  else if n1 == n2 then
                    visit a1 a2 stk updatedCtx
                  else visit (← mkApp2Expr (← mkNatAddOp) (← mkNatLitExpr (Nat.sub n1 n2)) a1) a2 stk updatedCtx

              | Expr.const ``Int.ofNat _, Expr.const ``Int.neg _ =>
                    match a2 with
                    | Expr.app (Expr.const ``Int.ofNat _) _ => return updatedCtx
                    | _ => -- case when rhs is an expression
                      updateEqualityMap rhs (← removeNamedPatternExpr lhs) nextCtxId
                      match stk with
                      | [] => return true
                      | (lhs', rhs') :: xs => visit lhs' rhs' xs true

              | Expr.const ``Int.neg _, Expr.const ``Int.ofNat _ => return updatedCtx

              | Expr.const ``Int.negSucc _, Expr.const ``Int.neg _ =>
                  match a2 with
                  | Expr.app (Expr.const ``Int.ofNat _) n2 => visit a1 n2 stk updatedCtx
                  | _ => -- case when rhs is an expression
                     updateEqualityMap rhs (← removeNamedPatternExpr lhs) nextCtxId
                     match stk with
                     | [] => return true
                     | (lhs', rhs') :: xs => visit lhs' rhs' xs true

              | Expr.const ``Int.neg _, Expr.const ``Int.negSucc _ =>
                   match a1 with
                   | Expr.app (Expr.const ``Int.ofNat _) n1 => visit n1 a2 stk updatedCtx
                   | _ => return updatedCtx -- unreachable

              | _, _ =>
                if ← isCtorExpr f2.getAppFn then
                   visit f1 f2 ((a1, a2) :: stk) updatedCtx
                else if !(← isInductiveTypeExpr rhs) then
                  -- case when rhs is an expression
                  updateEqualityMap rhs (← removeNamedPatternExpr lhs) nextCtxId
                  match stk with
                  | [] => return true
                  | (lhs', rhs') :: xs => visit lhs' rhs' xs true
                else
                  match stk with
                  | [] => return updatedCtx
                  | (lhs', rhs') :: xs => visit lhs' rhs' xs updatedCtx
          | _ =>
             -- case when rhs is an expression
             updateEqualityMap rhs (← removeNamedPatternExpr lhs) nextCtxId
             match stk with
             | [] => return true
             | (lhs', rhs') :: xs => visit lhs' rhs' xs true

    | _ => return updatedCtx -- unreachable: only const, app, fvar and lit expected as pattern match
  visit lhs rhs [] updatedCtx

@[always_inline, inline]
def updateEqMap
  (mInfo : MatchInfo) (lhs : Array Expr) (args : Array Expr) (nextCtxId : CtxId) (updatedCtx : Bool) : TranslateEnvT Bool := do
  let rec updateEntry (idx : Nat) (stop : Nat) (updatedCtx : Bool) : TranslateEnvT Bool :=  do
    if idx ≥ stop then return updatedCtx
    else
      let idxLhs := idx - mInfo.getFirstDiscrPos
      let pattern := lhs[idxLhs]!
      let updatedCtx ← unifyAndUpdateEqMap pattern args[idx]! nextCtxId updatedCtx
      let updatedCtx ← addNamedPatternToEqualityMap pattern nextCtxId updatedCtx
      -- propagate NotEqPattern w.r.t. equalityMap
      propagateNotEqPatternContext args[idx]! nextCtxId
      updateEntry (idx + 1) stop updatedCtx
  updateEntry mInfo.getFirstDiscrPos (mInfo.getFirstDiscrPos + mInfo.numDiscrs) updatedCtx

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
partial def optimizeMatchAlt
  (args : Array Expr) (mInfo : MatchInfo) (altIdx : Nat) (rhs : Expr)
  (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
  let currIdx := (altIdx - mInfo.getFirstAltPos).toUSize
  match ← reuseContext? mInfo.nameExpr currIdx with
  | some reuse =>
       setAndCommitCtx reuse.scope
       let body ← betaLambdaShared rhs reuse.fvars
       return .InitOptimizeExpr body :: .MatchAltWaitForExpr reuse.fvars (some reuse.scope) currIdx mInfo :: stack
  | none =>
       let alts ← getMatchAlts args mInfo
       let ⟨_, ⟨_, _, _, _, _, _, _, _, _,_, ⟨_, _, _, _, _, nextCtxId, _, _, _, _⟩, _, _, _⟩⟩ ← get
       let updatedMCtx ← addNotEqPatternToContext args mInfo alts 0 currIdx nextCtxId false
       forallTelescope alts[currIdx]! fun xs b => do
         let lhs := b.getAppArgs
         let body ← betaLambdaShared rhs xs
         let updatedEqCtx ← updateEqMap mInfo lhs args nextCtxId false
         let mscope ← if updatedMCtx || updatedEqCtx then some <$> newCtx else pure none
         return .InitOptimizeExpr body :: .MatchAltWaitForExpr xs mscope currIdx mInfo :: stack

  where
   onlyOnePattern (lhs : Array Expr) (idx : Nat) (onlyOne : Bool) : TranslateEnvT Bool := do
     if h : idx ≥ lhs.size then return onlyOne
     else if !isFVarPattern lhs[idx] then
          if !onlyOne then onlyOnePattern lhs (idx + 1) true
          else return false
     else onlyOnePattern lhs (idx + 1) onlyOne

   updateNotEqContext
     (updatedCtx : Bool) (nextCtxId : CtxId) (idx : USize) (start : USize) (stop : USize)
     (args : Array Expr) (lhs : Array Expr) (xs : Array Expr) : TranslateEnvT Bool := do
     if idx ≥ stop then return updatedCtx
     else
       let pattern ← removeNamedPatternExpr lhs[idx - start]!
       if !pattern.isFVar then
          -- add NotEqPattern in match context only when it's a constructor
         let patternExpr ← mkForallFVarsExpr xs pattern (usedOnly := true)
         addNotEqPatternInContext nextCtxId args[idx]! patternExpr
         updateNotEqContext true nextCtxId (idx + 1) start stop args lhs xs
       else updateNotEqContext updatedCtx nextCtxId (idx + 1) start stop args lhs xs

   addNotEqPatternToContext
     (args : Array Expr) (mInfo : MatchInfo) (alts : Array Expr) (idx : USize)
     (stopIdx : USize) (nextCtxId : CtxId) (updatedCtx : Bool) : TranslateEnvT Bool := do
     if idx ≥ stopIdx then return updatedCtx
     else
       let updatedCtx ←
         forallTelescope alts[idx]! fun xs b => do
           let lhs := b.getAppArgs
           if ← onlyOnePattern lhs 0 false then
             -- add NotEqPattern when there is only one pattern that is a constructor
             let start := mInfo.getFirstDiscrPos.toUSize
             updateNotEqContext updatedCtx nextCtxId start start mInfo.getFirstAltPos.toUSize args lhs xs
           else return updatedCtx
       addNotEqPatternToContext args mInfo alts (idx + 1) stopIdx nextCtxId updatedCtx

abbrev MatchElimResult := Sum Expr Expr

/--  Apply the following reduction rules, such that:
     Given match₁ e₁, ..., eₙ with
           | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
           ...
           | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

     - When ∀ i ∈ [1..m], ¬ tᵢ.hasLooseBVars ∧ tᵢ = t₁
         - return `some t₁`

     - When ∀ j ∈ [1..n], isPatternMatch p₍ₘ₎₍ⱼ₎ eⱼ = UnifyMatch ∧
            ∀ k ∈ [1..m-1],
              ∃ h ∈ [1..n], ( eₕ := pm ∈ matchInContext ∧ p₍ₖ₎₍ₕ₎ ∈ pm )
           - return `some tₘ`

     - Otherwise:
         - return none
-/
def elimMatch?
  (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option MatchElimResult) := do
  if let some re ← commonRhs? mInfo args then return re
  lastPatternReduction? mInfo args

where

  @[always_inline, inline]
  commonRhs? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option MatchElimResult) := do
    let firstRhs := getLambdaBody args[mInfo.getFirstAltPos]!
    -- Rhs can't be a function with loose BVars.
    if firstRhs.hasLooseBVars then return none
    for i in [mInfo.getFirstAltPos + 1 : mInfo.arity] do
      -- NOTE: No need to check for looseBVars as we are expecting equality
      if !(exprEq (getLambdaBody args[i]!) firstRhs) then return none
    -- erase context
    eraseMatchRhsRewriteCache mInfo
    return some $ Sum.inl firstRhs

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
    (alt : Expr) (h : MatchNotEqPatternMap) (active : HashSet CtxId) : TranslateEnvT Bool := do
    forallTelescope alt fun xs b => do
      let lhs := b.getAppArgs
      for j in mInfo.getDiscrRange do
        let idxLhs := j - mInfo.getFirstDiscrPos
        let pattern ← removeNamedPatternExpr lhs[idxLhs]!
        if !pattern.isFVar then
          let patternExpr ← mkForallFVarsExpr xs pattern (usedOnly := true)
          if let some pm ← ContextMap.findRaw h active args[j]! then
            if (← pm.get).contains patternExpr then return true
      return false

  @[always_inline, inline]
  lastPatternReduction? (mInfo : MatchInfo) (args : Array Expr) : TranslateEnvT (Option MatchElimResult) := do
     let ⟨_, _, _, _, _, _, _, _, matchInContext, _, ⟨_, _, _, _, _, _, active, _, _, _⟩, _, _, _⟩ := (← get).optEnv
     let h := (← get).optEnv.matchInContext
     let alts ← getMatchAlts args mInfo
     -- all last patterns are FVars
     let (mvarArgs, matchHit) ← patternMatchDiscrs alts[alts.size - 1]! args mInfo
     if isUnifyMatchResult matchHit then
       for i in [:alts.size - 1] do
         if !(← existsNotEqPattern mInfo args alts[i]! matchInContext active) then
           return none
       -- erase context
       eraseMatchRhsRewriteCache mInfo
       return some $ Sum.inr (← betaLambdaShared args[mInfo.arity - 1]! (← instantiateUnifiedMVars mvarArgs))
     else return none


@[always_inline, inline]
def getGenericMatchType (f : Expr) (args : Array Expr) (mInfo : MatchInfo) : TranslateEnvT GenericMatchResult := do
  let retTypeIdx := mInfo.getFirstDiscrPos - 1
  let genApp ← mkAppRangeExpr mInfo.instApp 0 retTypeIdx args
  match (← get).optEnv.memCache.genericMatchCache.get? genApp with
  | some g => return g
  | none =>
     let params ← getImplicitParametersRange f 0 retTypeIdx args
     let genericFVars ← retrieveGenericFVars params
     let appType ← genericMatchType genericFVars (← betaLambdaSharedRange mInfo.instApp 0 retTypeIdx args)
     let res := {appType, genericFVars}
     updateGenericMatchCache genApp res
     return res

  where
    genericMatchType (genFVars : Array Expr) (e : Expr) : TranslateEnvT Expr := do
      lambdaTelescope e fun fvars _ => do
        let inner ← mkForallFVarsExpr fvars (← mkPropType)
        mkForallFVarsExpr genFVars inner

/-- Given a `match` application expression of the form
     `f.match_n #[p₁, ..., pₙ, rt, d₁, ..., dₖ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`,
    perform the following actions:
     - params ← getImplicitParameters f #[p₁, ..., pₙ]
     - let genFVars ← retrieveGenericFVars params
     - appType ← genericMatchType (λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → mInfo.instApp p₁, ..., pₙ),
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
    let retTypeIdx := mInfo.getFirstDiscrPos - 1
    let genericType ← getGenericMatchType f args mInfo
    -- trace[Optimize.structEqMatch] "application type for {reprStr f} got {reprStr auxAppType}"
    match (← get).optEnv.matchCache.get? genericType.appType with
    | some gmatch =>
        let (f', args') := getAppFnArgsWithExtraRange (← betaLambdaShared gmatch genericType.genericFVars) retTypeIdx args.size args
        -- trace[Optimize.structEqMatch] "equivalence detected {reprStr f} ==> {reprStr f'}"
        return (f', args')
    | none =>
        -- trace[Optimize.structEqMatch] "no equivalence for {reprStr f}"
        let auxApp ← mkLambdaFVarsExpr genericType.genericFVars (← mkAppRangeExpr f 0 retTypeIdx args)
        -- trace[Optimize.structEqMatch] "generic application for {reprStr f} got {reprStr auxApp}"
        updateMatchCache genericType.appType auxApp
        return (f, args)

/-- Apply simplification and normalization rules on match expressions.
    Assumes that `f x₁ ... xₙ` is a match application
-/
@[always_inline, inline]
partial def optimizeMatch
  (f : Expr) (args : Array Expr) (mInfo : MatchInfo)
  (xs : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
 -- check for match elimination rules first
 if let some r ← elimMatch? mInfo args then
   match r with
   | Sum.inl e => return (← stackContinuity xs e)
   | Sum.inr b => return Sum.inl (.InitOptimizeExpr b :: xs)
 -- check for match equivalence afterwards
 let (f', args') ← structEqMatch f args mInfo
 let e ← mkAppNExpr f' args'
 updateCtorCacheAndFreeUnusedContext e f' args'
 return (← stackContinuity xs e)

 where
   propagateMatchReuseContext (mInfo : MatchInfo) (oldName : Expr) (newName : Expr) : TranslateEnvT Unit := do
     let rec visit (idx : USize) (stop : USize) (offset : USize) : TranslateEnvT Unit := do
       if idx ≥ stop then return ()
       else
         propagateReuseContext oldName newName (idx - offset)
         visit (idx + 1) stop offset
     let start := mInfo.getFirstAltPos.toUSize
     visit start mInfo.arity.toUSize start

   updateCtorCacheAndFreeUnusedContext (mth : Expr) (nf : Expr) (nargs : Array Expr) : TranslateEnvT Unit := do
     let some mInfo ← isMatcher? nf | throwEnvError "updateCtorCacheAndFreeUnusedContext: mInfo expected for {reprStr nf}"
     let isCtorMatchPropCache := (← get).optEnv.memCache.isCtorMatchPropCache
     let rec allRhsCtor (idx : Nat) (stop : Nat) : Bool :=
       if idx ≥ stop then true
       else
         if isCtorMatchPropCache.contains nargs[idx]! then allRhsCtor (idx + 1) stop
         else false
     let isCtor := allRhsCtor mInfo.getFirstAltPos mInfo.arity
     if isCtor then updateCtorMatchPropCache mth
     if (← isCtorArg) || ((← isAppArg) && (isCtor || isBoolType nargs[mInfo.getFirstDiscrPos - 1]!)) then
       if !exprEq f nf then propagateMatchReuseContext mInfo f nf
       return ()
     else
       -- erase context
       eraseMatchRhsRewriteCache mInfo

initialize
  registerTraceClass `Optimize.structEqMatch
  registerTraceClass `Optimize.normMatch

end Blaster.Optimize
