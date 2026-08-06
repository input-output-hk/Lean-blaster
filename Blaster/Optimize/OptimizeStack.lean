import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeProjection
import Blaster.Optimize.Telescope
import Blaster.Optimize.RetentionProfile

open Lean Meta Elab Blaster.Data.HashMap

namespace Blaster.Optimize

abbrev HypsStackContext := Option CtxScope -- context scope to close on exit

instance : Repr (Option MVarIdDecls) where
  reprPrec _ _ := "<MVarIdDecls>"

inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr) (mvarDecls : Option MVarIdDecls := none)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool) (mvarDecls : Option MVarIdDecls)
 | InitOpaqueRecExpr (f : Expr) (args : Array Expr)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters) (startCtxId : CtxId)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr)
                    (startCtxId : CtxId)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (hctx : HypsStackContext) (isProp : Bool)
 | AppWaitForConst (args : Array Expr)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat)
                           (pInfo : FunEnvInfo) (prevInApp : Bool)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo)
                           (mInfo : Option MatchInfo) (prevInApp : Bool)
 | InitNonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
 | NonFunOptimizeArgs (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat) (prevInCtor : Bool)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (prevInApp : Bool)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (idx : Nat) (mInfo : MatchInfo) (prevInApp : Bool)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | LambdaWaitForBody (x : Expr) (hctx : HypsStackContext) (inDite : Bool) (startCtxId : CtxId)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr)
 | MatchLhsSkipForallType (e : Expr)
 | MatchLhsForallWaitForBody (e : Expr)
 | MatchAltWaitForExpr (params : Array Expr) (hctx : HypsStackContext) (idx : USize) (mInfo : MatchInfo)
 | LetWaitForValue (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 | ProjWaitForExpr (n : Name) (idx : Nat)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) Expr


@[always_inline, inline]
def resetContext (h : HypsStackContext) : TranslateEnvT Unit := do
  match h with
  | some scope => endCtx scope
  | none => return ()


@[always_inline, inline]
def resetChoiceContext (h : HypsStackContext) (fvars : Array Expr) (lam : Expr) (idx : USize) : TranslateEnvT Unit := do
  match h with
  | some scope =>
       updateContextReuseCache lam idx ⟨scope, fvars⟩
       modifyOptEnv
         fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, _, s6, active, s7, s8⟩, o12, o13, o14⟩ =>
             ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, scope.parent, s6, active.erase scope.current, s7, s8⟩, o12, o13, o14⟩
  | none => return ()

def restoreMVarDecls (optDecls : Option MVarIdDecls) : TranslateEnvT Unit :=
  match optDecls with
  | none => pure ()
  | some mdecls =>
      let rec updateAssignments
        (idx : Nat) (stop : Nat) (mdecls : MVarIdDecls)
        (mAssignments : MVarAssignments) : MVarAssignments :=
        if idx ≥ stop then mAssignments
        else
          let d := mdecls[idx]!
          let mAssignments := mAssignments.insert d.mvar d.value
          updateAssignments (idx + 1) stop mdecls mAssignments
      modifyOptEnv
        fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩ =>
          let mAssignments := updateAssignments 0 mdecls.size mdecls mAssignments
          ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, mAssignments⟩

def isInEqualityMap (e : Expr) (isGlobal : Bool) : TranslateEnvT Expr := do
  if isGlobal then return e
  else
    match (← eqMapFind? e) with
    | none => return e
    | some b => return b

def stackContinuity (stack : List OptimizeStack) (optExpr : Expr) (skipCache := false) : TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] => return Sum.inr optExpr

  | .InitOptimizeReturn e isGlobal mvarDecls :: xs =>
       let optExpr ← isInEqualityMap optExpr isGlobal
       if !skipCache then
         updateOptimizeEnvCache optExpr optExpr isGlobal
         if !e.hasMVar && !exprEq e optExpr then updateOptimizeEnvCache e optExpr isGlobal
       restoreMVarDecls mvarDecls
       match xs with
       | [] => return Sum.inr optExpr
       | _ => stackContinuity xs optExpr

  | .RecFunDefWaitForStorage args instApp subsInst params startCtxId :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr startCtxId :: xs)

  | .ForallWaitForType n bi body :: xs =>
       -- optExpr corresponds to optimized forall binder type
       -- check forall reduction to avoid optimizing body
       let isProp ← isPropEnv (← mkForallExpr n bi optExpr body)
       if let some r ← forallReduction? optExpr body isProp then
         match r with
         | Expr.const ``True _ => stackContinuity xs r
         | _ => return Sum.inl ( .InitOptimizeExpr r :: xs)
       else
         -- continuity with optimizing forall body
          withLocalDecl' n bi optExpr fun x => do
            let body' ← instantiateShared1 body x
            let mscope ← addHypotheses optExpr x (isPropBody := isProp)
            return Sum.inl ( .InitOptimizeExpr body' :: .ForallWaitForBody x optExpr mscope isProp :: xs)

  | .ForallWaitForBody x t hctx isProp :: xs =>
       -- optExpr corresponds to optimized forall body
       -- continuity with applying forall normalization rules.
       let e ← optimizeForall x t optExpr hctx isProp
       resetContext hctx
       if ← isRestart then
         resetRestart
         return Sum.inl (.InitOptimizeExpr e :: xs)
       else -- continuity with optimizing next expression
         stackContinuity xs e

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- reset inFunApp flag
       setInFunApp false
       -- check if optExpr is a lambda
       if optExpr.isLambda then
         -- perform beta reduction and apply optimization
         let betaRes ← betaLambdaEnv optExpr (← resolveMVarsArgs #[] args)
         return Sum.inl (.InitOptimizeExpr betaRes.betaReduced betaRes.prevMVarIdDecls :: xs)
       else
         let (rf, extraArgs) := getAppFnWithArgs optExpr
         let args ← resolveMVarsArgs extraArgs args
         let is_match ← isMatchExpr rf
         if (← isNotFun rf <&&> pure !is_match) then
            return Sum.inl (.InitNonFunOptimizeArgs rf args extraArgs.size args.size :: xs)
         else
           let pInfo ← getFunEnvInfo rf
           -- apply optimization on match generic instance (if necessary)
           match (← hasUnOptMatchInfo? rf) with
           | none =>
              -- continuity with optimization on implicit arguments
              let prevInApp ← isAppArg
              if !(isBlasterDiteConst rf) then setIsAppArg true
              return Sum.inl (.AppOptimizeImplicitArgs rf args extraArgs.size extraArgs.size args.size pInfo prevInApp :: xs)
           | some (mInfo, instApp) =>
              -- continuity with optimizing match generic instance
              -- NOTE: instApp is expected to be a lambda term
              -- NOTE: we here only want to optimize the lambda params type, which mainly
              -- correspond to the match lhs.
              match instApp with
              | Expr.lam n t b bi =>
                    let mWait := .OptimizeMatchInfoWaitForInst rf args extraArgs.size pInfo mInfo :: xs
                    -- NOTE: we only optimize the lhs forall body and not the types.
                    return Sum.inl (.MatchLhsSkipForallType t :: .MatchRhsLambdaWaitForType n bi b :: mWait)
              | _ => throwEnvError "stackContinuity: lambda expected for match instance but got {reprStr instApp}"


  | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo :: xs =>
       -- optExpr corresponds to optimized match generic instance
       -- update cache isMatcherCache
       if let Expr.const n _ := f then
         let argInfo := ({ name := n, nameExpr := f, instApp := optExpr, recInfo := mInfo } : MatchInfo)
         updateIsMatcherCache n argInfo
         -- apply optimization only on implicit parameters to remove mdata annotation
         -- we don't consider explicit parameters at this stage to avoid performing
         -- optimization on unreachable arguments
         let prevInApp ← isAppArg
         return Sum.inl (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo prevInApp :: xs)
       else throwEnvError "stackContinuity: name expression for match application but got {reprStr f} !!!"

  | .NonFunOptimizeArgs f args idx stopIdx prevInCtor :: xs =>
       -- optExpr corresponds to the optimized non-fun argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       return Sum.inl (.NonFunOptimizeArgs f (args.set! idx optExpr) (idx + 1) stopIdx prevInCtor :: xs)

  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized implicit argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       return Sum.inl (.AppOptimizeImplicitArgs f (args.set! idx optExpr) (idx + 1) startArgIdx stopIdx pInfo prevInApp :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized explicit argument referenced by idx.
       -- continuity with optimizing the next explicit argument.
       return Sum.inl (.AppOptimizeExplicitArgs f (args.set! idx optExpr) (idx + 1) stopIdx pInfo mInfo prevInApp :: xs)

  | .DiteChoiceWaitForCond f args pInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized Blaster.dite' conditional, i.e., referenced by index 1.
       -- When some r ← optimizeDiteChoice f (args.set! 1 optExpr)
       --  - continuity with optimizing `r`
       -- Otherwise
       --  - continuity with optimizing remaining explicit parameters before reduction
       -- set isAppArg to keep context for eventual constant match.
       setIsAppArg true
       if let some r ← optimizeDITEChoice f (args.set! 1 optExpr) then
           return Sum.inl (.InitOptimizeExpr r :: xs)
       else
          return Sum.inl (.AppOptimizeExplicitArgs f (args.set! 1 optExpr) 2 args.size pInfo none prevInApp :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       return Sum.inl (.MatchChoiceOptimizeDiscrs f (args.set! idx optExpr) pInfo (idx + 1) mInfo prevInApp :: xs)

  | .LambdaWaitForType n bi body :: xs =>
       -- optExpr corresponds to optimized lambda type
       withLocalDecl' n bi optExpr fun x => do
         let bodyOpt := .InitOptimizeExpr (← instantiateShared1 body x)
         -- NOTE: keeping track of next ctxId to clean-up rewrite cache
         let nextCtxId := (← get).optEnv.options.nextCtxId
         return Sum.inl (bodyOpt :: .LambdaWaitForBody x none false nextCtxId :: xs)

  | .LambdaWaitForBody x hctx inDite startCtxId :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       let e ← mkLambdaFVarExpr x optExpr
       if inDite then
         if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
         resetChoiceContext hctx #[x] e 0
         stackContinuity xs e
       else
         -- clean-up rewrite cache
         freeRewriteCacheRange startCtxId (← get).optEnv.options.nextCtxId
         stackContinuity xs e

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalDecl' n bi optExpr fun x => do
          let bodyOpt := .MatchRhsLambdaNext (← instantiateShared1 body x)
          return Sum.inl (bodyOpt :: .MatchRhsLambdaWaitForBody x :: xs)

  | .MatchRhsLambdaWaitForBody x :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        let e ← mkLambdaFVarExpr x optExpr
        stackContinuity xs e

  | .MatchAltWaitForExpr params hctx idx mInfo :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       let e ← mkLambdaFVarsExpr params optExpr
       if ← isCstIteMatch optExpr then updateCtorMatchPropCache e
       resetChoiceContext hctx params mInfo.nameExpr idx
       stackContinuity xs e

  | .MatchLhsForallWaitForBody x :: xs =>
       -- optExpr corresponds to the optimized lhs forall body
       -- continuity with optimizing next expression
       let e ← mkForallFVarExpr x optExpr
       stackContinuity xs e

  | .LetWaitForValue body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       return Sum.inl (.InitOptimizeExpr (← instantiateShared1 body optExpr) :: xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       stackContinuity xs (← mkMDataExpr d optExpr)

  | .ProjWaitForExpr n idx :: xs =>
      -- optExpr corresponds to optimized projection structure
      if let some re ← optimizeProjection? n idx optExpr then
         return Sum.inl (.InitOptimizeExpr re :: xs)
      else
        -- continuity with optimizing next expression
        stackContinuity xs (← mkProjExpr n idx optExpr)

  | _ => throwEnvError "stackContinuity: unexpected optimize stack continuity {reprStr stack} !!!"

  where
    /-- Given a function `f := Expr const n l` perform the following:
         - When `n := mInfo ∈ isMatcherCache` (i.e., match info already optimized)
             - return `none`
         - When let some mInfo ← getMatcherRecInfo? n l (i.e., f's generic instance not optimized)
             - return `some $ Sum.inr (mInfo, matchFun)`
         - Otherwise `none`
    -/
    @[always_inline, inline]
    hasUnOptMatchInfo? (f : Expr) : TranslateEnvT (Option (MatcherRecInfo × Expr)) := do
      if (← isMatcher? f).isSome then return none -- already optimized
      else if let Expr.const n l := f then
        if let some mInfo ← getMatcherRecInfo? n l then
          let cInfo ← getConstEnvInfo n
          let matchFun ← hashcons (← instantiateValueLevelParams cInfo l)
          return some (mInfo, matchFun)
        else return none
      else return none

    @[always_inline, inline]
    resolveMVarsArgs (extra_args : Array Expr) (args : Array Expr) : TranslateEnvT (Array Expr) := do
      let mAssignments := (← get).optEnv.mAssignments
      let rec visit (idx : Nat) (stop : Nat) (args : Array Expr) : Array Expr :=
         if idx ≥ stop then args
         else
           let e := args[idx]!
           match e with
           | Expr.mvar _ => visit (idx + 1) stop (args.set! idx (getEnvMVarValue' e mAssignments))
           | _ => visit (idx + 1) stop args
      let rec visit'
          (idx : Nat) (offset : Nat) (stop : Nat)
          (extra_args : Array Expr) (args : Array Expr) (pargs : Array Expr) : Array Expr :=
         if idx ≥ stop then pargs
         else
           let p := if idx < offset then extra_args[idx]! else args[idx - offset]!
           match p with
           | Expr.mvar _ => visit' (idx + 1) offset stop extra_args args (pargs.push (getEnvMVarValue' p mAssignments))
           | _ => visit' (idx + 1) offset stop extra_args args (pargs.push p)
      let extra_size := extra_args.size
      if mAssignments.size == 0 then
        -- no mvar assignments: resolution is the identity, only concatenation remains
        if extra_size == 0 then return args
        else return extra_args ++ args
      else if extra_size == 0 then
        return visit 0 args.size args
      else
        let stop := extra_size + args.size
        return visit' 0 extra_size stop extra_args args (Array.emptyWithCapacity stop)


@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else stackContinuity stack e

/-- Apply simplification/normalization rules on Blaster.dite' expressions.
    Assume that f = Expr.const ``Blaster.dite'.
-/
@[always_inline, inline]
def optimizeIfThenElse? (f : Expr) (args : Array Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
   mkOptimizeContinuity (← optimizeDITE f args) stack

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) (mvarDecls : Option MVarIdDecls) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  -- retention profiling: one driver iteration (no-op unless BLASTER_RETENTION_PROFILE is set)
  if ← Retention.due then Retention.sample "tick" stack.length
  -- hash-cons GC v1 (no-op unless BLASTER_HASHCONS_GC is set)
  maybeGCHashCons
  let env ← get
  -- NOTE: Always consider global context when `a` does not contain any FVar/MVar
  let isGlobal := !(hasVar a) || isGlobalContext env
  let useCache := !a.hasMVar
  if useCache then
    let cached := ← isInOptimizeCache? a isGlobal env
    if !exprEq cached instCacheMiss then Sum.inr <$> stackContinuity stack cached
    else
      -- retention diagnostics (p0a): would this local miss have hit
      -- another context's cache? No-op unless profiling is enabled.
      if !isGlobal then Retention.probeWouldHit a env
      return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)
  else return Sum.inl (.InitOptimizeReturn a isGlobal mvarDecls :: stack)

  where
    hasVar (e : Expr) : Bool := e.hasFVar || e.hasMVar

end Blaster.Optimize
