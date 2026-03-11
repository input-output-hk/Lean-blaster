import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Rewriting.OptimizeProjection
import Blaster.Optimize.Telescope

open Lean Meta

namespace Blaster.Optimize

structure HypsStackContext where
  newHCtx : UpdatedHypContext -- new hypothesis context
  oldHCtx : Option HypothesisContext -- old hypothesis context
  oldCache : Option RewriteCacheMap -- old local rewriting cache

structure MatchStackContext where
  oldMatchCtx : MatchContextMap -- old match context
  oldCache : RewriteCacheMap -- old local rewriting cache

structure LocalDeclStackContext where
  newCtx : LocalDeclContext -- new local decl context
  oldCtx : LocalDeclContext -- old local decl context

instance : Repr HypsStackContext where
  reprPrec _ _ := "<HypsStackContext>"

instance : Repr MatchStackContext where
  reprPrec _ _ := "<MatchStackContext>"

instance : Repr LocalDeclContext where
  reprPrec _ _ := "<LocalDeclContext>"

instance : Repr LocalContext where
  reprPrec _ _ := "<LocalContext>"

inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool)
 | InitOpaqueRecExpr (f : Expr) (args : Array Expr)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (hctx : HypsStackContext) (lctx : LocalDeclContext)
 | AppWaitForConst (args : Array Expr)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat) (pInfo : FunEnvInfo)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo) (mInfo : Option MatchInfo)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (startArgIdx : Nat) (idx : Nat) (mInfo : MatchInfo)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr) (inDite : Bool)
 | LambdaWaitForBody (x : Expr) (lctx : LocalDeclContext) (hctx : Option HypsStackContext)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr) (lctx : LocalDeclContext)
 | MatchAltWaitForExpr (params : Array Expr) (lctx : LocalDeclContext) (mctx : MatchStackContext)
 | LetWaitForValue (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 | ProjWaitForExpr (n : Name) (idx : Nat)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) Expr

@[always_inline, inline]
def mkHypStackContext (h : UpdatedHypContext) : TranslateEnvT HypsStackContext := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, hypothesisContext, _, _, _, _, _⟩⟩ ← get
  if h.1 then
    updateHypothesis h.2 Std.HashMap.emptyWithCapacity
    return {newHCtx := h, oldHCtx := some hypothesisContext, oldCache := some localRewriteCache}
  else return {newHCtx := h, oldHCtx := none, oldCache := none}

@[always_inline, inline]
def resetHypContext (h : HypsStackContext) : TranslateEnvT Unit := do
  match h.oldHCtx, h.oldCache with
  | some hyps, some cache => updateHypothesis hyps cache
  | none, none => pure ()
  | _, _ => throwEnvError "resetHypContext: invalid HypsStackContext !!!"

@[always_inline, inline]
def mkMatchStackContext (h : MatchContextMap) : TranslateEnvT MatchStackContext := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, _, matchInContext, _, _, _, _⟩⟩ ← get
  updateMatchContext h Std.HashMap.emptyWithCapacity
  return {oldMatchCtx := matchInContext, oldCache := localRewriteCache}

@[always_inline, inline]
def resetMatchContext (h : MatchStackContext) : TranslateEnvT Unit :=
  updateMatchContext h.oldMatchCtx h.oldCache

@[always_inline, inline]
def mkLocalDeclStackContext (newCtx : LocalDeclContext) : TranslateEnvT LocalDeclContext := do
  let oldCtx := (← get).optEnv.ctx
  updateLocalContext newCtx
  return oldCtx

@[always_inline, inline]
def resetLocalDeclContext (oldCtx : LocalDeclContext) : TranslateEnvT Unit :=
  updateLocalContext oldCtx

def stackContinuity (stack : List OptimizeStack) (optExpr : Expr) (skipCache := false) : TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] => return Sum.inr optExpr

  | .InitOptimizeReturn e isGlobal :: xs =>
       if !skipCache then updateOptimizeEnvCache e optExpr isGlobal
       match xs with
       | [] => return Sum.inr optExpr
       | _ => stackContinuity xs optExpr

  | .RecFunDefWaitForStorage args instApp subsInst params :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr :: xs)

  | .ForallWaitForType n bi body :: xs =>
       -- optExpr corresponds to optimized forall binder type
       -- continuity with optimizing forall body
       withLocalContext $ do
         withLocalDecl' n bi optExpr fun x => do
           let body' := instantiate1' body x
           let isNotPropBody := !(← isPropEnv body')
           let hyps ← addHypotheses optExpr x isNotPropBody
           let hctx ← mkHypStackContext hyps
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           return Sum.inl ( .InitOptimizeExpr body' :: .ForallWaitForBody x optExpr hctx lctx :: xs)

  | .ForallWaitForBody x t hctx lctx :: xs =>
       -- optExpr corresponds to optimized forall body
       -- continiuity with applying forall normalization rules
       resetHypContext hctx
       let e ← withLocalContext $ do
                 optimizeForall x t hctx.newHCtx.2.1 optExpr
       resetLocalDeclContext lctx
       if ← isRestart then
         resetRestart
         return Sum.inl (.InitOptimizeExpr e :: xs)
       else -- continuity with optimizing next expression
         stackContinuity xs (← mkExpr e)

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- reset inFunApp flag
       setInFunApp false
       -- check if optExpr is a lambda
       if optExpr.isLambda then
         -- perform beta reduction and apply optimization
         return Sum.inl (.InitOptimizeExpr (betaLambda optExpr args) :: xs)
       else
         let (rf, extraArgs) := getAppFnWithArgs optExpr
         let args := extraArgs ++ args
         let pInfo ← withLocalContext $ do getFunEnvInfo rf
         -- apply optimization on match generic instance (if necessary)
         match (← hasUnOptMatchInfo? rf) with
         | none =>
            -- continuity with optimization on implicit arguments
            return Sum.inl (.AppOptimizeImplicitArgs rf args extraArgs.size extraArgs.size args.size pInfo :: xs)
         | some (mInfo, instApp) =>
            -- continuity with optimizing match generic instance
            -- NOTE: instApp is expected to be a lambda term
            -- NOTE: we here only want to optimize the lambda params type, which mainly
            -- correspond to the match lhs.
            match instApp with
            | Expr.lam n t b bi =>
                let mWait := .OptimizeMatchInfoWaitForInst rf args extraArgs.size pInfo mInfo :: xs
                return Sum.inl (.InitOptimizeExpr t :: .MatchRhsLambdaWaitForType n bi b :: mWait)
            | _ => throwEnvError "stackContinuity: lambda expected for match instance but got {reprStr instApp}"


  | .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo :: xs =>
       -- optExpr corresponds to optimized match generic instance
       -- update cache isMatcherCache
       if let Expr.const n _ := f then
         let argInfo := ({ name := n, nameExpr := f, instApp := optExpr, recInfo := mInfo } : MatchInfo)
         modify (fun env => { env with optEnv.memCache.isMatcherCache :=
                                       env.optEnv.memCache.isMatcherCache.insert n argInfo })
         -- apply optimization only on implicit parameters to remove mdata annotation
         -- we don't consider explicit parameters at this stage to avoid performing
         -- optimization on unreachable arguments
         return Sum.inl (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo :: xs)
       else throwEnvError "stackContinuity: name expression for match application but got {reprStr f} !!!"


  | .AppOptimizeImplicitArgs f args idx startArgIdx stopIdx pInfo :: xs =>
       -- optExpr corresponds to the optimized implicit argument referenced by idx.
       -- continuity with optimizing the next implicit argument.
       return Sum.inl (.AppOptimizeImplicitArgs f (args.set! idx optExpr) (idx + 1) startArgIdx stopIdx pInfo :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo :: xs =>
       -- optExpr corresponds to the optimized explicit argument referenced by idx.
       -- continuity with optimizing the next explicit argument.
       return Sum.inl (.AppOptimizeExplicitArgs f (args.set! idx optExpr) (idx + 1) stopIdx pInfo mInfo :: xs)

  | .DiteChoiceWaitForCond f args pInfo startArgIdx :: xs =>
       -- optExpr corresponds to the optimized Blaster.dite' conditional, i.e., referenced by index 1.
       -- When some r ← optimizeDiteChoice f (args.set! 1 optExpr)
       --  - continuity with optimizing `r`
       -- Otherwise
       --  - continuity with optimizing remaining explicit parameters before reduction
       -- NOTE: keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
       if let some r ← optimizeDITEChoice f (args.set! 1 optExpr) then
           return Sum.inl (.InitOptimizeExpr r :: xs)
       else
          -- NOTE: keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
          return Sum.inl (.AppOptimizeExplicitArgs f (args.set! 1 optExpr) startArgIdx args.size pInfo none :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       return Sum.inl (.MatchChoiceOptimizeDiscrs f (args.set! idx optExpr) pInfo startArgIdx (idx + 1) mInfo :: xs)

  | .LambdaWaitForType n bi body inDite :: xs =>
       -- optExpr corresponds to optimized lambda type
       withLocalContext $ do
         withLocalDecl' n bi optExpr fun x => do
           let bodyOpt := .InitOptimizeExpr (instantiate1' body x)
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           if inDite then
             let hyps ← addHypotheses optExpr x
             let hypsCtx ← mkHypStackContext hyps
             return Sum.inl (bodyOpt :: .LambdaWaitForBody x lctx (some hypsCtx) :: xs)
           else return Sum.inl (bodyOpt :: .LambdaWaitForBody x lctx none :: xs)

  | .LambdaWaitForBody x lctx hctx :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       if let some h := hctx then resetHypContext h
       let e ← withLocalContext $ do mkLambdaExpr x optExpr
       resetLocalDeclContext lctx
       stackContinuity xs e

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalContext $ do
          withLocalDecl' n bi optExpr fun x => do
            let bodyOpt := .MatchRhsLambdaNext (instantiate1' body x)
            let lctx ← mkLocalDeclStackContext (← mkLocalContext)
            return Sum.inl (bodyOpt :: .MatchRhsLambdaWaitForBody x lctx :: xs)

  | .MatchRhsLambdaWaitForBody x lctx :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        -- NOTE: We can't catch optimize result here as match
        -- rhs has not been optimized yet.
        let e ← withLocalContext $ do mkLambdaFVar x optExpr
        resetLocalDeclContext lctx
        stackContinuity xs e

  | .MatchAltWaitForExpr params lctx mctx :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       let e ← withLocalContext $ do mkExpr (← mkLambdaFVars' params optExpr)
       resetMatchContext mctx
       resetLocalDeclContext lctx
       stackContinuity xs e

  | .LetWaitForValue body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       return Sum.inl (.InitOptimizeExpr (body.instantiate1 optExpr) :: xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       stackContinuity xs (← mkExpr (Expr.mdata d optExpr))

  | .ProjWaitForExpr n idx :: xs =>
      -- optExpr corresponds to optimized projection structure
      if let some re ← optimizeProjection? n idx optExpr then
         return Sum.inl (.InitOptimizeExpr re :: xs)
      else
        -- continuity with optimizing next expression
        stackContinuity xs (← mkExpr $ mkProj n idx optExpr)

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
          let matchFun ← instantiateValueLevelParams cInfo l
          return some (mInfo, matchFun)
        else return none
      else return none

@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else stackContinuity stack (← mkExpr e)

/-- Apply simplification/normalization rules on Blaster.dite' expressions.
    Assume that f = Expr.const ``Blaster.dite'.
-/
@[always_inline, inline]
def optimizeIfThenElse? (f : Expr) (args : Array Expr) (stack : List OptimizeStack) :
  TranslateEnvT OptimizeContinuity := withLocalContext $ do
   mkOptimizeContinuity (← optimizeDITE f args) stack

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  -- NOTE: Always consider global context when `a` does not contain any FVar.
  let isGlobal := !a.hasFVar || (← isGlobalContext)
  match (← isInOptimizeCache? a isGlobal) with
  | some b => Sum.inr <$> stackContinuity stack b
  | none => return Sum.inl (.InitOptimizeReturn a isGlobal :: stack)


end Blaster.Optimize
