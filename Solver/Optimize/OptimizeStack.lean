import Lean
import Solver.Optimize.Env
import Solver.Optimize.Rewriting.OptimizeForAll
import Solver.Optimize.Telescope

open Lean Meta

namespace Solver.Optimize

structure HypsStackContext where
  newHCtx : Bool × HypothesisContext -- new hypothesis context
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

instance : Repr NameGenerator where
  reprPrec _ _ := "<NameGenerator>"

inductive OptimizeStack where
 | InitOptimizeExpr (e : Expr)
 | InitOptimizeReturn (e : Expr) (isGlobal : Bool)
 | InitNextOptimize (e : Expr)
 | InitOpaqueRecExpr (f : Expr) (args : Array Expr)
 | RecFunDefWaitForStorage (args : Array Expr) (instApp : Expr)
                           (subsInts : Expr) (params : ImplicitParameters)
 | RecFunDefStorage (args : Array Expr) (instApp : Expr)
                    (subsInts : Expr) (params : ImplicitParameters) (optBody : Expr)
 | LocalDeclWaitForExpr (h : LocalDeclContext)
 | ForallWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | ForallWaitForBody (x : Expr) (t : Expr) (h : HypsStackContext)
 | ForallOptimize (x : Expr) (t : Expr) (body : Expr) (h : HypothesisMap)
 | AppWaitForConst (args : Array Expr)
 | InitOptimizeMatchInfo (f : Expr) (args : Array Expr) (startArgIdx : Nat)  (pInfo : FunEnvInfo)
 | OptimizeMatchInfoWaitForInst (f : Expr) (args : Array Expr)
                                (startArgIdx : Nat) (pInfo : FunEnvInfo) (mInfo : MatcherRecInfo)
 | AppOptimizeImplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (startArgIdx : Nat) (stopIdx : Nat) (pInfo : FunEnvInfo)
 | AppOptimizeExplicitArgs (f : Expr) (args : Array Expr) (idx : Nat)
                           (stopIdx : Nat) (pInfo : FunEnvInfo) (mInfo : Option MatchInfo)
 | InitIteChoiceExpr (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | IteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | IteChoiceReturn (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | DiteChoiceWaitForCond (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | DiteChoiceReturn (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | InitMatchChoiceExpr (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo) (startArgIdx : Nat)
 | MatchChoiceOptimizeDiscrs (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                             (startArgIdx : Nat) (idx : Nat) (mInfo : MatchInfo)
 | MatchChoiceReduce (f : Expr) (args : Array Expr) (pInfo : FunEnvInfo)
                     (startArgIdx : Nat) (mInfo : MatchInfo)
 | HypothesisWaitForExpr (h : HypsStackContext)
 | LambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr) (inDite : Bool)
 | LambdaWaitForBody (x : Expr)
 | InitOptimizeMatchAlt (args : Array Expr) (mInfo : MatchInfo) (altIdx : Nat) (rhs : Expr)
 | MatchRhsLambdaWaitForType (n : Name) (bi : BinderInfo) (body : Expr)
 | MatchRhsLambdaNext (e : Expr)
 | MatchRhsLambdaWaitForBody (x : Expr)
 | MatchAltWaitForParamsRhs (args : Array Expr) (mInfo : MatchInfo) (altIdx : Nat)
 | MatchAltOptimize (args : Array Expr) (mInfo : MatchInfo) (altIdx : Nat) (rhs : Expr)
 | MatchContextWaitForExpr (h : MatchStackContext)
 | MatchAltWaitForExpr (params : Array Expr)
 | LetWaitForValue (body : Expr)
 | MDataRecCallWaitForExpr (data : MData)
 deriving Repr

abbrev OptimizeContinuity := Sum (List OptimizeStack) Expr

@[always_inline, inline]
def mkHypStackContext (h : Bool × HypothesisContext) : TranslateEnvT HypsStackContext := do
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

def stackContinuity (stack : List OptimizeStack) (optExpr : Expr) : TranslateEnvT OptimizeContinuity := do
  match stack with
  | [] => return Sum.inr optExpr

  | .InitOptimizeReturn e isGlobal :: xs =>
       updateOptimizeEnvCache e optExpr isGlobal
       match xs with
       | [] => return Sum.inr optExpr
       | _ => return Sum.inl (.InitNextOptimize optExpr :: xs)

  | .RecFunDefWaitForStorage args instApp subsInst params :: xs =>
       -- optExpr corresponds to optimized rec fun body
       -- continuity with normOpaqueAndRecFun
       return Sum.inl (.RecFunDefStorage args instApp subsInst params optExpr :: xs)

  | .LocalDeclWaitForExpr h :: xs =>
       -- optExpr corresponds to the optimized expression under h.
       -- continuity with optimizing next expression
       resetLocalDeclContext h
       return Sum.inl (.InitNextOptimize optExpr :: xs)

  | .ForallWaitForType n bi body :: xs =>
       withLocalContext $ do
         withLocalDecl n bi optExpr fun x => do
           let body' := body.instantiate1 x
           let isNotPropBody := !(← isPropEnv body')
           let hyps ← addHypotheses optExpr (some x) isNotPropBody
           let hypsCtx ← mkHypStackContext hyps
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           let bOpt := .InitOptimizeExpr body'
           let allWait := .ForallWaitForBody x optExpr hypsCtx
           return Sum.inl ( bOpt :: allWait :: .LocalDeclWaitForExpr lctx :: xs)

  | .ForallWaitForBody x t h :: xs =>
       -- optExpr corresponds to optimized forall body
       -- optimizing forall
       resetHypContext h
       return Sum.inl (.ForallOptimize x t optExpr h.newHCtx.2.1 :: xs)

  | .AppWaitForConst args :: xs =>
       -- optExpr corresponds to optimized fun app
       -- continuity with optimizing match generic instance
       let (rf, extraArgs) := getAppFnWithArgs optExpr
       let args := extraArgs ++ args
       let pInfo ← withLocalContext $ do getFunEnvInfo rf
       -- apply optimization on match generic instance (if necessary)
       return Sum.inl (.InitOptimizeMatchInfo rf args extraArgs.size pInfo :: xs)

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

  | .IteChoiceWaitForCond f args pInfo startArgIdx :: xs =>
       -- optExpr corresponds to the optimized ite conditional, i.e., referenced by index 1.
       -- continuity with optimizing ite if constant
       return Sum.inl (.IteChoiceReturn f (args.set! 1 optExpr) pInfo startArgIdx :: xs)

  | .DiteChoiceWaitForCond f args pInfo startArgIdx :: xs =>
       -- optExpr corresponds to the optimized dite conditional, i.e., referenced by index 1.
       -- continuity with optimizing dite if constant
       return Sum.inl (.DiteChoiceReturn f (args.set! 1 optExpr) pInfo startArgIdx :: xs)

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo :: xs =>
       -- optExpr corresponds to the optimized match discriminator referenced by idx.
       -- continuity with optimizing the next discriminator
       return Sum.inl (.MatchChoiceOptimizeDiscrs f (args.set! idx optExpr) pInfo startArgIdx (idx + 1) mInfo :: xs)

  | .HypothesisWaitForExpr h :: xs =>
       -- optExpr corresponds to the optimized expression under h.
       -- continuity with optimizing next expression
       resetHypContext h
       return Sum.inl (.InitNextOptimize optExpr :: xs)

  | .LambdaWaitForType n bi body inDite :: xs =>
       -- optExpr corresponds to optimized lambda type
       withLocalContext $ do
         withLocalDecl n bi optExpr fun x => do
           let bodyOpt := .InitOptimizeExpr (body.instantiate1 x)
           let lctx ← mkLocalDeclStackContext (← mkLocalContext)
           let lamWait := .LambdaWaitForBody x :: .LocalDeclWaitForExpr lctx :: xs
           if inDite then
             let hyps ← addHypotheses optExpr (some x)
             let hypsCtx ← mkHypStackContext hyps
             return Sum.inl (bodyOpt :: .HypothesisWaitForExpr hypsCtx :: lamWait)
           else return Sum.inl (bodyOpt :: lamWait)

  | .LambdaWaitForBody x :: xs =>
       -- optExpr corresponds to optimized lambda body
       -- continuity with optimizing next expression
       let e ← withLocalContext $ do mkLambdaExpr x optExpr
       return Sum.inl (.InitNextOptimize e :: xs)

  | .MatchRhsLambdaWaitForType n bi body :: xs =>
        -- optExpr corresponds to optimized lambda type
        -- continuity with optimizing body
        withLocalContext $ do
          withLocalDecl n bi optExpr fun x => do
            let bodyOpt := .MatchRhsLambdaNext (body.instantiate1 x)
            let lctx ← mkLocalDeclStackContext (← mkLocalContext)
            let lamWait := .MatchRhsLambdaWaitForBody x
            return Sum.inl (bodyOpt :: lamWait :: .LocalDeclWaitForExpr lctx :: xs)

  | .MatchRhsLambdaWaitForBody x :: xs =>
        -- optExpr corresponds to optimized lambda body
        -- continuity with optimizing next expression
        let e ← withLocalContext $ do mkLambdaFVars #[x] optExpr
        return Sum.inl (.InitNextOptimize e :: xs)

  | .MatchAltWaitForParamsRhs args minfo altIdx :: xs =>
        -- optExpr corresponds to match rhs for which all lambda parameters have been optimized
        -- continuity with optimizing rhs body with match context
        return Sum.inl (.MatchAltOptimize args minfo altIdx optExpr :: xs)

  | .MatchContextWaitForExpr h :: xs =>
       -- optExpr corresponds to the optimized expression under h
       -- continuity with optimizing next expression
       resetMatchContext h
       return Sum.inl (.InitNextOptimize optExpr :: xs)

  | .MatchAltWaitForExpr params :: xs =>
       -- optExpr corresponds to the optimized match rhs
       -- continuity with optimizing next expression
       let e ← withLocalContext $ do mkExpr (← mkLambdaFVars params optExpr)
       return Sum.inl (.InitNextOptimize e :: xs)

  | .LetWaitForValue body :: xs =>
       -- optExpr corresponds to the optimized let value
       -- continuity with optimizing body
       return Sum.inl (.InitOptimizeExpr (body.instantiate1 optExpr) :: xs)

  | .MDataRecCallWaitForExpr d :: xs =>
       -- optExpr corresponds to the annotated rec call that is optimized when `normalizeFunCall` is set to false
       -- continuity with optimizing next expression
       setNormalizeFunCall true
       return Sum.inl (.InitNextOptimize (← mkExpr (Expr.mdata d optExpr)) :: xs)

  | _ => throwEnvError "stackContinuity: unexpected optimize stack continuity {reprStr stack} !!!"

@[always_inline, inline]
def mkOptimizeContinuity (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
  if ← isRestart then
    resetRestart
    return Sum.inl (.InitOptimizeExpr e :: stack)
  else stackContinuity stack e

@[always_inline, inline]
def isInOptimizeEnvCache (a : Expr) (stack : List OptimizeStack) : TranslateEnvT (Sum (List OptimizeStack) OptimizeContinuity) := do
  -- TODO: Always consider global context when `a` does not contain any FVar.
  -- let isGlobal := !a.hasFVar || (← isGlobalContext)
  let isGlobal ← isGlobalContext
  match (← isInOptimizeCache? a isGlobal) with
  | some b => Sum.inr <$> stackContinuity stack b
  | none => return Sum.inl (.InitOptimizeReturn a isGlobal :: stack)

/-- Apply simplification rules on `forallE` and check for continuity. -/
@[always_inline, inline]
def forallContinuity
  (n : Expr) (t : Expr) (h : HypothesisMap) (b : Expr)
  (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := withLocalContext $ do
    mkOptimizeContinuity (← optimizeForall n t h b) stack


end Solver.Optimize
