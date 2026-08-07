import Lean
import Lean.Util.MonadCache
import Blaster.Command.Options
import Blaster.Logging
import Blaster.Optimize.Rewriting.FunPropagation
import Blaster.Optimize.Rewriting.OptimizeApp
import Blaster.Optimize.Rewriting.OptimizeConst
import Blaster.Optimize.Rewriting.OptimizeForAll

open Lean Elab Command Term Meta Blaster.Options

namespace Blaster.Optimize

-- TODO: update formalization with inference rule style notation.
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT Expr := do
  match stack with
  | .InitOptimizeExpr e mvarDecls :: xs =>
      match (← isInOptimizeEnvCache e xs mvarDecls) with
      | Sum.inl i_stack =>
          -- trace[Optimize.expr] "optimizing {← ppExpr e}"
          match e with
          | Expr.fvar _ =>
              match (← normFVar e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.mvar _ =>
              optimizeExprAux (.InitOptimizeExpr (← getMVarValue e) :: i_stack)

          | Expr.sort l =>
              -- sort is used for Type u, Prop, etc
              let s' ← mkExpr (Expr.sort (← normLevel l))
              match (← stackContinuity i_stack s') with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.lit .. => -- number or string literal
              match (← stackContinuity i_stack e) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.const .. =>
              match (← normConst e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.forallE n t b bi =>
              match ← reuseContext? e 0 with
              | some reuse =>
                   let x := reuse.fvars[0]!
                   setAndCommitCtx reuse.scope
                   let body ← instantiateShared1 b x
                   optimizeExprAux (.InitOptimizeExpr body :: .ForallWaitForBody x t (some reuse.scope) true :: i_stack)

              | none => optimizeExprAux (.InitOptimizeExpr t :: .ForallWaitForType n bi b :: i_stack)

          | Expr.app .. =>
             let (f, ras) := getAppFnWithArgs e
             -- check if f is a lambda term
             if f.isLambda then
               -- perform beta reduction and apply optimization
               let betaRes ← betaLambdaEnv f ras
               optimizeExprAux (.InitOptimizeExpr betaRes.betaReduced betaRes.prevMVarIdDecls :: i_stack)
             else
               -- set inFunApp flag before optimizing `f`
               setInFunApp true
               let i_stack' := .AppWaitForConst ras :: i_stack
               optimizeExprAux (.InitOptimizeExpr f :: i_stack')

          | Expr.lam n t b bi => optimizeExprAux (.InitOptimizeExpr t :: .LambdaWaitForType n bi b :: i_stack)

          | Expr.letE _n _t v b _ => optimizeExprAux (inlineLet v b i_stack) -- inline let expression

          | Expr.mdata d me =>
              if (isTaggedRecursiveCall e) then
                setNormalizeFunCall false
                optimizeExprAux (.InitOptimizeExpr me :: .MDataRecCallWaitForExpr d :: i_stack)
              else optimizeExprAux (.InitOptimizeExpr me :: i_stack)

          | Expr.proj n idx s =>
              let i_stack' := .ProjWaitForExpr n idx :: i_stack
              optimizeExprAux (.InitOptimizeExpr s :: i_stack')

          | Expr.bvar .. => throwEnvError "optimizeExpr: unexpected bound variable {e}"

      | Sum.inr (Sum.inr e') => return e'
      | Sum.inr (Sum.inl stack') => optimizeExprAux stack'

  | s@(.InitOpaqueRecExpr ..) :: xs
  | s@(.RecFunDefStorage ..) :: xs =>
        match (← normOpaqueAndRecFun s xs) with
        | Sum.inr e => return e
        | Sum.inl stack' => optimizeExprAux stack'

  | .InitNonFunOptimizeArgs f args idx stopIdx :: xs =>
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         if let some r ← funPropagation? f args (resolveArgs := true) (← isAppArg) then
           optimizeExprAux (r :: xs)
         else
           let prevInCtor ← isCtorArg
           setIsCtorArg (← isCtorExpr f)
           optimizeExprAux (.NonFunOptimizeArgs f args idx stopIdx prevInCtor :: xs)

  | .NonFunOptimizeArgs f args idx stopIdx prevInCtor :: xs =>
        if idx ≥ stopIdx then
          -- restore previous isCtorArg flag
          setIsCtorArg prevInCtor
          match (← finalizeNonFunApp f args xs) with
          | Sum.inr e' => return e'
          | Sum.inl stack' => optimizeExprAux stack'
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .AppOptimizeImplicitArgs f args idx startIdx stopIdx pInfo prevInApp :: xs =>
       if idx ≥ stopIdx then
         -- normalizing ite/match function application first to
         -- avoid handling extra args in optimizeDITEChoice, matchReduction and funPropagation
         if let some re ← normChoiceApplication? f args prevInApp then
           -- trace[Optimize.normChoiceApp] "normalizing choice application {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (re :: xs)
         else if isBlasterDiteConst f && args.size ≥ 2 then
           -- applying choice reduction to avoid optimizing unreachable arguments in Blaster.dite'
           setIsAppArg true
           let condOpt := .InitOptimizeExpr args[1]!
           optimizeExprAux (condOpt :: .DiteChoiceWaitForCond f args pInfo prevInApp :: xs)
         else if let some mInfo ← isMatcher? f then
            -- try match reduction rule first to avoid unnecessary optimization on discriminators
            if let some r ← matchReduction? f args mInfo (resolveArgs := true) prevInApp then
              optimizeExprAux (r :: xs)
            else
              -- applying choice reduction and match constant propagation to
              -- avoid optimizing unreachable rhs in match
              -- only optimizing match return type and discriminators first
              setIsAppArg true
              optimizeExprAux (.MatchChoiceOptimizeDiscrs f args pInfo (mInfo.getFirstDiscrPos - 1) mInfo prevInApp :: xs)
         -- try to apply funPropagation to avoid optimizing ite/match multiple times
         else if let some r ← funPropagation? f args (reorderArgs := true) (resolveArgs := true) prevInApp then
           optimizeExprAux (r :: xs)
         -- apply optimization on remaining explicit parameters before reduction
         else optimizeExprAux (.AppOptimizeExplicitArgs f args startIdx args.size pInfo none prevInApp :: xs)

       else if idx < pInfo.paramsInfo.size -- handle case when HOF is the returned type
            then if !pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)
                 else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo prevInApp :: xs)
            else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo prevInApp :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp :: xs =>
       if idx ≥ stopIdx then
         -- restore previous isAppArg flag
         setIsAppArg prevInApp
         -- apply match normalization rules
         if let some argInfo := mInfo then
           match (← optimizeMatch f args argInfo xs) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- apply ite normalization rules only when fully applied
         else if isBlasterDiteConst f && args.size == 4 then
           match (← optimizeIfThenElse? f args xs) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- try to reduce app if all params are constructors
         else if let some re ← reduceApp? f args then
           match re with
           | Sum.inl e =>
              match (← stackContinuity xs e) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'
           | Sum.inr be =>
               -- trace[Optimize.reduceApp] "application reduction {reprStr f} {reprStr args} => {reprStr re}"
               optimizeExprAux (.InitOptimizeExpr be.betaReduced be.prevMVarIdDecls :: xs)
         -- unfold non-recursive and non-opaque functions
         -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
         -- NOTE: we can only unfold once all parameters have been optimized.
         else if let some fdef ← getUnfoldFunDef? f args then
           -- trace[Optimize.unfoldDef] "unfolding function definition {reprStr f} {reprStr args} => {reprStr fdef}"
           optimizeExprAux (.InitOptimizeExpr fdef.betaReduced fdef.prevMVarIdDecls :: xs)
         -- normalizing partially apply function after unfolding non-opaque functions
         else if let some pe ← normPartialFun? f args then
           -- trace[Optimize.normPartial] "normalizing partial function {reprStr f} {reprStr args} => {reprStr pe}"
           optimizeExprAux (.InitOptimizeExpr pe :: xs)
         -- applying optimization on opaque rec function and app and proceed with fun propagation rules
         else optimizeExprAux (.InitOpaqueRecExpr f args :: xs)
       else if idx < pInfo.paramsInfo.size
            then if pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (← optimizeExplicitArgs f args idx stopIdx pInfo mInfo prevInApp stack xs)
                 else optimizeExprAux (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo prevInApp :: xs)
            else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchChoiceOptimizeDiscrs f args pInfo idx mInfo prevInApp :: xs =>
        if idx ≥ mInfo.getFirstAltPos then
          -- restore prevous isAppArg flag
          setIsAppArg prevInApp
          if let some r ← matchReduction? f args mInfo (matchToIte := true) prevInApp then
            optimizeExprAux (r :: xs)
          else
            -- apply optimization on remaining explicit parameters before reduction
            -- keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
            optimizeExprAux (.AppOptimizeExplicitArgs f args mInfo.getFirstAltPos args.size pInfo mInfo prevInApp :: xs)
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchRhsLambdaNext next :: xs =>
      match next with
      | Expr.lam n t b bi =>
          optimizeExprAux (.MatchLhsSkipForallType t :: .MatchRhsLambdaWaitForType n bi b :: xs)
      | _ =>
         -- header on xs is expected to be .MatchRhsLambdaWaitForBody
         match (← stackContinuity xs next) with
         | Sum.inl stack' => optimizeExprAux stack'
         | _ => throwEnvError "optimizeExprAux: continuity expected for MatchRhsLambdaNext !!!"

  | .MatchLhsSkipForallType e :: xs =>
      match e with
      | Expr.forallE n t b bi =>
          let stack' ←
            withLocalDecl' n bi t fun x => do
              pure $ .MatchLhsSkipForallType (← instantiateShared1 b x) :: .MatchLhsForallWaitForBody x :: xs
          optimizeExprAux stack'
      | _ => optimizeExprAux (.InitOptimizeExpr e :: xs) -- optimize lhs body

  | _ => throwEnvError "optimizeExprAux: unexpected optimize stack continuity {reprStr stack} !!!"

  where
    @[always_inline, inline]
    finalizeNonFunApp (f : Expr) (args : Array Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
      if ← isCtorExpr f
      then optimizeConstApp f args stack
      else stackContinuity stack (← mkAppNExpr f args)

    /-- Given `e := Expr.fVar fv` perform the following:
         - When `some v := fv.getValue?`
             - return `Sum.inl (.InitOptimizeExpr v :: stack)`
         - Otherwise:
             - return `stackContinuity stack (← mkExpr e)`
    -/
    @[always_inline, inline]
    normFVar (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity := do
      match ← e.fvarId!.getEnvValue? with
      | none => stackContinuity stack e
      | some v => return Sum.inl (.InitOptimizeExpr (← hashcons v) :: stack)

    @[always_inline, inline]
    inlineLet (v : Expr) (body : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      (.InitOptimizeExpr v :: .LetWaitForValue body :: stack)

    @[always_inline, inline]
    optimizeDiteArg (e : Expr) (cond : Expr) (isThen : Bool) (stack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
      match e with
      | Expr.lam n _t b bi =>
           let mkCond (c : Expr) : TranslateEnvT Expr := do
             if isThen then return c
             else mkAppExpr (← mkPropNotOp) c
           match ← reuseContext? e 0 with
           | some reuse =>
               let x := reuse.fvars[0]!
               setAndCommitCtx reuse.scope
               let body ← instantiateShared1 b x
               return .InitOptimizeExpr body :: .LambdaWaitForBody x (some reuse.scope) true 0 :: stack
           | none =>
               let t' ← mkCond cond
               withLocalDecl' n bi t' fun x => do
                 let bodyOpt := .InitOptimizeExpr (← instantiateShared1 b x)
                 let mscope ← addHypotheses t' x
                 return bodyOpt :: .LambdaWaitForBody x mscope true 0 :: stack
      | Expr.mvar _ => optimizeDiteArg (← getMVarValue e) cond isThen stack
      | _ => return .InitOptimizeExpr e :: stack

    @[always_inline, inline]
    optimizeExplicitArgs
     (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
     (pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (prevInApp : Bool)
     (stack : List OptimizeStack) (nxtStack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := do
      let currArg := args[idx]!
      if isBlasterDiteConst f then
         -- NOTE: optimization on Blaster.dite' cond already performed at this stage
         -- and idx starts as from 2 (see continuation for DiteChoiceWaitForCond)
        if idx == 2 || idx == 3 then
          optimizeDiteArg currArg args[1]! (idx == 2) stack
        else return (.InitOptimizeExpr currArg :: stack)
      else if let some argInfo := mInfo then
         -- NOTE: optimization on discriminators already performed at this stage
         -- and idx starts as from getFirstDiscrPos (see continuation for MatchChoiceOptimizeDiscrs).
         if idx >= argInfo.getFirstAltPos && idx < argInfo.arity then
           optimizeMatchAlt args argInfo idx currArg stack
         else return (.InitOptimizeExpr currArg :: stack)
      else if pInfo.paramsInfo[idx]!.isProp && (currArg.isFVar || (← isNotFun currArg.getAppFn)) then
          -- NOTE: We don't optimize proof arguments. We only do proof reconstruction when arg type differs
          let argType ← inferArgTypeAt pInfo.type args idx
          match (← inHypMap argType) with
          | some p =>
              if exprEq p currArg then
                return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo prevInApp :: nxtStack)
              else
                return (.AppOptimizeExplicitArgs f (args.set! idx p) (idx + 1) stopIdx pInfo mInfo prevInApp :: nxtStack)
          | none => -- TODO: add backward proof reconstruction
             return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo prevInApp :: nxtStack)
      else return (.InitOptimizeExpr currArg :: stack)


@[always_inline, inline]
def optimizeExpr (e : Expr) : TranslateEnvT Expr :=
  optimizeExprAux [.InitOptimizeExpr e]

/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun : TranslateEnvT Unit := do
  let commonExpr := (← get).optEnv.memCache.commonExpr
  callOptimize commonExpr.natAdd
  callOptimize commonExpr.natSub
  callOptimize commonExpr.natMul
  callOptimize commonExpr.natBle
  callOptimize commonExpr.natBeq
  callOptimize commonExpr.natPow
  callOptimize commonExpr.intPow

 where
   callOptimize (e : Expr) : TranslateEnvT Unit :=
     discard $ optimizeExprAux [.InitOpaqueRecExpr e #[]]


/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`
-/
def Optimize.mainAux (e : Expr) (applyHashCons := true) : TranslateEnvT Expr := do
  -- retention profiling: enabled only when BLASTER_RETENTION_PROFILE is set
  Retention.init
  -- populate recFunInstCache with recursive function definition.
  cacheOpaqueRecFun
  -- hash cons expression before optimization
  let r ←
    if applyHashCons
    then do
      let e' ← hashcons e
      -- register the original term as a GC root: it is alive for the whole
      -- run but visible only through this frame's locals
      Retention.gcExtraRootsRef.set #[e']
      optimizeExpr e'
    else do
      Retention.gcExtraRootsRef.set #[e]
      optimizeExpr e
  Retention.sample "final" 0
  return r

/-- Same as mainAux but set localContext -/
def Optimize.main (e : Expr) (applyHashCons := true) : TranslateEnvT Expr := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  Optimize.mainAux e applyHashCons


/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: This function is to be used only by callOptimize in package Test.
-/
def command (sOpts: BlasterOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let res ← Optimize.main e|>.run env
  return res


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Blaster.Optimize
