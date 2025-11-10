import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Optimize.Rewriting.FunPropagation
import Solver.Optimize.Rewriting.OptimizeApp
import Solver.Optimize.Rewriting.OptimizeConst
import Solver.Optimize.Rewriting.OptimizeForAll

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Optimize

-- TODO: update formalization with inference rule style notation.
partial def optimizeExprAux (stack : List OptimizeStack) : TranslateEnvT Expr := do
  match stack with
  | .InitOptimizeExpr e :: xs =>
      match (← isInOptimizeEnvCache e xs) with
      | Sum.inl i_stack =>
          -- trace[Optimize.expr] "optimizing {← ppExpr e}"
          match e with
          | Expr.fvar _ =>
              match (← normFVar e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.sort l =>
              -- sort is used for Type u, Prop, etc
              let s' ← mkExpr (Expr.sort (normLevel l))
              match (← stackContinuity i_stack s') with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.lit .. => -- number or string literal
              match (← stackContinuity i_stack (← mkExpr e)) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.const .. =>
              match (← normConst e i_stack) with
              | Sum.inr e' => return e'
              | Sum.inl stack' => optimizeExprAux stack'

          | Expr.forallE n t b bi =>
              optimizeExprAux (.InitOptimizeExpr t :: .ForallWaitForType n bi b :: i_stack)

          | Expr.app .. =>
             let (f, ras) := getAppFnWithArgs e
             -- check if f is a lambda term
             if f.isLambda then
               -- perform beta reduction and apply optimization
               optimizeExprAux (.InitOptimizeExpr (Expr.beta f ras) :: i_stack)
             else
               -- set inFunApp flag before optimizing `f`
               setInFunApp true
               let i_stack' := .AppWaitForConst ras :: i_stack
               optimizeExprAux (.InitOptimizeExpr f :: i_stack')

          | Expr.lam n t b bi => optimizeExprAux (optimizeLambda n t b bi i_stack)

          | Expr.letE _n _t v b _ => optimizeExprAux (inlineLet v b i_stack) -- inline let expression

          | Expr.mdata d me =>
              if (isTaggedRecursiveCall e) then
                setNormalizeFunCall false
                optimizeExprAux (.InitOptimizeExpr me :: .MDataRecCallWaitForExpr d :: i_stack)
              else optimizeExprAux (.InitOptimizeExpr me :: i_stack)

          | Expr.proj n idx s =>
              let i_stack' := .ProjWaitForExpr n idx :: i_stack
              optimizeExprAux (.InitOptimizeExpr s :: i_stack')

          | Expr.mvar .. => throwEnvError "optimizeExpr: unexpected meta variable {e}"
          | Expr.bvar .. => throwEnvError "optimizeExpr: unexpected bound variable {e}"

      | Sum.inr (Sum.inr e') => return e'
      | Sum.inr (Sum.inl stack') => optimizeExprAux stack'

  | .InitNextOptimize e :: xs =>
        match (← stackContinuity xs e) with
        | Sum.inr e' => return e'
        | Sum.inl stack' => optimizeExprAux stack'

  | s@(.InitOpaqueRecExpr ..) :: xs
  | s@(.RecFunDefStorage ..) :: xs =>
        match (← normOpaqueAndRecFun s xs) with
        | Sum.inr e => return e
        | Sum.inl stack' => optimizeExprAux stack'

  | .ForallOptimize x t b hyps :: xs =>
        match (← forallContinuity x t hyps b xs) with
        | Sum.inr e => return e
        | Sum.inl stack' => optimizeExprAux stack'

  | .InitOptimizeMatchInfo f args startArgIdx pInfo :: xs =>
      -- optimize match generic instance (if any)
      match (← hasUnOptMatchInfo? f) with
      | none =>
          -- continuity with optimization on implicit arguments
          optimizeExprAux (.AppOptimizeImplicitArgs f args startArgIdx startArgIdx args.size pInfo :: xs)
      | some (mInfo, instApp) =>
          -- optimizing match generic instance
          let mWait := .OptimizeMatchInfoWaitForInst f args startArgIdx pInfo mInfo :: xs
          -- NOTE: instApp is expected to be a lambda term
          -- NOTE: we here only want to optimize the lambda params type, which mainly
          -- correspond to the match lhs.
          match instApp with
          | Expr.lam n t b bi =>
              let typeOpt := .InitOptimizeExpr t
              let lamWait := .MatchRhsLambdaWaitForType n bi b
              optimizeExprAux (typeOpt :: lamWait :: mWait)
          | _ => throwEnvError "optimizeExprAux: lambda expected for match instance but got {reprStr instApp}"

  | .AppOptimizeImplicitArgs f args idx startIdx stopIdx pInfo :: xs =>
       if idx ≥ stopIdx then
         -- applying choice reduction to avoid optimizing unreachable arguments in ite
         optimizeExprAux (.InitIteChoiceExpr f args pInfo startIdx :: xs)
       else if idx < pInfo.paramsInfo.size -- handle case when HOF is the returned type
            then if !pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)
                 else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo :: xs)
            else optimizeExprAux (.AppOptimizeImplicitArgs f args (idx + 1) startIdx stopIdx pInfo :: xs)

  | .AppOptimizeExplicitArgs f args idx stopIdx pInfo mInfo :: xs =>
       if idx ≥ stopIdx then
         -- normalizing ite/match function application
         if let some re ← normChoiceApplication? f args then
           -- trace[Optimize.normChoiceApp] "normalizing choice application {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (.InitOptimizeExpr re :: xs)
         -- apply match normalization rules
         else if let some argInfo := mInfo then
           match (← optimizeMatch f args argInfo xs) with
           | Sum.inr e' => return e'
           | Sum.inl stack' => optimizeExprAux stack'
         -- try to reduce app if all params are constructors
         else if let some re ← reduceApp? f args then
           -- trace[Optimize.reduceApp] "application reduction {reprStr f} {reprStr args} => {reprStr re}"
           optimizeExprAux (.InitOptimizeExpr re :: xs)
         -- unfold non-recursive and non-opaque functions
         -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
         -- NOTE: we can only unfold once all parameters have been optimized.
         else if let some fdef ← getUnfoldFunDef? f args then
           -- trace[Optimize.unfoldDef] "unfolding function definition {reprStr f} {reprStr args} => {reprStr fdef}"
           optimizeExprAux (.InitOptimizeExpr fdef :: xs)
         -- normalizing partially apply function after unfolding non-opaque functions
         else if let some pe ← normPartialFun? f args then
           -- trace[Optimize.normPartial] "normalizing partial function {reprStr f} {reprStr args} => {reprStr pe}"
           optimizeExprAux (.InitOptimizeExpr pe :: xs)
         -- applying optimization on opaque rec function and app and proceed with fun propagation rules
         else optimizeExprAux (.InitOpaqueRecExpr f args :: xs)
       else if idx < pInfo.paramsInfo.size
            then if pInfo.paramsInfo[idx]!.isExplicit
                 then optimizeExprAux (← optimizeExplicitArgs f args idx stopIdx pInfo mInfo stack xs)
                 else optimizeExprAux (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: xs)
            else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | s@(.InitIteChoiceExpr f args pInfo startArgIdx) :: xs
  | s@(.IteChoiceReturn f args pInfo startArgIdx) :: xs
  | s@(.DiteChoiceReturn f args pInfo startArgIdx) :: xs =>
     match (← reduceITEChoice? s xs) with
     | none =>
         -- applying choice reduction and match constant propagation to
         -- avoid optimizing unreachable arguments in match
         optimizeExprAux (.InitMatchChoiceExpr f args pInfo startArgIdx :: xs)
     | some (Sum.inl stack') => optimizeExprAux stack'
     | _ => throwEnvError "optimizeExprAux: continuity expected for reduceIteChoice? !!!"

  | s@(.InitMatchChoiceExpr f args pInfo startArgIdx) :: xs
  | s@(.MatchChoiceReduce f args pInfo startArgIdx _) :: xs =>
       match (← reduceMatchChoice? s xs) with
       | none =>
           -- apply optimization on remaining explicit parameters before reduction
           -- keep matchInfo to avoid unnecessary query and to avoid optimizing discriminators again
           let minfo ← isMatcher? f
           optimizeExprAux (.AppOptimizeExplicitArgs f args startArgIdx args.size pInfo minfo :: xs)
       | some (Sum.inl stack') => optimizeExprAux stack'
       | _ => throwEnvError "optimizeExprAux: continuity expected for reduceMatchChoice? !!!"

  | .MatchChoiceOptimizeDiscrs f args pInfo startArgIdx idx mInfo :: xs =>
        if idx ≥ mInfo.getFirstAltPos
        then optimizeExprAux (.MatchChoiceReduce f args pInfo startArgIdx mInfo :: xs)
        else optimizeExprAux (.InitOptimizeExpr args[idx]! :: stack)

  | .MatchRhsLambdaNext next :: xs =>
      match next with
      | Expr.lam n t b bi =>
          optimizeExprAux (.InitOptimizeExpr t :: .MatchRhsLambdaWaitForType n bi b :: xs)
      | _ =>
         -- header on xs is expected to be .MatchRhsLambdaWaitForBody
         match (← stackContinuity xs next) with
         | Sum.inl stack' => optimizeExprAux stack'
         | _ => throwEnvError "optimizeExprAux: continuity expected for MatchRhsLambdaNext !!!"

  | s@(.InitOptimizeMatchAlt ..) :: xs
  | s@(.MatchAltOptimize ..) :: xs =>
       match (← optimizeMatchAlt s xs) with
        | Sum.inl stack' => optimizeExprAux stack'
        | _ => throwEnvError "optimizeExprAux: continuity expected for optimizeMatchAlt !!!"

  | _ => throwEnvError "optimizeExprAux: unexpected optimize stack continuity {reprStr stack} !!!"

  where

    /-- Given `e := Expr.fVar fv` perform the following:
         - When `some v := fv.getValue?`
             `return `Sum.inl (.InitOptimizeExpr v :: stack)`
         - Otherwise:
              `return `stackContinuity stack (← mkExpr e)`
    -/
    @[always_inline, inline]
    normFVar (e : Expr) (stack : List OptimizeStack) : TranslateEnvT OptimizeContinuity :=
      withLocalContext $ do
        match ← e.fvarId!.getValue? with
        | none => stackContinuity stack (← mkExpr e)
        | some v =>
            return Sum.inl (.InitOptimizeExpr (← instantiateMVars v) :: stack)

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
    inlineLet (v : Expr) (body : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      (.InitOptimizeExpr v :: .LetWaitForValue body :: stack)

    @[always_inline, inline]
    optimizeLambda
      (n : Name) (t : Expr) (b : Expr) (bi : BinderInfo)
      (xs : List OptimizeStack) (inDite := false) : List OptimizeStack :=
        (.InitOptimizeExpr t :: .LambdaWaitForType n bi b inDite :: xs)

    @[always_inline, inline]
    optimizeDiteArg (e : Expr) (stack : List OptimizeStack) : List OptimizeStack :=
      match e with
      | Expr.lam n t b bi => optimizeLambda n t b bi stack (inDite := true)
      | _ => .InitOptimizeExpr e :: stack

    @[always_inline, inline]
    optimizeExplicitArgs
      (f : Expr) (args : Array Expr) (idx : Nat) (stopIdx : Nat)
      (pInfo : FunEnvInfo) (mInfo : Option MatchInfo) (stack : List OptimizeStack)
      (nxtStack : List OptimizeStack) : TranslateEnvT (List OptimizeStack) := withLocalContext $ do
      if isIteConst f then
       if idx == 1 then
         -- skipping optimization for ite cond as already performed by reduceITechoice?
         return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: nxtStack)
       else if idx == 3 then
         let hyps ← addHypotheses args[1]! none
         let hypsCtx ← mkHypStackContext hyps
         return (.InitOptimizeExpr args[idx]! :: .HypothesisWaitForExpr hypsCtx :: stack)
       else if idx == 4 then
         let notExpr ← optimizeNot (← mkPropNotOp) #[args[1]!] (cacheResult := false)
         let hyps ← addHypotheses notExpr none
         let hypsCtx ← mkHypStackContext hyps
         return (.InitOptimizeExpr args[idx]! :: .HypothesisWaitForExpr hypsCtx :: stack)
       else return (.InitOptimizeExpr args[idx]! :: stack)
      else if isDiteConst f then
        if idx == 1 then
         -- skipping optimization for ite cond as already performed by reduceITechoice?
         return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: nxtStack)
        else if idx == 3 || idx == 4
        then return optimizeDiteArg args[idx]! stack
        else return (.InitOptimizeExpr args[idx]! :: stack)
      else if let some argInfo := mInfo then
         if idx >= argInfo.getFirstDiscrPos && idx < argInfo.getFirstAltPos then
           -- skipping optimization for discriminators as already performed by reduceMatchChoice?
           return (.AppOptimizeExplicitArgs f args (idx + 1) stopIdx pInfo mInfo :: nxtStack)
         else if idx >= argInfo.getFirstAltPos && idx < argInfo.arity then
           return (.InitOptimizeMatchAlt args argInfo idx args[idx]! :: stack)
         else return (.InitOptimizeExpr args[idx]! :: stack)
      else return (.InitOptimizeExpr args[idx]! :: stack)


@[always_inline, inline]
def optimizeExpr (e : Expr) : TranslateEnvT Expr :=
  optimizeExprAux [.InitOptimizeExpr e ]

/-- Same as optimizeExpr but updates local context before optimizing expression -/
@[always_inline, inline]
def optimizeExpr' (e : Expr) : TranslateEnvT Expr := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  optimizeExprAux [.InitOptimizeExpr e ]

/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun : TranslateEnvT Unit := do
  callOptimize natAdd
  callOptimize natSub
  callOptimize natMul
  callOptimize natBle
  callOptimize natBeq
  callOptimize natPow
  callOptimize intPow

 where
   callOptimize (e : Expr) : TranslateEnvT Unit :=
     discard $ optimizeExprAux [.InitOpaqueRecExpr e #[]]

/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`
-/
def Optimize.main (e : Expr) : TranslateEnvT Expr := do
  -- set start local context
  updateLocalContext (← mkLocalContext)
  -- populate recFunInstCache with recursive function definition.
  cacheOpaqueRecFun
  optimizeExpr e


/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: This function is to be used only by callOptimize in package Test.
-/
def command (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  -- keep the current name generator and restore it afterwards
  let ngen ← getNGen
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let res ← Optimize.main e|>.run env
  -- restore name generator
  setNGen ngen
  return res


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Solver.Optimize
