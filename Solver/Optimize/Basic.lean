import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Optimize.Rewriting.FunPropagation
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeApp
import Solver.Optimize.Rewriting.OptimizeConst
import Solver.Optimize.Rewriting.OptimizeForAll
import Solver.Optimize.Rewriting.OptimizeProjection


open Lean Elab Command Term Meta Solver.Options

namespace Solver.Optimize

-- TODO: update formalization with inference rule style notation.
partial def optimizeExpr (ve : Expr) : TranslateEnvT Expr := do
  let rec visit (e : Expr) : TranslateEnvT Expr := do
    withOptimizeEnvCache e fun _ => do
    trace[Optimize.expr] "optimizing {← ppExpr e}"
    match e with
    | Expr.fvar .. => mkExpr e
    | Expr.const .. => normConst e visit
    | Expr.forallE n t b bi =>
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          let hyps ← addHypotheses t' (some x)
          optimizeForall x t' hyps.2 (← withHypothesis hyps $ do visit (b.instantiate1 x))
    | Expr.app .. =>
        let (f, ras) := getAppFnWithArgs e
        -- calling normConst explicitly for `const` case to avoid
        -- catching when no optimization is performed on opaque functions.
        let f' ← if f.isConst then withInFunApp $ do normConst f visit else visit f
        let rf := f'.getAppFn'
        let extraArgs := f'.getAppArgs
        let mut mas := extraArgs ++ ras
        let fInfo ← getFunInfoNArgs rf mas.size
        -- apply optimization only on implicit parameters to remove mdata annotation
        -- we don't consider explicit parameters at this stage to avoid performing
        -- optimization on unreachable arguments
        for i in [extraArgs.size:mas.size] do
          if i < fInfo.paramInfo.size then -- handle case when HOF is passed as argument
            if !fInfo.paramInfo[i]!.isExplicit then
              mas ← mas.modifyM i visit
        -- applying choice reduction to avoid optimizing unreachable arguments in ite
        if let some re ← reduceITEChoice? rf mas visit then
           trace[Optimize.reduceChoice] "choice ite reduction {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- applying choice reduction and match constant propagation to
        -- avoid optimizing unreachable arguments in match
        if let some re ← reduceMatchChoice? rf mas visit then
           trace[Optimize.matchConstPropagation]
             "match constant propagation {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- apply optimization on remaining explicit parameters before reduction
        for i in [extraArgs.size:mas.size] do
          if i < fInfo.paramInfo.size then
            if fInfo.paramInfo[i]!.isExplicit then
              mas ← optimizeExplicitArgs rf mas i visit
          else mas ← mas.modifyM i visit
        -- try to reduce app if all params are constructors
        if let some re ← reduceApp? rf mas then
          trace[Optimize.reduceApp] "application reduction {reprStr rf} {reprStr mas} => {reprStr re}"
          return (← visit re)
        -- unfold non-recursive and non-opaque functions
        -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
        -- NOTE: we can only unfold once all parameters have been optimized.
        if let some fdef ← getUnfoldFunDef? rf mas then
           trace[Optimize.unfoldDef] "unfolding function definition {reprStr rf} {reprStr mas} => {reprStr fdef}"
           return (← visit fdef)
        -- normalizing partially apply function after unfolding non-opaque functions
        if let some pe ← normPartialFun? rf mas then
           trace[Optimize.normPartial] "normalizing partial function {reprStr rf} {reprStr mas} => {reprStr pe}"
           return (← visit pe)
        -- normalizing ite/match function application
        if let some re ← normChoiceApplication? rf mas then
           trace[Optimize.normChoiceApp]
             "normalizing choice application {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- normalize match expression to ite
        if let some mdef ← normMatchExpr? rf mas visit then
           trace[Optimize.normMatch] "normalizing match to ite {reprStr rf} {reprStr mas} => {reprStr mdef}"
           return (← visit mdef)
        -- applying fun propagation over ite and match
        if let some re ← funPropagation? rf mas then
           trace[Optimize.funPropagation]
             "fun propagation {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        normOpaqueAndRecFun rf mas visit
    | Expr.lam n t b bi => optimizeLambda n t b bi visit
    | Expr.letE _n _t v b _ =>
        -- inline let expression
        let v' ← (visit v)
        visit (b.instantiate1 v')
    | Expr.mdata d me =>
       if (isTaggedRecursiveCall e)
       then mkExpr (Expr.mdata d (← withOptimizeRecBody $ visit me))
       else visit me
    | Expr.sort _ => mkExpr e -- sort is used for Type u, Prop, etc
    | Expr.proj .. =>
        if let some re ← optimizeProjection? e then
          trace[Optimize.normProjection]
             "normalizing projection {reprStr e} => {reprStr re}"
          return (← visit re)
        mkExpr e
    | Expr.lit .. => mkExpr e -- number or string literal: do nothing
    | Expr.mvar .. => throwEnvError f!"optimizeExpr: unexpected meta variable {e}"
    | Expr.bvar .. => throwEnvError f!"optimizeExpr: unexpected bound variable {e}"
  visit ve

  where

    @[always_inline, inline]
    optimizeLambda
      (n : Name) (t : Expr) (b : Expr) (bi : BinderInfo)
      (optimizer : Expr → TranslateEnvT Expr) (inDite := false) : TranslateEnvT Expr := do
        let t' ← optimizer t
        withLocalDecl n bi t' fun x => do
          if inDite
          then
            let hyps ← addHypotheses t' (some x)
            withHypothesis hyps $ do mkLambdaExpr x (← optimizer (b.instantiate1 x))
          else mkLambdaExpr x (← optimizer (b.instantiate1 x))

    @[always_inline, inline]
    optimizeDiteArg (optimizer : Expr → TranslateEnvT Expr) (e : Expr) : TranslateEnvT Expr := do
      match e with
      | Expr.lam n t b bi => optimizeLambda n t b bi optimizer (inDite := true)
      | _ => optimizer e

    @[always_inline, inline]
    optimizeExplicitArgs
      (rf : Expr) (mas : Array Expr) (idx : Nat)
      (optimizer : Expr → TranslateEnvT Expr) : TranslateEnvT (Array Expr) := do
      if isIteConst rf then
       if idx == 3 then
         let hyps ← addHypotheses mas[1]! none
         withHypothesis hyps $ do mas.modifyM idx optimizer
       else if idx == 4 then
         let notExpr ← optimizeNot (← mkPropNotOp) #[mas[1]!]
         let hyps ← addHypotheses notExpr none
         withHypothesis hyps $ do mas.modifyM idx optimizer
       else mas.modifyM idx optimizer
      else if isDiteConst rf then
        if idx == 3 || idx == 4 then mas.modifyM idx (optimizeDiteArg optimizer)
        else mas.modifyM idx optimizer
      else if let some argInfo ← isMatcher? (mkAppN rf mas) then
         if idx >= argInfo.mInfo.getFirstAltPos && idx < argInfo.mInfo.arity then
           mas.modifyM idx (optimizeMatchAlt argInfo mas optimizer idx)
         else mas.modifyM idx optimizer
      else mas.modifyM idx optimizer


/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun (optimize : Expr → TranslateEnvT Expr) : TranslateEnvT Unit := do
  callOptimize natAdd
  callOptimize natSub
  callOptimize natMul
  callOptimize natDiv
  callOptimize natBle
  callOptimize natBeq
  callOptimize natPow
  callOptimize intPow

 where
   callOptimize (e : Expr) : TranslateEnvT Unit :=
     discard $ normOpaqueAndRecFun e #[] optimize

/-- Perform the following actions:
      - populate the recFunInstCache with default recursive function definitions.
      - optimize expression `e`
-/
def Optimize.main (e : Expr) : TranslateEnvT Expr := do
  -- populate recFunInstCache with recursive function definition.
  cacheOpaqueRecFun (λ a => optimizeExpr a)
  optimizeExpr e


/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: optimization is repeated until no entry is introduced in `replayRecFunMap`.
-/
def command (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  Optimize.main e|>.run env


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.funPropagation
  registerTraceClass `Optimize.matchConstPropagation
  registerTraceClass `Optimize.normChoiceApp
  registerTraceClass `Optimize.normMatch
  registerTraceClass `Optimize.normPartial
  registerTraceClass `Optimize.normProjection
  registerTraceClass `Optimize.reduceChoice
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Solver.Optimize
