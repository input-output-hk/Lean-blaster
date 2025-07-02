import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Optimize.Rewriting.FunPropagation
import Solver.Optimize.Rewriting.NormalizeMatch
import Solver.Optimize.Rewriting.OptimizeApp
import Solver.Optimize.Rewriting.OptimizeConst
import Solver.Optimize.Rewriting.OptimizeForAll

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Optimize

-- TODO: update formalization with inference rule style notation.
partial def optimizeExpr (e : Expr) : TranslateEnvT Expr := do
  let rec visit (e : Expr) : TranslateEnvT Expr := do
    withOptimizeEnvCache e fun _ => do
    trace[Optimize.expr] f!"optimizing {← ppExpr e}"
    logReprExpr "Optimize:" e
    match e with
    | Expr.fvar .. => return e
    | Expr.const .. => normConst e visit
    | Expr.forallE n t b bi =>
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          optimizeForall x t' (← visit (b.instantiate1 x))
    | Expr.app .. =>
        let (f, ras) := getAppFnWithArgs e
        -- calling normConst explicitly for `const` case to avoid
        -- catching when no optimization is performed on foldable body function.
        let f' ← if f.isConst then withInFunApp $ normConst f visit else visit f
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
           trace[Optimize.reduceChoice] f!"choice ite reduction {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- applying choice reduction and match constant propagation to
        -- avoid optimizing unreachable arguments in match
        if let some re ← reduceMatchChoice? rf mas visit then
           trace[Optimize.matchConstPropagation]
             f!"match constant propagation {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- apply optimization on remaining explicit parameters before reduction
        for i in [extraArgs.size:mas.size] do
          if i < fInfo.paramInfo.size then
            if fInfo.paramInfo[i]!.isExplicit then
              mas ← mas.modifyM i visit
          else mas ← mas.modifyM i visit
        -- try to reduce app if all params are constructors
        if let some re ← reduceApp? rf mas then
          trace[Optimize.reduceApp] f!"application reduction {reprStr rf} {reprStr mas} => {reprStr re}"
          return (← visit re)
        -- unfold non-recursive and non-opaque functions
        -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
        -- NOTE: we can only unfold once all parameters have been optimized.
        if let some fdef ← getUnfoldFunDef? rf mas then
           trace[Optimize.unfoldDef] f!"unfolding function definition {reprStr rf} {reprStr mas} => {reprStr fdef}"
           return (← visit fdef)
        -- normalizing partially apply function after unfolding non-opaque functions
        if let some pe ← normPartialFun? rf mas then
           trace[Optimize.normPartial] f!"normalizing partial function {reprStr rf} {reprStr mas} => {reprStr pe}"
           return (← visit pe)
        -- normalizing ite/match function application
        if let some re ← normChoiceApplication? rf mas then
           trace[Optimize.normChoiceApp]
             f!"normalizing choice application {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        -- normalize match expression to ite
        if let some mdef ← normMatchExpr? rf mas visit then
           trace[Optimize.normMatch] f!"normalizing match to ite {reprStr rf} {reprStr mas} => {reprStr mdef}"
           return (← visit mdef)
        let ne ← normOpaqueAndRecFun rf mas visit
        -- applying fun propagation over ite and match
        if let some re ← funPropagation? ne then
           trace[Optimize.funPropagation]
             f!"ctor constant propagation {reprStr rf} {reprStr mas} => {reprStr re}"
           return (← visit re)
        return ne
    | Expr.lam n t b bi => do
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          mkLambdaExpr x (← visit (b.instantiate1 x))
    | Expr.letE _n _t v b _ =>
        -- inline let expression
        let v' ← (visit v)
        visit (b.instantiate1 v')
    | Expr.mdata d me =>
       if (isTaggedRecursiveCall e)
       then mkExpr (Expr.mdata d (← withOptimizeRecBody $ visit me))
       else visit me
    | Expr.sort _ => return e -- sort is used for Type u, Prop, etc
    | Expr.proj .. =>
        match (← reduceProj? e) with
        | some re => visit re
        | none => return e
    | Expr.lit .. => return e -- number or string literal: do nothing
    | Expr.mvar .. => throwEnvError f!"optimizeExpr: unexpected meta variable {e}"
    | Expr.bvar .. => throwEnvError f!"optimizeExpr: unexpected bound variable {e}"
  visit e


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
  registerTraceClass `Optimize.reduceChoice
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef

end Solver.Optimize
