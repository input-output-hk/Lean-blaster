import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Optimize.Rewriting.OptimizeApp
import Solver.Optimize.Rewriting.OptimizeConst
import Solver.Optimize.Rewriting.OptimizeForAll
import Solver.Optimize.Rewriting.OptimizeMatch

open Lean Elab Command Term Meta Solver.Options

namespace Solver.Optimize

-- TODO: update formalization with inference rule style notation.
--  - ((∀ x : Type), P₁ x) → (∀ (a b .. n : Type), P₂ a b n) ==> (∀ (a b ... n : Type), P₁ a → P₁ b → P₁ c .. → P₁ n → P₂ a b .. n)
--  - ¬ ((∀ x : Type), P x) ==> ∃ (x : Type), ¬ P x
--  - ¬ ((∃ x : Type), P x) ==> ∀ (x : Type), ¬ P x
-- Need to consider ArrowT as introducing assumptions s.t.
--  - ∀ (x y : Type) x = y → f x = f y ==> ∀ (x y : Type) f x = f x => True
-- The COI computation must handle the following cases as well:
--  - (∀ (x₁ : TypeA₁) ... (xₙ : TypeAₙ), P₁ x₁ ... xₙ) → (∀ (y₁ : TypeB₁ .. yₙ : TypeBₙ), P₂ y₁ ... yₙ) ===>
--       ∀ (y₁ : TypeB₁ .. yₙ : Typeₙ), P₂ y₁ ... yₙ) IF {TypeB₁, .., TypeBₙ} ⊄ {TypeA₁, ...,TypeAₙ}
-- - ∀ (x₁ : TypeA₁) ... (xₙ : TypeAₙ), P₁ → P₂ ===>
--      ∀ (x₄ : TypeA₄) ... (xₙ : TypeAₙ), P₂ x₄ ... xₙ IF Var(P₂) ∩ Var(P₁) = ∅
partial def optimizeExpr (e : Expr) : TranslateEnvT Expr := do
  let rec visit (e : Expr) : TranslateEnvT Expr := do
    withOptimizeEnvCache e fun _ => do
    trace[Optimize.expr] f!"optimizing {reprStr e}"
    logReprExpr "Optimize:" e
    match e with
    | Expr.fvar .. => return e
    | Expr.const .. => normConst e visit
    | Expr.forallE n t b bi =>
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          optimizeForall x t' (← visit (b.instantiate1 x))
    | Expr.app .. =>
        Expr.withApp e fun f ras => do
         -- calling normConst explicitly for `const` case to avoid
         -- catching when no optimization is performed on foldable body function.
         let f' ← if f.isConst then withInFunApp $ normConst f visit else visit f
         -- apply optimization on params first before reduction
         -- we need to apply optimization even on the implicit arguments
         -- to remove mdata annotation and have max expression sharing.
         let rf := f'.getAppFn'
         let extraArgs := f'.getAppArgs
         let mut mas := extraArgs ++ ras
         for i in [extraArgs.size:mas.size] do
            mas ← mas.modifyM i visit
         -- try to reduce app if all params are constructors
         match (← reduceApp? rf mas) with
         | some re =>
             trace[Optimize.reduceApp] f!"application reduction {reprStr rf} {reprStr mas} => {reprStr re}"
             visit re
         | none =>
            -- unfold non-recursive and non-opaque functions
            -- NOTE: beta reduction performed by getUnfoldFunDef? when rf is a lambda term
            if let some fdef ← getUnfoldFunDef? rf mas then
               trace[Optimize.unfoldDef] f!"unfolding function definition {reprStr rf} {reprStr mas} => {reprStr fdef}"
               return (← visit fdef)
            -- normalize match expression to ite
            if let some mdef ← normMatchExpr? rf mas visit then
               trace[Optimize.normMatch] f!"normalizing match to ite {reprStr rf} {reprStr mas} => {reprStr mdef}"
               return (← visit mdef)
            if let some pe ← normPartialFun? rf mas then
               trace[Optimize.normPartial] f!"normalizing partial function {reprStr rf} {reprStr mas} => {reprStr pe}"
               return (← visit pe)
            normOpaqueAndRecFun rf mas visit
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

/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: optimization is repeated until no entry is introduced in `replayRecFunMap`.
-/
def optimize (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  -- populate recFunInstCache with recursive function definition.
  let res ← cacheOpaqueRecFun (λ a => optimizeExpr a)|>.run env
  optimizeExpr e|>.run res.2


initialize
  registerTraceClass `Optimize.expr
  registerTraceClass `Optimize.reduceApp
  registerTraceClass `Optimize.unfoldDef
  registerTraceClass `Optimize.normMatch
  registerTraceClass `Optimize.normPartial

end Solver.Optimize
