import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Optimize.Env
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
partial def optimizeExpr (sOpts: SolverOptions) (e : Expr) : TranslateEnvT Expr := do
  let rec visit (e : Expr) : TranslateEnvT Expr := do
    withOptimizeEnvCache e fun _ => do
    logReprExpr sOpts "Optimize:" e
    match e with
    | Expr.fvar .. => return e
    | Expr.const n l => normConst n l visit
    | Expr.forallE n t b bi =>
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          optimizeForall x t' (← visit (b.instantiate1 x))
    | Expr.app .. =>
        Expr.withApp e fun rf ras => do
        -- apply optimization on params first before reduction
        let fInfo ← getFunInfoNArgs rf ras.size
        let mut mas := ras
        for i in [:ras.size] do
          if i < fInfo.paramInfo.size then
            let aInfo := fInfo.paramInfo[i]!
            if aInfo.isExplicit then
              mas ← mas.modifyM i visit
          else
            mas ← mas.modifyM i visit
        -- try to reduce app if all params are constructors
        match (← reduceApp? rf mas) with
        | some re => visit re
        | none =>
          if rf.isLambda then
            -- perform beta-reduction
            visit (Expr.beta rf mas)
          else
            -- unfold non-recursive and non-opaque functions
            if let some fdef ← getUnfoldFunDef? rf mas then return (← visit fdef)
            -- normalize match expression to ite
            if let some mdef ← normMatchExpr? rf mas visit then return (← visit mdef)
            let f' ← visit rf
            normOpaqueAndRecFun f' mas visit
    | Expr.lam n t b bi => do
        let t' ← visit t
        withLocalDecl n bi t' fun x => do
          mkLambdaExpr x (← visit (b.instantiate1 x))
    | Expr.letE _n _t v b _ =>
        -- inline let expression
        let v' ← (visit v)
        visit (b.instantiate1 v')
    | Expr.mdata d me =>
       let me' ← visit me
       if (isTaggedRecursiveCall e)
       then mkExpr (Expr.mdata d me')
       else return me'
    | Expr.sort _ => return e -- sort is used for Type u, Prop, etc
    | Expr.proj .. =>
        match (← reduceProj? e) with
        | some re => visit re
        | none => return e
    | Expr.lit .. => return e -- number or string literal: do nothing
    | Expr.mvar .. => throwError f!"optimizeExpr: unexpected meta variable {e}"
    | Expr.bvar .. => throwError f!"optimizeExpr: unexpected bound variable {e}"
  visit e


/-- Populate the `recFunInstCache` with opaque recursive function definition.
    This function need to be call before performing optimization on a lean expression.
    NOTE: This function need to be updated each time we are opacifying a new recursive function.
-/
def cacheOpaqueRecFun (optimize : Expr → TranslateEnvT Expr) : TranslateEnvT Unit := do
  let natZero ← mkNatLitExpr 0
  let intZero ← mkIntLitExpr (Int.ofNat 0)
  callOptimize (mkApp (← mkNatAddOp) natZero)
  callOptimize (mkApp (← mkNatSubOp) natZero)
  callOptimize (mkApp (← mkNatMulOp) natZero)
  callOptimize (mkApp (← mkNatDivOp) natZero)
  callOptimize (mkApp (← mkNatModOp) natZero) -- TODO: need to handle Nat.mod case as is not directly recursive.
  callOptimize (mkApp (← mkNatBleOp) natZero)
  callOptimize (mkApp (← mkNatBeqOp) natZero)
  callOptimize (mkApp (← mkNatPowOp) natZero)
  callOptimize (mkApp (← mkIntPowOp) intZero)
  callOptimize (mkApp (← mkIntEDivOp) intZero)
  callOptimize (mkApp (← mkIntEModOp) intZero)

 where
   callOptimize (e : Expr) : TranslateEnvT Unit := discard $ optimize e

/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the optimization environment.
    NOTE: optimization is repeated until no entry is introduced in `replayRecFunMap`.
-/
partial def optimize (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  -- populate recFunInstCache with recursive function definition.
  let res ← cacheOpaqueRecFun (optimizeExpr sOpts)|>.run default
  optimizeExpr sOpts e|>.run res.2

end Solver.Optimize
