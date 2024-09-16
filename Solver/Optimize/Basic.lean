import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Translate.Env
import Solver.Optimize.OptimizeApp
import Solver.Optimize.OptimizeForAll

open Lean Elab Command Term Meta

namespace Solver.Optimize

-- TODO: update specification
-- Some translation notes
-- Some translation rules
--  - ((∀ x : Type), P₁ x) → (∀ (a b .. n : Type), P₂ a b n) ==> (∀ (a b .. n : Type), P₁ a → P₁ b → P₁ c .. → P₁ n → P₂ a b .. n)
--  - ¬ ((∀ x : Type), P x) ==> ∃ (x : Type), ¬ P x
--  - ¬ ((∃ x : Type), P x) ==> ∀ (x : Type), ¬ P x
-- Need to consider ArrowT as introducing assumptions s.t.
--  - ∀ (x y : Type) x = y → f x = f y ==> ∀ (x y : Type) f x = f x => True
-- The COI computation must handle the following cases as well:
--  - (∀ (x₁ : TypeA₁) ... (xₙ : TypeAₙ), P₁ x₁ ... xₙ) → (∀ (y₁ : TypeB₁ .. yₙ : TypeBₙ), P₂ y₁ ... yₙ) ===>
--       ∀ (y₁ : TypeB₁ .. yₙ : Typeₙ), P₂ y₁ ... yₙ) IF {TypeB₁, .., TypeBₙ} ⊄ {TypeA₁, ...,TypeAₙ}
-- - ∀ (x₁ : TypeA₁) ... (xₙ : TypeAₙ), P₁ → P₂ ===>
--      ∀ (x₄ : TypeA₄) ... (xₙ : TypeAₙ), P₂ x₄ ... xₙ IF Var(P₂) ∩ Var(P₁) = ∅
partial def optimize (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) :=
  let rec visit (e : Expr) : TranslateEnvT Expr := do
    withTranslateEnvCache e fun _ => do
    logReprExpr sOpts "Optimize:" e
    match e with
    | Expr.fvar v =>
        -- adding free variable not required
        addFVar v >>= (fun _ => return e)
    | Expr.const n l => normConst n l
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
             match (← getUnfoldFunDef? rf mas) with
             | some fdef => visit fdef
             | none =>
                -- normalize and cache opaque and recursive function name
                let f' ← visit rf
                optimizeApp f' mas -- optimizations on opaque functions
    | Expr.lam n t b bi => do
       let t' ← visit t
       withLocalDecl n bi t' fun x => do
         mkLambdaExpr x (← visit (b.instantiate1 x))
    | Expr.letE n t v b _ =>
       -- inline let expression
       let t' ← (visit t)
       let v' ← (visit v)
       withLetDecl n t' v' fun _ =>
         visit (b.instantiate1 v')
    | Expr.mdata _ me => visit me
    | Expr.sort _ => return e -- sort is used for Type u, Prop, etc
    | Expr.proj .. =>
       match (← reduceProj? e) with
       | some re => return re
       | none => return e
    | Expr.lit .. => return e -- number or string literal: do nothing
    | Expr.mvar .. => throwError f!"unexpected meta variable {e}"
    | Expr.bvar .. => throwError f!"unexpected bounded variable {e}"
   visit e |>.run default

end Solver.Optimize
