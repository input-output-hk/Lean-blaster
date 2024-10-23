import Lean
import Lean.Util.MonadCache
import Solver.Command.Options
import Solver.Logging
import Solver.Translate.Env
import Solver.Optimize.OptimizeApp
import Solver.Optimize.OptimizeForAll
import Solver.Optimize.OptimizeMatch

open Lean Elab Command Term Meta

namespace Solver.Optimize

-- TODO: update formalization with inference rule style notation.
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
mutual
  partial def optimizeExpr (sOpts: SolverOptions) (e : Expr) : TranslateEnvT Expr := do
    let rec visit (e : Expr) : TranslateEnvT Expr := do
      withTranslateEnvCache e fun _ => do
      logReprExpr sOpts "Optimize:" e
      match e with
      | Expr.fvar .. => return e
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
              if let some fdef ← getUnfoldFunDef? rf mas then return (← visit fdef)
              -- normalize match expression to ite
              if let some mdef ← matchExprRewriter sOpts rf mas normMatchExpr? then return (← visit mdef)
              let f' ← visit rf
              normOpaqueAndRecFun sOpts f' mas
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
          | some re => mkExpr re
          | none => return e
      | Expr.lit .. => return e -- number or string literal: do nothing
      | Expr.mvar .. => throwError f!"unexpected meta variable {e}"
      | Expr.bvar .. => throwError f!"unexpected bounded variable {e}"
    visit e

  /-- Given application `f x₁ ... xₙ` perform the following:
      - when `f` corresponds to a recursive definition `λ p₁ ... pₙ → fbody` the following actions are performed:
          - When entry `f x₁ ... xₖ := fdef` exists in the instance cache and `fdef := fₙ` is in the recursive function map.
               - return `optimizeApp fₙ xₖ₊₁ ... xₙ`
          - when no entry for `f x₁ ... xₖ` exists in the instance cache:
             - fbody' ← optimizeExpr sOpts `(λ p₁ ... pₙ → fbody[f/_recFun]) x₁ ... xₖ`
             - entry `f x₁ ... xₖ := fbody` is added to the instance cache
             - return `optimizeApp fₙ xₖ₊₁ ... xₙ` IF entry `fbody' := fₙ` exists in recursive function map and `f` is not an opaque function
             - return `optimizeApp f x₁ ... xₙ` IF entry `fbody' := fₙ` exists in recursive function map and `f` is an opaque function, with:
                  - `fbody' := f x₁ ... xₖ` added to the replay recursive function map,
             - return `optimizeApp f x₁ ... xₙ`  OTHERWISE, with:
                   - `fbody' := f x₁ ... xₖ` added to the recursive function map,
          where `x₁ ... xₖ` correspond to the implicit arguments of `f` (if any).
      - when `f` is not a recursive definition or is already in the recursive visited cache.
         - return optimizeApp `f x₁ ... xₙ`.
  -/
  partial def normOpaqueAndRecFun (sOpts: SolverOptions) (f : Expr) (args: Array Expr) : TranslateEnvT Expr := do
   match f with
   | Expr.const n l =>
       let isOpaque := isOpaqueFun n args
       if (← isRecursiveFun n)
       then
         -- retrieve implicit arguments
         let iargs ← getImplicitArgs f args
         let instApp ← mkAppExpr f iargs
         if (← isVisitedRecFun instApp)
         then optimizeApp f args -- already cached
         else
           if let some r ← hasRecFunInst? instApp isOpaque then return (← optimizeApp r args[iargs.size : args.size])
           cacheFunName instApp -- cache function name
           let some eqThm ← getUnfoldEqnFor? n | throwError "normOpaqueAndRecFun: equation theorem expected for {n}"
           let fn' ←
             forallTelescopeReducing ((← getConstInfo eqThm).type) fun xs eqn => do
               let some (_, _, fbody) := eqn.eq? | throwError "normOpaqueAndRecFun: equation expected but got {reprStr eqn}"
               let auxApp ← mkLambdaFVars xs fbody
               -- instantiating polymorphic parameters in fun body
               let fdef ← generalizeRecCall n l iargs (Expr.beta auxApp iargs)
               -- optimize recursive fun definition and store
               storeRecFunDef instApp (← optimizeExpr sOpts fdef) isOpaque
           -- only considering explicit args when instantiating
           -- as storeRecFunDef already handled implicit arguments
           optimizeApp fn' args[iargs.size : args.size] -- optimizations on cached opaque recursive functions
         else optimizeApp f args -- optimizations on opaque functions
   | _ => mkAppExpr f args


  /-- A generic match expression rewriter that given a `match` application expression `f args`
      apply the `rewriter` function on each match pattern. The `rewriter` function
      is applied from the last match pattern to the first one.
      Concretely, given a match expression of the form:
        match e₁, ..., eₙ with
        | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁
        ...
        | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ

     `matchExprRewriter` return the following evaluation:
       rewriter m-1 [e₁, ..., eₙ] [p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎] t₁
         ...
         (rewriter 1 [e₁, ..., eₙ] [p₍ₘ₋₁₎₍₁₎, ..., p₍ₘ₋₁₎₍ₙ₎] tₘ₋₁
           (rewriter 0 [e₁, ..., eₙ] [p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎] tₘ none))
     where,
       - the first application is passed the `none` accumulator
       - the `Nat` argument corresponding to the traversed index, starting with 0.
     NOTE: The evaluation stops when at least one of the `rewriter` invocation return `none`.
  -/
  partial def matchExprRewriter
    (sOpts: SolverOptions)
    (f : Expr) (args : Array Expr)
    (rewriter : Nat → Array Expr → Array Expr → Expr → Option α → TranslateEnvT (Option α))
    : TranslateEnvT (Option α) := do
  match f with
    | Expr.const n dlevel =>
        let some matcherInfo ← getMatcherInfo? n | return none
        let cInfo ← getConstInfo n
        let discrs := args[matcherInfo.getFirstDiscrPos : matcherInfo.getFirstAltPos]
        let rhs := args[matcherInfo.getFirstAltPos : matcherInfo.arity]
        let matchFun ← instantiateValueLevelParams cInfo dlevel
        let auxApp := Expr.beta matchFun args[0 : matcherInfo.getFirstAltPos]
        let auxAppType ← inferType auxApp
        forallTelescope auxAppType fun xs _t => do
          let alts := xs[xs.size - rhs.size:]
          let mut accExpr := (none : Option α)
          -- traverse in reverse order to handle last pattern first
          let nbAlts := alts.size
          for i in [:nbAlts] do
            let idx := nbAlts - i - 1
            accExpr ←
              forallTelescope (← inferType alts[idx]!) fun _xs b => do
                let mut lhs := b.getAppArgs
                -- NOTE: lhs has not been normalized as is kept at the type level.
                -- NOTE: optimizing lhs removes annotated named pattern, e.g.,
                --       ((namedPattern Nat p) (Nat.succ n)) is reduced to (Nat.succ n)
                -- normalizing lhs
                for j in [:lhs.size] do
                  lhs ← lhs.modifyM j (optimizeExpr sOpts)
                rewriter i discrs lhs rhs[idx]! accExpr
            unless (accExpr.isSome) do return accExpr -- break if accExpr is still none
          return accExpr
    | _ => pure none

end

/-- Optimize an expression using the given solver options.
    ### Parameters
      - `sOpts`: The solver options to use for optimization.
      - `expr`: The expression to be optimized.
    ### Returns
      - A tuple containing the optimized expression and the translation environment.
    NOTE: optimization is repeated until no entry is introduced in `replayRecFunMap`.
-/
partial def optimize (sOpts: SolverOptions) (e : Expr) : MetaM (Expr × TranslateEnv) := do
  let rec loop (e : Expr) (env : TranslateEnv) : MetaM (Expr × TranslateEnv) := do
    let res@(e', env') ← optimizeExpr sOpts e|>.run env
    if env'.replayRecFunMap.isEmpty
    then return res
    else loop e' (← restartTranslateEnv env').2
  loop e default

end Solver.Optimize
