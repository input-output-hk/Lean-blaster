import Lean
import Blaster.Command.Syntax
import Blaster.Smt.Translate
import Blaster.Optimize
import Blaster.Logging.Basic

open Lean Elab Tactic Meta
open Blaster.Optimize Blaster.Smt Blaster.Options Blaster.Syntax

namespace Blaster.Tactic

/--
`blaster` is an SMT-based tactic that automatically proves goals using Z3.

Options:
  - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
  - `verbose:` activating debug info (default: 0)
  - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
  - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
  - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
  - `gen-cex`: generate counterexample for falsified theorems (default: 1)
  - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
  - `random-seed`: seed for the random number generator (default: none)
  - `solve-result`: specify the expected result from the blaster tactic, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)
Example: `blaster (timeout: 10) (verbose: 1)`
-/
syntax (name := blasterTactic) "blaster" (solveOption)* : tactic

/-- Convert core Nat operators to their HAdd/HSub/HMul elaborated form
    so that proof term LHS patterns structurally match goal expressions. -/
def toElabForm (e : Expr) : MetaM Expr := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) a) b =>
      mkAdd (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) a) b =>
      mkSub (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) a) b =>
      mkMul (← toElabForm a) (← toElabForm b)
  | Expr.app f a =>
      return mkApp (← toElabForm f) (← toElabForm a)
  | _ => return e

/-- Replace optimizer-context FVarIds with goal-context FVarIds in proof steps. -/
def substProofStackFVars (steps : Array Blaster.Optimize.ProofStep)
    (optBinders goalFVarIds : Array FVarId) : Array Blaster.Optimize.ProofStep :=
  if optBinders.isEmpty then steps
  else
    let n := min optBinders.size goalFVarIds.size
    let from_ := (optBinders[:n].toArray).map mkFVar
    let to_ := (goalFVarIds[:n].toArray).map mkFVar
    steps.map fun
      | .rewrite proof symm  => .rewrite (proof.replaceFVars from_ to_) symm
      | .exact proof => .exact (proof.replaceFVars from_ to_)

/-- Apply recorded proof stack rewrites to a goal.
    Each rewrite step is attempted; steps that don't match are skipped.
-/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep) : MetaM MVarId := do
  -- normalize proof terms once upfront
  let steps : Array Blaster.Optimize.ProofStep ← goal.withContext <| steps.mapM fun
    | .rewrite proof symm => return .rewrite (← toElabForm proof) symm
    | .exact proof => return .exact proof
  /- trace[Optimize.expr] "proofStack size: {steps.size}" -/
  /- trace[Optimize.expr] "proofStack: -/
  /-   {reprStr $ Array.map (λ | .rewrite proof _ => proof | .exact proof => proof) steps}" -/
  let mut g := goal
  let mut changed := true
  while changed do
    changed := false
    for step in steps do
      match step with
      | .rewrite heq symm =>
        try
          let r ← g.rewrite (← g.getType) heq symm
          g ← g.replaceTargetEq r.eNew r.eqProof
          changed := true
        catch _ => pure ()
      | .exact proof =>
        try
          g.assign proof
          return g
        catch _ => pure ()
  /- trace[Optimize.expr] "final goal after proofStack: {← g.getType}" -/
  return g

/-- Given a proof `h : ∀ x₁ ... xₙ, P x₁...xₙ = Q x₁...xₙ`, produce a proof of
    `(∀ x₁ ... xₙ, P x₁...xₙ) = (∀ x₁ ... xₙ, Q x₁...xₙ)`.
    When `lhs` and `rhs` are not both foralls, returns `h` unchanged. -/
partial def liftForallEq (lhs rhs h : Expr) : MetaM Expr := do
  match lhs, rhs with
  | Expr.forallE n α lhsBody bi, Expr.forallE _ _ rhsBody _ =>
    let forward ← withLocalDecl `hp .default lhs fun hp =>
      withLocalDecl n bi α fun x => do
        let innerEq ← liftForallEq (lhsBody.instantiate1 x) (rhsBody.instantiate1 x) (mkApp h x)
        let body ← mkAppM ``cast #[innerEq, mkApp hp x]
        let lam ← mkLambdaFVars #[x] body
        mkLambdaFVars #[hp] lam
    let backward ← withLocalDecl `hq .default rhs fun hq =>
      withLocalDecl n bi α fun x => do
        let innerEq ← liftForallEq (lhsBody.instantiate1 x) (rhsBody.instantiate1 x) (mkApp h x)
        let symmEq ← mkAppM ``Eq.symm #[innerEq]
        let body ← mkAppM ``cast #[symmEq, mkApp hq x]
        let lam ← mkLambdaFVars #[x] body
        mkLambdaFVars #[hq] lam
    let iff ← mkAppM ``Iff.intro #[forward, backward]
    mkAppM ``propext #[iff]
  | _, _ => return h

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts default
   let goal ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let ((result, optExpr), finalEnv) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType) (logUndetermined := false) |>.run env
   match result with
   | .Valid =>
        let goalType ← goal.getType
        -- Try propositional equality path: (∀ xs, body₁) = (∀ xs, body₂)
        let usedPropEqPath ← try
          match goalType.eq? with
          | some (_, lhs, rhs) =>
            if ← isProp lhs then
              let numBinders ← forallTelescope lhs fun fvars _ => pure fvars.size
              if numBinders > 0 then
                -- Build pointwise equality goal: ∀ xs, body₁(xs) = body₂(xs)
                let innerGoalType ← forallTelescope lhs fun inputFvars inputBody => do
                  let optBody ← forallBoundedTelescope rhs (some numBinders) fun optFvars optBody =>
                    pure (optBody.replaceFVars optFvars inputFvars)
                  let eq ← mkEq inputBody optBody
                  mkForallFVars inputFvars eq
                let innerMVar ← mkFreshExprMVar innerGoalType
                let (goalFVarIds, ig) ← innerMVar.mvarId!.introNP numBinders
                let proofStack := substProofStackFVars finalEnv.optEnv.proofStack
                                    finalEnv.optEnv.optBinders goalFVarIds
                let ig ← applyProofStack ig proofStack
                try ig.refl
                catch _ => ig.admit
                -- Lift: (∀ xs, body₁ = body₂) → (∀ xs, body₁) = (∀ xs, body₂)
                let liftedProof ← liftForallEq lhs rhs innerMVar
                goal.assign liftedProof
                pure true
              else pure false
            else pure false
          | none => pure false
        catch _ => pure false
        unless usedPropEqPath do
          -- intro all binders, rewrite, refl
          let numBinders ← forallTelescope goalType fun fvars _ => pure fvars.size
          let (goalFVarIds, g) ← goal.introNP numBinders
          let proofStack := substProofStackFVars finalEnv.optEnv.proofStack
                              finalEnv.optEnv.optBinders goalFVarIds
          let g ← applyProofStack g proofStack
          unless ← g.isAssigned do
            try g.refl
            catch _ => g.admit
   | .Falsified cex => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
   | .Undetermined =>
        -- Replace the goal with the optimized expression
        let newGoal ← goal.replaceTargetDefEq optExpr
        replaceMainGoal [newGoal]

  where

    @[always_inline, inline]
    revertHypotheses (goal : MVarId) : TacticM MVarId :=
      goal.withContext $ do
        -- Get all hypotheses from the local context
        let lctx ← getLCtx
        let mut hyps := #[]
        for decl in lctx do
          if decl.isImplementationDetail then continue
          if ← isProp decl.type then
            hyps := hyps.push decl.fvarId
        -- revert hyp from context
        hyps.foldrM
          (fun h g => do
             let (_, g) ← g.revert #[h]
             return g) goal


end Blaster.Tactic
