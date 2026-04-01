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

/-- Apply recorded proof stack rewrites to a goal.
    Each rewrite step is attempted; steps that don't match are skipped.
-/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep) : MetaM MVarId := do
  -- normalize proof terms once upfront
  let steps : Array Blaster.Optimize.ProofStep ← goal.withContext <| steps.mapM fun
    | .rewrite proof symm => return .rewrite (← toElabForm proof) symm
  /- trace[Optimize.expr] "proofStack size: {steps.size}" -/
  /- trace[Optimize.expr] "proofStack: -/
  /-   {reprStr $ Array.map (λ | .rewrite proof _ => proof) steps}" -/
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
  /- trace[Optimize.expr] "final goal after proofStack: {← g.getType}" -/
  return g

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
        -- intro all binders so rewrite can find patterns
        let numBinders ← forallTelescope (← goal.getType) fun fvars _ => pure fvars.size
        let (goalFVarIds, g) ← goal.introNP numBinders
        let proofStack := substProofStackFVars finalEnv.optEnv.proofStack
                            finalEnv.optEnv.optBinders goalFVarIds
        let g ← applyProofStack g proofStack
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
