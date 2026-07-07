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
  - `solver`: select the backend SMT solver: `z3`, `cvc5`, `all` (run every solver, cross-check answers) or `any` (first definitive answer wins) (default: z3)
Example: `blaster (timeout: 10) (verbose: 1)`
-/
syntax (name := blasterTactic) "blaster" (solveOption)* : tactic


/-- Custom sorry for Blaster to differentiate
    between SMT-verified goals and regular `sorry`.-/
axiom blasterProven : ∀ {α : Sort u}, α

private def blasterAdmit (mvarId : MVarId) : MetaM Unit :=
  mvarId.withContext do
    mvarId.checkNotAssigned `blasterAdmit
    let mvarType ← mvarId.getType >>= instantiateMVars
    let u ← getLevel mvarType
    mvarId.assign (mkApp (mkConst ``blasterProven [u]) mvarType)

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts default
   let goal ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let t0 ← IO.monoMsNow
   let ((result, optExpr), fenv) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType) (logUndetermined := false) |>.run env
   -- performance report: total wall-clock of the whole call
   if sOpts.verbose ≥ 1 then
     logInfoAt stx s!"⏱ blaster total: {(← IO.monoMsNow) - t0}ms"
   -- pin-the-winner suggestion after a decisive `any` race
   if sOpts.solver == .any then
     if let some w := fenv.smtEnv.anyWinner then
       Blaster.Smt.suggestPinnedSolver stx w
   match result with
   | .Valid =>
      blasterAdmit goal
      if (← getOptions).getBool `warn.sorry true then
        logWarningAt stx "declaration uses 'blasterProven' (SMT-verified, no proof term)" -- TODO: replace with proof reconstruction

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
