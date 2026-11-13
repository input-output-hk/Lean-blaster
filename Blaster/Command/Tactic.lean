import Lean
import Blaster.Command.Syntax
import Blaster.Smt.Translate
import Blaster.Optimize
import Blaster.Logging.Basic
import Blaster.Reconstruct.Main

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
  - `reconstruct`: 0 for the existing behavior, 1 for best-effort Z3 proof replay,
                   2 to require a complete kernel-checked proof (default: 0)
  - `gen-proof`: require a proof using only Lean's standard axioms (default: 0)
  - `solve-result`: specify the expected result from the blaster tactic, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)
Example: `blaster (timeout: 10) (verbose: 1)`
-/
syntax (name := blasterTactic) "blaster" (solveOption)* : tactic

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts (← BlasterOptions.fromEnv)
   let goal ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let ((result, optExpr), finalEnv) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType) (logUndetermined := false) |>.run env
   let proofStack := finalEnv.optEnv.proofStack
   let optBinders := finalEnv.optEnv.optBinders
   match result with
   | .Valid =>
        -- `optExpr == True` ⟹ proved by rewriting (no SMT)
        let optimizerClosed := optExpr.isConstOf ``True
        if sOpts.reconstruct == 0 then
          goal.assign (← proveGoalByProofStack (← goal.getType) proofStack optBinders optimizerClosed)
        else
          let state ← saveState
          match ← Blaster.Reconstruct.reconstructGoal (← goal.getType) proofStack optBinders optimizerClosed sOpts with
          | .ok proof => goal.assign proof
          | .error msg =>
              state.restore
              if sOpts.reconstruct ≥ 2 then throwTacticEx `blaster goal msg
              logWarning m!"blaster: checked reconstruction failed: {msg}"
              goal.assign (← proveGoalByProofStack (← goal.getType) proofStack optBinders optimizerClosed)
   | .Falsified cex => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
   | .Undetermined =>
        let replace ← goal.withContext do
          return (← Blaster.Reconstruct.attempt 20 (do
            if ← withDefault <| isDefEq (← goal.getType) optExpr then return some ()
            return none)).isSome
        let newGoal ← if replace then goal.replaceTargetDefEq optExpr else pure goal
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
