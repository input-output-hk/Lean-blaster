import Lean
import Solver.Command.Syntax
import Solver.Smt.Translate
import Solver.Optimize
import Solver.Logging.Basic

open Lean Elab Tactic Meta
open Solver.Optimize Solver.Smt Solver.Options Solver.Syntax

namespace Solver.Tactic

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

/-! ### Helper Functions -/

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx => withMainContext do
  -- Parse options in any order
  let opts := stx[1].getArgs
  let sOpts ← parseSolveOptions opts default

  -- Get the current goal
  let goal ← getMainGoal

  -- Build the full goal including hypotheses as implications
  let fullGoal ← goal.withContext do
    let goalType ← goal.getType
    -- Get all hypotheses from the local context
    let lctx ← getLCtx
    let mut hyps := #[]
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let declType ← instantiateMVars decl.type
      if ← isProp declType then
        hyps := hyps.push decl.toExpr
    -- Build: h1 → h2 → ... → hn → goal
    mkForallFVars hyps goalType

  let env : TranslateEnv := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let ((result, optExpr), _) ← Translate.main fullGoal (logUndetermined := false) |>.run env

  match result with
  | .Valid =>
      -- TODO: replace with proper proof reconstruction
      -- Label sorry for goal splitting?
      let goalType ← goal.getType
      let sorryProof ← Lean.Meta.mkLabeledSorry goalType (synthetic := false) (unique := true)
      goal.assign sorryProof
      replaceMainGoal []

  | .Falsified cex =>
        throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"

  | .Undetermined =>
      -- Replace the goal with the optimized expression
      let goalType ← goal.getType
      let newGoal ← goal.replaceTargetEq optExpr (← mkEqRefl goalType)
      replaceMainGoal [newGoal]

end Solver.Tactic
