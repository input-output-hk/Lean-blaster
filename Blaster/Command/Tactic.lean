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


@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts default
   let (goal, nbQuantifiers) ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let ((result, optExpr), _) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType >>= instantiateMVars') (logUndetermined := false) |>.run env
   match result with
   | .Valid => goal.admit -- TODO: replace with proof reconstruction
   | .Falsified cex => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
   | .Undetermined =>
        -- Replace the goal with the optimized expression
        let newGoal ← goal.replaceTargetDefEq optExpr
        -- reintroduce reverted quantifiers
        let currQuantifiers ← getFirstNbQuantifiers optExpr
        let (_, newGoal') ← newGoal.introNP (max currQuantifiers nbQuantifiers)
        replaceMainGoal [newGoal']

  where
    getFirstNbQuantifiers (e : Expr) : MetaM Nat := do
      forallTelescope e fun fvars _ => do
        let mut nb := 0
        for v in fvars do
          if !(← isProp (← v.fvarId!.getType)) then
            nb := nb + 1
        return nb

    @[always_inline, inline]
    instantiateMVars' (e : Expr) : TacticM Expr :=
     if e.hasMVar then instantiateMVars e else return e

    @[always_inline, inline]
    revertHypotheses (goal : MVarId) : TacticM (MVarId × Nat) :=
      goal.withContext $ do
        -- Get all hypotheses from the local context
        let lctx ← getLCtx
        let mut hyps := #[]
        let mut nbQuantifiers := 0
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let declType ← instantiateMVars' decl.type
          if !(← isProp declType) then
            nbQuantifiers := nbQuantifiers + 1
          hyps := hyps.push decl.fvarId
        -- revert hyp from context
        let goal' ←
          hyps.foldrM
          (fun h g => do
             let (_, g) ← g.revert #[h]
             return g) goal
        return (goal', nbQuantifiers)


end Blaster.Tactic
