import Lean
import Blaster.BlastResults
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
    let opts := stx[1].getArgs
    let sOpts ← parseSolveOptions opts default
    -- Capture original goal type for display before hypotheses are reverted.
    let origGoalType ← (← getMainGoal).getType
    let goal ← revertHypotheses (← getMainGoal)
    -- Gather theorem identity from the enclosing declaration.
    let declName? ← Lean.Elab.Term.getDeclName?
    let name    := declName?.map (·.toString) |>.getD "anonymous"
    let modName := (← getEnv).mainModule.toString
    let fm ← getFileMap
    let line := stx.getPos?.map (fm.toPosition ·) |>.map (·.line) |>.getD 0
    let docStr? : Option String ← do
      match declName? with
      | none => pure none
      | some n =>
        let fromEnv ← findDocString? (← getEnv) n
        match fromEnv with
        | some s => pure (some s)
        | none =>
          -- The current declaration isn't in the env yet while it elaborates.
          -- Scan the source text before this tactic call for the last /-- ... -/ block.
          let textBefore := fm.source.extract ⟨0⟩ (stx.getPos?.getD ⟨0⟩)
          let startParts := textBefore.splitOn "/--"
          if startParts.length < 2 then pure none
          else
            let endParts := startParts.getLast!.splitOn "-/"
            pure (endParts.head?.map String.trim)
    let desc    := docStr?.getD name
    let declStr := s!"theorem {name} : {← ppExpr origGoalType}"
    let startRec : Blaster.BlastResults.StartRecord :=
      { name, desc, decl := declStr, moduleName := modName, line }
    let startMs ← IO.monoMsNow
    (Blaster.BlastResults.writeStart startRec).catchExceptions fun _ => pure ()
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    let resultPair ← try
      let ((result, optExpr), _) ←
        withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
          IO.setNumHeartbeats 0
          Translate.main (← goal.getType) (logUndetermined := false) |>.run env
      let endMs ← IO.monoMsNow
      let (status, cex) := match result with
        | .Valid         => ("proved",       [])
        | .Falsified cex => ("falsified",    cex)
        | .Undetermined  => ("undetermined", [])
      let endRec : Blaster.BlastResults.EndRecord :=
        { name, status, time_ms := endMs - startMs, cex }
      (Blaster.BlastResults.writeEnd endRec modName).catchExceptions fun _ => pure ()
      pure (result, optExpr)
    catch ex =>
      let endMs ← IO.monoMsNow
      let endRec : Blaster.BlastResults.EndRecord :=
        { name, status := "error", time_ms := endMs - startMs, cex := [] }
      (Blaster.BlastResults.writeEnd endRec modName).catchExceptions fun _ => pure ()
      throw ex
    let (result, optExpr) := resultPair
    -- Original result-handling logic unchanged.
    match result with
    | .Valid       => goal.admit -- TODO: replace with proof reconstruction
    | .Falsified _ => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
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
