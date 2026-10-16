import Blaster.Command.Tactic
import Blaster.Proof.Summary
import Blaster.Proof.Verification.Solver
import Blaster.Proof.Verification.Local
import Blaster.Proof.Induction

namespace Blaster.Proof.Tactic
open Lean Elab Tactic Meta Blaster.Options Blaster.Syntax

syntax "(summaries:" "[" term,* "]" ")" : solveOption
syntax "(induction:" "auto" ")" : solveOption

/-- Elaborate a supplied summary: a constant or an arbitrary proof term. -/
private def elabSummary (term : Term) : TacticM Expr :=
  if term.raw.isIdent then elabTermForApply term (mayPostpone := false)
  else Term.elabTermAndSynthesize term none

/-- Instantiate summaries or apply checked functional induction. -/
@[tactic Blaster.Tactic.blasterTactic]
def elabBlaster : Tactic := fun stx =>
  withMainContext do
    let mut sOpts : BlasterOptions := default
    let mut plain : Array (TSyntax `solveOption) := #[]
    let mut summaryTerms : Array Term := #[]
    let mut induction := false
    for option in stx[1].getArgs do
      match option with
      | `(solveOption| (summaries: [$terms:term,*])) => summaryTerms := summaryTerms ++ terms.getElems
      | `(solveOption| (induction: auto)) => induction := true
      | _ =>
        plain := plain.push ⟨option⟩
        sOpts ← parseSolveOption sOpts ⟨option⟩
    -- the ordinary tactic handles every other invocation
    unless induction || !summaryTerms.isEmpty do throwUnsupportedSyntax
    if induction then
      let summaries ← summaryTerms.mapM elabSummary
      let originalGoal ← getMainGoal
      try
        Induction.run summaries sOpts
      catch ex =>
        if ex.isInterrupt then throw ex
        logException ex
        throwAbortCommand
      let proof ← instantiateMVars (mkMVar originalGoal)
      if proof.getUsedConstants.contains ``Blaster.Tactic.blasterProven &&
          (← getOptions).getBool `warn.sorry true then
        logWarningAt stx "declaration uses 'blasterProven' (SMT-verified, no proof term)"
      return
    -- summaries: add their instances at the calls of the goal, then solve as usual
    let (_, introduced) ← (← getMainGoal).intros
    replaceMainGoal [introduced]
    introduced.withContext do
      let summaries ← summaryTerms.mapM elabSummary
      let facts ← Summary.instantiate introduced summaries
      if facts.isEmpty then
        throwError "blaster: no summary matched an existing call; introduce binders or specialize the supplied summaries"
      let mut enriched := introduced
      for fact in facts do
        let (_, next) ← enriched.note (← mkFreshUserName `summary) fact
        enriched := next
      -- Instantiated proofs have already been applied outside the remaining
      -- goal. Do not also send a selected local universal summary to SMT.
      for summary in summaries do
        if summary.isFVar then
          enriched ← enriched.tryClear summary.fvarId!
      replaceMainGoal [enriched]
      if sOpts.verbose > 0 then logInfo m!"Blaster: instantiated {facts.size} local summary facts"
    evalTactic (← `(tactic| blaster $plain*))

end Blaster.Proof.Tactic
