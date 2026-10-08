import Blaster.Command.Tactic
import Blaster.Proof.Summary
import Blaster.Proof.Verification.Solver
import Blaster.Proof.Verification.Local
import Blaster.Proof.Induction
import Blaster.Proof.Explore.Frontend
import Blaster.Proof.Export

/-!
# Summaries and automatic induction for `blaster`

Two options extend the ordinary `blaster` tactic:

* `(summaries: [t₁, …])`: proved facts, instantiated at the calls of the goal
  before the SMT query. Only the instances are added; nothing is assumed.
* `(induction: auto)`: prove a statement about a recursive program, either by
  symbolic exploration of a machine run with inferred invariants
  (`Explore.Frontend`) or by checked functional induction (`Induction.run`).

This elaborator handles only invocations that use one of these options; every
other `blaster` call is left to the ordinary tactic.
-/

namespace Blaster.Proof.Tactic
open Lean Elab Tactic Meta Blaster.Options Blaster.Syntax

syntax "(summaries:" "[" term,* "]" ")" : solveOption
syntax "(induction:" "auto" ")" : solveOption

/-- `x`, or `h` when `x` is interrupted (the cancel token of a wall-clock cap).
The elaboration monads never catch an interrupt with `try`, so this catches it
in the underlying `EIO`. -/
def onInterrupt (x h : TermElabM α) : TermElabM α :=
  fun c1 r1 c2 r2 c3 r3 =>
    tryCatch (x c1 r1 c2 r2 c3 r3) fun ex =>
      if ex.isInterrupt then h c1 r1 c2 r2 c3 r3 else throw ex

/-- A replay condition often needs only arithmetic between observations already
present in its hypotheses. Prove the stronger statement with recursive calls
replaced by arbitrary values, then instantiate those values with the real calls.
No equations or recursive behavior are assumed by this fast path. -/
private def proveObservationCondition (target : Expr) (expose : Bool := false) : TermElabM Expr :=
  forallTelescope target fun xs body => do
    let hypotheses ← xs.filterM fun x => do isProp (← inferType x)
    let implication ← mkForallFVars hypotheses body
    let discovery ← Induction.Source.discover implication.getUsedConstants
    if expose then
      -- Keep one symbol for a recursive function, including calls underneath
      -- match alternatives. Wrapper unfolding and constructor equations are
      -- definitional reductions; arbitrary recursive behavior stays opaque.
      let implication ← Induction.Source.expose discovery implication true
      let discovery ← Induction.Source.discover implication.getUsedConstants
      let proof ← Optimize.withUninterpretedRecursion discovery.recursive <|
        Verification.Solver.prove implication {timeout := some 2, generateCex := false}
      return ← mkLambdaFVars xs (mkAppN proof hypotheses)
    let observedNames := discovery.recursive
    let functions ← IO.mkRef (#[] : Array Expr)
    implication.forEach fun e => do
      if let .const n _ := e then
        if observedNames.contains n then functions.modify (·.push e)
    let functions := (Std.HashSet.ofArray (← functions.get)).toArray
    if functions.isEmpty then throwError "no observations to abstract"
    let proof ← Verification.Local.abstractApplications implication functions
      (fun abstracted => Verification.Local.solveConnected abstracted fun connected =>
        Verification.Solver.prove connected {timeout := some 1, generateCex := false})
    mkLambdaFVars xs (mkAppN proof hypotheses)

/-- Prove an observation condition after substituting its constructor
equations (`subst_vars`), with its recursive calls abstracted
(`proveAbstractObservationCondition`). -/
private def proveNormalizedObservationCondition (target : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar target
  let goals ← Tactic.run mvar.mvarId! <| Term.withoutErrToSorry do
    -- Make constructor values visible before keeping recursion opaque. For
    -- example, `xs = []` must reduce a recursive sum at xs to its base case.
    evalTactic (← `(tactic| intros; subst_vars))
    unless (← getGoals).isEmpty do
      withMainContext do
        let goal ← getMainGoal
        let xs := (← getLCtx).foldl (init := #[]) fun acc d =>
          if d.isImplementationDetail then acc else acc.push d.toExpr
        let closed ← mkForallFVars xs (← goal.getType)
        let proof ← proveObservationCondition closed true
        goal.assign (mkAppN proof xs)
        setGoals []
  unless goals.isEmpty do throwError "open normalized observation goals"
  return ← instantiateMVars mvar

/-- A fact prover for the explorer: `blaster`, or automatic induction, on
`target` with `facts` as summaries, under a wall-clock cap. `plainFirst` tries
the observation fast paths and plain `blaster` before induction. The messages
of these inner proofs are discarded; the caller reports the result. -/
private def proveExplorerFact (timeout maxGoals : Nat) (plainFirst : Bool)
    (facts : Array Expr) (target : Expr) : TermElabM (Option Expr) := do
  let messages := (← getThe Core.State).messages
  let names := facts.filterMap fun f => f.constName?
  -- a hard wall-clock cap: the per-goal solver timeout multiplies over the
  -- induction front end's goals
  let wall := timeout * 3000 + 2000
  let tk ← IO.CancelToken.new
  -- the caller's cancellation (an edit in the editor) stops the proof too
  let outer := (← readThe Core.Context).cancelTk?
  let cancelled : BaseIO Bool := match outer with
    | some t => t.isSet
    | none => pure false
  -- the timer on its own thread (a pool worker asleep for the whole cap
  -- starves the parallel provers), leaving as soon as the proof is done
  let done ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    let mut left := wall
    while left > 0 && !(← done.get) && !(← cancelled) do
      IO.sleep 100
      left := left - min left 100
    unless ← done.get do tk.set
  -- (no exploration inside: these are first-order facts about the observers)
  -- (nor an export: they are parts of the proof being exported)
  let options := fun (o : Options) => o.setNat `blaster.induction.maxGoals maxGoals
    |>.setNat `maxRecDepth 20000 |>.setBool `blaster.explore.enabled false
    |>.setString `blaster.induction.export ""
  let r ← withOptions options <| withLCtx {} {} do
    let saved ← Term.saveState
    onInterrupt (h := do
        if ← cancelled then throwInterruptException
        saved.restore
        pure none) <|
      withTheReader Core.Context (fun c => {c with cancelTk? := some tk}) <|
    try
      if plainFirst then
        for expose in #[false, true] do
          let fastState ← Term.saveState
          try
            let proof ← if expose then proveNormalizedObservationCondition target
              else proveObservationCondition target
            if proof.hasMVar || proof.hasFVar || proof.hasSorry then throwError "incomplete observation proof"
            return some proof
          catch ex =>
            if ex.isInterrupt then throw ex
            fastState.restore
      let mvar ← mkFreshExprMVar target
      let t := Lean.Syntax.mkNumLit (toString timeout)
      let ids ← names.mapM fun n => Term.exprToSyntax (mkConst n)
      let gs ← Tactic.run mvar.mvarId! <| Term.withoutErrToSorry do
        -- a verification condition is usually first-order: plain translation
        -- first, the induction front end only when that fails
        if plainFirst && names.isEmpty then
          evalTactic (← `(tactic| first
            | blaster (timeout: $t) (gen-cex: 0)
            | blaster (induction: auto) (timeout: $t) (gen-cex: 0)))
        else if names.isEmpty then
          evalTactic (← `(tactic| blaster (induction: auto) (timeout: $t) (gen-cex: 0)))
        else if plainFirst then
          evalTactic (← `(tactic| first
            | blaster (timeout: $t) (gen-cex: 0)
            | blaster (induction: auto) (summaries: [$ids,*]) (timeout: $t) (gen-cex: 0)))
        else
          evalTactic (← `(tactic| blaster (induction: auto) (summaries: [$ids,*]) (timeout: $t) (gen-cex: 0)))
      unless gs.isEmpty do throwError "open goals"
      let pr ← instantiateMVars mvar
      if pr.hasMVar || pr.hasFVar || pr.hasSorry then throwError "incomplete"
      pure (some pr)
    catch _ =>
      saved.restore
      pure none
  done.set true
  modifyThe Core.State fun s => {s with messages}
  return r

/-- Elaborate a supplied summary: a constant or an arbitrary proof term. -/
private def elabSummary (term : Term) : TacticM Expr :=
  if term.raw.isIdent then elabTermForApply term (mayPostpone := false)
  else Term.elabTermAndSynthesize term none

/-- `blaster` with `(summaries: …)` or `(induction: auto)` (see the module
documentation); any other invocation goes to the ordinary tactic. With
`(induction: auto)` the goal is proved by exploration when it is about a
machine run, otherwise by functional induction, and the proof is exported
when `blaster.induction.export` is set. -/
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
      let start ← getEnv
      let canExplore := !sOpts.onlyOptimize && !sOpts.onlySmtLib && sOpts.solveResult == .ExpectedValid
      let replays ← try
        -- the explorer's provers: observer facts, links between observers, a
        -- quick first attempt at each verification condition, and the full one
        let explored ← if canExplore then
          Explore.Frontend.run? summaries
            (proveExplorerFact 1 6 false) (proveExplorerFact 3 8 false)
            (proveExplorerFact 1 1 true)
            (proveExplorerFact (sOpts.timeout.getD 10) 8 true)
          else pure none
        if explored.isNone then Induction.run summaries sOpts
        pure (explored.getD #[])
      catch ex =>
        if ex.isInterrupt then throw ex
        -- A failure is final: Lean would otherwise retry the invocation with
        -- the ordinary `blaster` elaborator, which ignores these options.
        logException ex
        throwAbortCommand
      let proof ← instantiateMVars (mkMVar originalGoal)
      if proof.getUsedConstants.contains ``Blaster.Tactic.blasterProven &&
          (← getOptions).getBool `warn.sorry true then
        logWarningAt stx "declaration uses 'blasterProven' (SMT-verified, no proof term)"
      -- (a failed export is reported; the proof stands)
      try Export.exportProof originalGoal proof start replays stx
      catch ex =>
        if ex.isInterrupt then throw ex
        logException ex
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
