import Lean

/-! Finite, proof-producing instantiation of supplied summaries. This module
    knows nothing about evaluators or application domains. It never asserts a
    summary's preconditions and never unfolds a summarized function. -/
namespace Blaster.Proof.Summary
open Lean Meta

initialize registerTraceClass `Blaster.summary

register_option blaster.summary.maxInstances : Nat := {
  defValue := 256
  descr := "Maximum distinct local summary facts per Blaster invocation" }

register_option blaster.summary.maxMatches : Nat := {
  defValue := 4096
  descr := "Maximum same-head summary matching attempts per Blaster invocation" }

private structure Rule where
  proof : Expr
  type : Expr
  levels : Array Name
  /-- Lambda-abstracted patterns, in theorem-parameter order. -/
  patterns : Array (Name × Expr)
  ground : Bool

/-- Collect complete constant-headed applications without opening binders.
    Bound-dependent calls cannot be instantiated in the outer proof context. -/
private partial def calls (expression : Expr) : Array Expr := Id.run do
  let mut result := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo := #[expression]
  while !todo.isEmpty do
    let current := todo.back!
    todo := todo.pop
    if seen.contains current then continue
    seen := seen.insert current
    match current with
    | .app .. =>
      if current.getAppFn.isConst && !current.hasLooseBVars && !current.hasMVar then
        result := result.push current
      todo := todo ++ current.getAppArgs
      if !current.getAppFn.isConst then todo := todo.push current.getAppFn
    | .forallE _ domain body _ | .lam _ domain body _ =>
      todo := todo.push domain |>.push body
    | .letE _ type value body _ => todo := todo.push type |>.push value |>.push body
    | .mdata _ body | .proj _ _ body => todo := todo.push body
    | _ => pure ()
  return result

private def checkProof (proof : Expr) : MetaM Unit := do
  if proof.hasMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "blaster summary must be a fully elaborated proof without sorry"
  unless ← isProp (← inferType proof) do
    throwError "blaster summary must be a proof, not a proposition or function returning data"

private def compile (proof : Expr) : MetaM Rule := do
  if proof.hasExprMVar then
    throwError "blaster summary has unresolved arguments; explicitly specialize its implicit parameters"
  let abstracted ← abstractMVars proof
  let proof := abstracted.expr
  let levels := abstracted.paramNames
  checkProof proof
  let type ← inferType proof
  forallTelescopeReducing type fun parameters body => do
    let mut values := #[]
    let mut expressions := #[body]
    for parameter in parameters do
      let parameterType ← inferType parameter
      if ← isProp parameterType then
        expressions := expressions.push parameterType
      else
        values := values.push parameter
    if values.isEmpty then
      unless levels.isEmpty do
        throwError "blaster summary has undetermined universes; explicitly specialize it"
      return {proof, type, levels, patterns := #[], ground := true}
    let mut patterns := #[]
    let mut seen : Std.HashSet Expr := {}
    for expression in expressions do
      for candidate in calls expression do
        if seen.contains candidate then continue
        seen := seen.insert candidate
        if ← isProp candidate then continue
        unless values.all (fun parameter => candidate.containsFVar parameter.fvarId!) do
          continue
        patterns := patterns.push (candidate.getAppFn.constName!, ← mkLambdaFVars parameters candidate)
    if patterns.isEmpty then
      throwError "blaster summary has no first-order call determining all value parameters; partially apply observation parameters or supply a more specific summary: {type}"
    return {proof, type, levels, patterns, ground := false}

/-- Syntactic call matching, with typed assignment only at pattern variables.
    In particular, defeq must not unfold a recursive head to find a match. -/
private partial def matchCall (pattern actual : Expr) : MetaM Bool := do
  let pattern ← instantiateMVars pattern
  match pattern, actual with
  | .mvar .., _ => withTransparency .reducible <| isDefEq pattern actual
  | .app pf pa, .app af aa =>
    return (← matchCall pf af) && (← matchCall pa aa)
  | .const pn _, .const an _ =>
    if pn != an then return false
    withTransparency .reducible <| isDefEq pattern actual
  | .mdata _ p, a => matchCall p a
  | p, .mdata _ a => matchCall p a
  | _, _ => return pattern == actual

private def instantiateAt (rule : Rule) (pattern candidate : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let universes ← rule.levels.mapM fun _ => mkFreshLevelMVar
    let source := rule.proof.instantiateLevelParamsArray rule.levels universes
    let type := rule.type.instantiateLevelParamsArray rule.levels universes
    let pattern := pattern.instantiateLevelParamsArray rule.levels universes
    let (parameters, _, _) ← forallMetaTelescopeReducing type
    unless ← matchCall (pattern.beta parameters) candidate do return none
    for parameter in parameters do
      if (← instantiateMVars parameter).hasMVar && !(← isProp (← inferType parameter)) then
        return none
    -- Any unfilled proof arguments remain hypotheses of the instantiated
    -- theorem. They are never silently assumed or replaced with sorry.
    let rec close (remaining : List Expr) (premises : Array Expr) : MetaM Expr := do
      match remaining with
      | [] => mkLambdaFVars premises (← instantiateMVars (mkAppN source parameters))
      | parameter :: rest =>
        let actual ← instantiateMVars parameter
        if actual.hasMVar then
          let type ← instantiateMVars (← inferType parameter)
          withLocalDeclD `summaryPremise type fun premise => do
            parameter.mvarId!.assign premise
            close rest (premises.push premise)
        else close rest premises
    let proof ← close parameters.toList #[]
    if proof.hasMVar || proof.hasLooseBVars then return none
    check proof
    return some proof
  finally saved.restore

/-- Derive facts at calls already present in the goal/context. The call set is
    frozen: new facts do not recursively seed more matching or unfolding.
    Missing instances only reduce proving power, never strengthen assumptions. -/
def instantiate (goal : MVarId) (summaries : Array Expr) : MetaM (Array Expr) :=
  goal.withContext do
    let rules ← summaries.mapM compile
    let mut expressions := #[← goal.getType]
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        expressions := expressions.push declaration.type
        if !(← isProp declaration.type) then
          if let some value := declaration.value? then expressions := expressions.push value
    let mut indexed : Std.HashMap Name (Array Expr) := {}
    let mut seen : Std.HashSet Expr := {}
    for expression in expressions do
      for candidate in calls expression do
        unless seen.contains candidate do
          seen := seen.insert candidate
          let name := candidate.getAppFn.constName!
          indexed := indexed.insert name ((indexed[name]?).getD #[] |>.push candidate)
    let maxInstances := blaster.summary.maxInstances.get (← getOptions)
    let maxMatches := blaster.summary.maxMatches.get (← getOptions)
    let mut facts := #[]
    let mut factTypes : Std.HashSet Expr := {}
    let mut attempts := 0
    for rule in rules do
      let mut instances := if rule.ground then #[rule.proof] else #[]
      for (head, pattern) in rule.patterns do
        for candidate in (indexed[head]?).getD #[] do
          attempts := attempts + 1
          if attempts > maxMatches then
            throwError "blaster summary matching limit reached ({maxMatches}); specialize the supplied summaries or raise blaster.summary.maxMatches"
          if let some proof ← instantiateAt rule pattern candidate then
            instances := instances.push proof
      for proof in instances do
        let type ← inferType proof
        if factTypes.contains type then continue
        if facts.size >= maxInstances then
          throwError "blaster summary instance limit reached ({maxInstances}); specialize the supplied summaries or raise blaster.summary.maxInstances"
        factTypes := factTypes.insert type
        facts := facts.push proof
        trace[Blaster.summary] "instantiated: {type}"
    trace[Blaster.summary] "{facts.size} facts from {attempts} matching attempts"
    return facts

end Blaster.Proof.Summary
