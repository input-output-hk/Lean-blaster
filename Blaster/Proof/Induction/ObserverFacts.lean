import Blaster.Proof.Induction.Source

/-! Bounded discovery of ordinary relations between scalar observations.
Candidates are not assumptions. A separate prover must construct a closed
proof, which is kernel-checked before it can become a law.
No execution postcondition, source point, or application annotation is input.
-/
namespace Blaster.Proof.Induction.ObserverFacts
open Lean Meta Elab

/-- Proves a closed proposition (the second argument) from facts, or answers `none`. -/
abbrev Prover := Array Expr → Expr → TermElabM (Option Expr)

/-- Run `k` on a snapshot of the current elaboration state, as a task. Its
effects on the state are discarded; only the result is returned. -/
def asTask (k : TermElabM α) : TermElabM (Task (Except IO.Error α)) := do
  let coreCtx ← readThe Core.Context
  let coreSt ← getThe Core.State
  let metaCtx ← readThe Meta.Context
  let metaSt ← getThe Meta.State
  let termCtx ← readThe Term.Context
  let termSt ← getThe Term.State
  let act : CoreM (α × Term.State) := (k.run termCtx termSt).run' metaCtx metaSt
  IO.asTask (prio := .dedicated) do
    let ((a, _), _) ← act.toIO coreCtx coreSt
    return a

/-- Prove independent targets concurrently, `jobs` at a time (each target from
the current elaboration state). A proof that mentions a constant the current
environment lacks (one declared inside its task) is redone here. -/
def proveParallel (jobs : Nat) (prove : Prover) (facts : Array Expr) (targets : Array Expr) :
    TermElabM (Array (Option Expr)) := do
  let jobs := max 1 jobs
  let next ← IO.mkRef 0
  let tasks ← (Array.range (min jobs targets.size)).mapM fun _ => asTask do
    let saved ← Term.saveState
    let mut results := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if i ≥ targets.size then break
      let result ← try prove facts targets[i]! catch _ => pure none
      -- Each target gets the original elaboration state, just as when it had
      -- its own task. Workers can take the next target without waiting for a
      -- slower member of a fixed batch.
      saved.restore
      results := results.push (i, result)
    return results
  let mut out := Array.replicate targets.size none
  for task in tasks do
    if let .ok results := task.get then
      for (i, result) in results do out := out.set! i result
  for i in [:targets.size] do
    if let some pr := out[i]! then
      let env ← getEnv
      unless pr.getUsedConstants.all env.contains do
        out := out.set! i (← prove facts targets[i]!)
  return out

/-- The definitions inspected behind the observations of a goal. -/
private def maxInspected : Nat := 256

/-- The relations proposed for one goal. -/
private def maxProposals : Nat := 64

/-- A definition returning a `Bool` (a check) or an `Int` (a quantity). -/
private structure Observer where
  function : Expr
  domains : Array Expr
  /-- The positions of its list (or array) arguments. -/
  inputs : Array Nat
  boolean : Bool

private def observer? (name : Name) : MetaM (Option Observer) := do
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do return none
  forallTelescope info.type fun arguments result => do
    let result ← whnf result
    unless result.isConstOf ``Bool || result.isConstOf ``Int do return none
    let mut domains := #[]
    let mut inputs := #[]
    for (argument, index) in arguments.zipIdx do
      let domain ← whnf (← inferType argument)
      if domain.hasFVar || domain.hasMVar || domain.isSort || domain.isForall ||
          (← isProp domain) then return none
      domains := domains.push domain
      if domain.isAppOf ``List || domain.isAppOf ``Array then inputs := inputs.push index
    if inputs.isEmpty then return none
    return some {function := mkConst name, domains, inputs, boolean := result.isConstOf ``Bool}

/-- Inspect the ordinary definitions behind observations, including recursive
checks nested under match binders. Dependencies precede their callers so a
proved local contract can support a later, larger observation. -/
private def dependencies (patterns : Array Expr) : MetaM (Array Observer) := do
  let roots := patterns.flatMap (·.getUsedConstants)
  let mut pending := roots.reverse.map (·, false)
  let mut seen : NameSet := {}
  let mut found := #[]
  while !pending.isEmpty do
    let (name, expanded) := pending.back!
    pending := pending.pop
    if expanded then
      if let some observer ← observer? name then found := found.push observer
      continue
    if seen.contains name || Source.primitive name then continue
    if seen.size == maxInspected then continue
    seen := seen.insert name
    let environment ← getEnv
    if isMatcherCore environment name || isCasesOnRecursor environment name then continue
    let .defnInfo info ← getConstInfo name | continue
    unless info.safety == .safe && info.levelParams.isEmpty do continue
    pending := pending.push (name, true) ++ info.value.getUsedConstants.reverse.map (·, false)
  return found

private def relation? (condition quantity : Observer) (left right : Nat) : MetaM (Option Expr) := do
  unless condition.boolean && !quantity.boolean do return none
  unless ← isDefEq condition.domains[left]! quantity.domains[right]! do return none
  let domains := condition.domains ++ quantity.domains
  withLocalDeclsD (domains.mapIdx fun index domain =>
      (Name.mkSimple s!"argument{index}", fun _ => pure domain)) fun parameters => do
    let observed := parameters[left]!
    let first := parameters.extract 0 condition.domains.size
    let second := (parameters.extract condition.domains.size parameters.size).set! right observed
    let premise ← mkEq (mkAppN condition.function first) (mkConst ``Bool.true)
    let result := mkApp2 (mkConst ``Int.le) (toExpr (0 : Int)) (mkAppN quantity.function second)
    let omitted := condition.domains.size + right
    let binders := parameters.extract 0 omitted ++ parameters.extract (omitted + 1) parameters.size
    return some (← mkForallFVars binders (← mkArrow premise result))

private def nonnegative? (condition quantity : Expr) : MetaM (Option Expr) := do
  unless condition.getNumHeadLambdas == 1 && quantity.getNumHeadLambdas == 1 do return none
  let proposition ← lambdaTelescope quantity fun arguments value => do
    unless (← whnf (← inferType value)).isConstOf ``Int do return none
    let input := arguments[0]!
    let domain ← whnf (← inferType input)
    unless domain.isAppOf ``List || domain.isAppOf ``Array do return none
    unless ← isDefEq domain condition.bindingDomain! do return none
    let valid := condition.beta #[input]
    unless (← whnf (← inferType valid)).isConstOf ``Bool do return none
    let premise ← mkEq valid (mkConst ``Bool.true)
    let result := mkApp2 (mkConst ``Int.le) (toExpr (0 : Int)) value
    return some (← mkForallFVars arguments (← mkArrow premise result))
  let some proposition := proposition | return none
  let free := (collectFVars {} proposition).fvarSet
  let mut parameters := #[]
  for declaration in ← getLCtx do
    unless free.contains declaration.fvarId do continue
    -- Original theorem assumptions must never become premises of a generated
    -- library fact. Close only independent first-order query values.
    if declaration.type.hasFVar || (← isProp declaration.type) ||
        declaration.type.isForall || declaration.type.isSort then return none
    parameters := parameters.push declaration.toExpr
  let closed ← mkForallFVars parameters proposition
  if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then return none
  return some closed

/-- Propose relations `valid xs = true → 0 ≤ quantity xs` between the goal's
observers `patterns` and between the definitions behind them, and keep those
`prove` proves (`jobs` at a time), as kernel-checked theorems. -/
def discover (jobs : Nat) (patterns : Array Expr) (prove : Prover) : TermElabM (Array Expr) := do
  -- facts between the goal's own observers first: they are what the
  -- invariant search reads; relations between helper definitions support them
  let mut proposals := #[]
  for condition in patterns do
    for quantity in patterns do
      if let some target ← nonnegative? condition quantity then proposals := proposals.push target
  let helpers ← dependencies patterns
  for condition in helpers do
    for quantity in helpers do
      for left in condition.inputs do
        for right in quantity.inputs do
          if let some target ← relation? condition quantity left right then
            proposals := proposals.push target
  let mut targets := #[]
  for target in proposals do
    if targets.size == maxProposals then break
    unless targets.contains target do targets := targets.push target
  -- the candidates are independent: prove them concurrently
  let proofs ← proveParallel jobs prove #[] targets
  let mut facts := #[]
  for (target, proof?) in targets.zip proofs do
    let some proof := proof? | continue
    if proof.hasFVar || proof.hasMVar || proof.hasSorry then
      throwError "observation prover returned an incomplete proof"
    let environment ← getEnv
    let name := environment.asyncPrefix?.getD environment.mainModule ++
      `blasterObserverFact ++ (← mkFreshId)
    addDecl (.thmDecl {name, levelParams := [], type := target, value := proof})
    facts := facts.push (mkConst name)
  return facts

end Blaster.Proof.Induction.ObserverFacts
