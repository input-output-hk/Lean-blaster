import Blaster.Proof.Induction.Source
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Elab.Tactic.Split

/-!
Turn a closed observation of a value-returning, fuel-recursive definition into
a predicate equation graph. The generated definitions are aliases for the
original executions. Each transformed equation is independently kernel-checked
using the original unfolding equation and structural case analysis; no solver,
postcondition, or application-specific rewrite is used for this transformation.
-/
namespace Blaster.Proof.Induction.Observed
open Lean Meta Elab Tactic

/-- An observed definition: `observed args = observer (original args)`. -/
structure Entry where
  original : Name
  observed : Name
  /-- The observation: a closed proposition about the original's result. -/
  observer : Expr

/-- The observed definitions, and their checked defining equations. -/
structure Result where
  entries : Array Entry := #[]
  equations : Array Source.Equation := #[]

private def compatible (name : Name) (resultType : Expr) : MetaM Bool := do
  let .defnInfo info ← getConstInfo name | return false
  unless info.safety == .safe && info.levelParams.isEmpty &&
      (← isRecursiveDefinition name) do return false
  forallTelescope info.type fun arguments result => do
    return !arguments.isEmpty && !result.hasFVar &&
      (← isDefEq result resultType) &&
      (← isDefEq (← inferType arguments.back!) (mkConst ``Nat))

private def family (root : Name) (resultType : Expr) : MetaM (Array Source.Equation) := do
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut result := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    unless ← compatible name resultType do continue
    let equation ← Source.equationFor name
    result := result.push equation
    pending := pending ++ equation.body.getUsedConstants
  return result

private partial def push (observer : Expr) (names : NameMap Name) (value : Expr) : MetaM Expr := do
  if let .const name _ := value.getAppFn then
    if let some observed := names.find? name then
      return mkAppN (mkConst observed) value.getAppArgs
  if let .letE _ _ assigned body _ := value then
    return ← push observer names (body.instantiate1 assigned)
  if let some matcher ← matchMatcherApp? value (alsoCasesOn := true) then
    unless matcher.remaining.isEmpty do
      throwError "observed recursion does not yet support a function-valued match"
    let matcher ← matcher.transform
      (onMotive := fun _ _ => pure (mkSort levelZero))
      (onAlt := fun _ _ _ branch => push observer names branch)
    return matcher.toExpr
  if value.isAppOfArity ``ite 5 then
    let args := value.getAppArgs
    return mkAppN (mkConst ``ite [levelOne]) #[mkSort levelZero,
      args[1]!, args[2]!, ← push observer names args[3]!, ← push observer names args[4]!]
  let observed := observer.beta #[value]
  withCanUnfoldPred (fun _ info => do return !(← isRecursiveDefinition info.name))
    (whnf observed)

private def certify (observer : Expr) (names : NameMap Name)
    (source : Source.Equation) : TermElabM Source.Equation :=
  prependError m!"while checking observation equation for {source.name}:\n" do
  let name := names.get! source.name
  let (body, proof) ← forallTelescope (← inferType (mkConst source.name)) fun arguments _ => do
    let original := source.body.beta arguments
    let body ← push observer names original
    let target ← mkEq (observer.beta #[original]) body
    let goal ← mkFreshExprMVar target
    let goals ← Tactic.run goal.mvarId! <| Term.withoutErrToSorry do
      evalTactic (← `(tactic| repeat' first | rfl | split))
    unless goals.isEmpty do
      throwError "structural observation equation could not be certified for {source.name}"
    let normalized ← instantiateMVars goal
    if normalized.hasSorry || normalized.hasMVar then
      throwError "observation equation contains an unchecked proof"
    let mut unfolded := mkConst source.proof
    for argument in arguments do unfolded ← mkAppM ``congrFun #[unfolded, argument]
    unfolded ← mkAppM ``congrArg #[observer, unfolded]
    let proof ← Source.extensional arguments (← mkEqTrans unfolded normalized)
    return (← mkLambdaFVars arguments body, proof)
  let proofName := name ++ `equation
  addDecl (.thmDecl {name := proofName, levelParams := [], type := ← mkEq (mkConst name) body, value := proof})
  return {name, body, proof := proofName}

private def build (root : Name) (observer resultType : Expr) : TermElabM Result := do
  let sources ← prependError m!"while reading source family for {root}:\n" <| family root resultType
  let environment ← getEnv
  let generatedPrefix := environment.asyncPrefix?.getD environment.mainModule ++
    `blasterObserved ++ (← mkFreshId)
  let mut names : NameMap Name := {}
  let mut entries := #[]
  for source in sources do
    let name := generatedPrefix ++ source.name
    let value ← forallTelescope (← inferType (mkConst source.name)) fun arguments _ => do
      mkLambdaFVars arguments (observer.beta #[mkAppN (mkConst source.name) arguments])
    let type ← inferType value
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := value
      hints := .abbrev
      safety := .safe })
    names := names.insert source.name name
    entries := entries.push {original := source.name, observed := name, observer}
  let equations ← sources.mapM (certify observer names)
  return {entries, equations}

/-- Only closed observations already present in the theorem are lifted. The
caller cannot supply an acceptance predicate or a program-point convention. -/
def discover (expressions : Array Expr) (recursive : Array Name) : TermElabM Result := do
  let candidates ← IO.mkRef (#[] : Array (Name × Expr × Expr))
  for expression in expressions do
    expression.forEach fun node => do
      -- Keep this guard separate: a monadic type query inside a Boolean
      -- expression is evaluated before its Boolean operands short-circuit.
      unless node.isApp && !node.hasLooseBVars do return
      unless ← isProp node do return
      for argument in node.getAppArgs do
        let .const name _ := argument.getAppFn | continue
        unless recursive.contains name do continue
        let resultType ← inferType argument
        if resultType.isForall || resultType.hasFVar || (← isProp argument) then continue
        unless ← compatible name resultType do continue
        let observer ← withLocalDeclD `result resultType fun result => do
          let body := node.replace fun term => if term == argument then some result else none
          mkLambdaFVars #[result] body
        unless !observer.hasFVar && !observer.hasMVar && !observer.hasLooseBVars do continue
        candidates.modify (·.push (name, observer, resultType))
  let mut result : Result := {}
  for (name, observer, resultType) in ← candidates.get do
    if result.entries.any (fun entry => entry.original == name && entry.observer == observer) then continue
    let next ← prependError m!"while observing {name}:\n" <| build name observer resultType
    result := {entries := result.entries ++ next.entries, equations := result.equations ++ next.equations}
  return result

/-- A purely definitional replacement. Goal replacement must still request
Lean's conversion check; the generated predicates are not assumed contracts. -/
def replace (entries : Array Entry) (expression : Expr) : Expr :=
  expression.replace fun node => do
    for argument in node.getAppArgs do
      let .const name _ := argument.getAppFn | continue
      for entry in entries do
        if entry.original == name && entry.observer.beta #[argument] == node then
          return mkAppN (mkConst entry.observed) argument.getAppArgs
    none

end Blaster.Proof.Induction.Observed
