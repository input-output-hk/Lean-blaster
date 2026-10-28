import Blaster.FiniteField.Admission
import Blaster.Smt.FiniteFieldCapability

open Lean Meta Blaster.Optimize Blaster.Options Blaster.FiniteField

namespace Blaster.Smt

/-- Fields found in each visited subterm, so shared subterms of the optimized
DAG are walked once instead of once per path. -/
private abbrev FieldCache := IO.Ref (Std.HashMap Expr (Array ResidueDescriptor))

/-- Collect exact nominal carriers from the residual syntax and variable types,
without unfolding term definitions or admitting fields in a nested scope. -/
private partial def collectNativeFieldsAux (cache : FieldCache) (e : Expr)
    (fields : Array ResidueDescriptor) : TranslateEnvT (Array ResidueDescriptor) := do
  let type ← inferType e
  let carrier := if type.isSort then e else type
  let mut fields := fields
  let native := (← getResidueModulus? carrier).isSome
  if native then
    let some descriptor ← getResidueDescriptor? carrier
      | throwEnvError "native finite-field routing requires a concrete closed Residue modulus"
    unless fields.any (·.type == descriptor.type) do
      fields := fields.push descriptor
    -- A carrier is atomic, but a term of that carrier can still consume values
    -- from another field whose admission must be checked independently.
    if type.isSort then return fields
  -- Instantiated result types can contain a field even when no application
  -- argument exposes it (for example an opaque constant of `List (Residue p)`).
  if !type.isSort && !native then
    fields ← visit cache type fields
  match e with
  | .app .. =>
      let args := e.getAppArgs
      if e.getAppFn.isConstOf ``ite && args.size == 5 then
        fields ← visit cache args[1]! fields
        fields ← visit cache args[3]! fields
        return ← visit cache args[4]! fields
      if e.getAppFn.isConstOf ``Blaster.dite' && args.size == 4 then
        fields ← visit cache args[1]! fields
        for branch in #[args[2]!, args[3]!] do
          let .lam _ _ body _ := branch
            | throwEnvError "native finite-field ite requires normalized branches"
          if body.hasLooseBVars then
            throwEnvError "native finite-field ite does not support proof-dependent branches"
          fields ← visit cache body fields
        return fields
      for arg in e.getAppArgs do
        fields ← visit cache arg fields
      return fields
  | .fvar .. => return fields
  | .mdata _ body => visit cache body fields
  | .proj _ _ body => visit cache body fields
  | .forallE _ domain body _ =>
      if (← isProp domain) && !body.hasLooseBVars then
        fields ← visit cache domain fields
        return ← visit cache body fields
      let nested ← visit cache domain #[]
      let nested ← withLocalDeclD `x domain fun x =>
        visit cache (body.instantiate1 x) nested
      unless nested.isEmpty do
        throwEnvError "native finite-field routing does not support residual quantified or higher-order FF queries; only top-level theorem parameters are permitted"
      return fields
  | .lam name domain body bi =>
      let nested ← visit cache domain #[]
      let nested ← withLocalDecl name bi domain fun x =>
        visit cache (body.instantiate1 x) nested
      unless nested.isEmpty do
        throwEnvError "native finite-field routing does not support residual quantified or higher-order FF queries; only top-level theorem parameters are permitted"
      return fields
  | .letE name type value body _ =>
      let valueFields ← visit cache value fields
      withLetDecl name type value fun x => visit cache (body.instantiate1 x) valueFields
  | _ => return fields

where
  /-- Add the fields of `e`'s subtree to `fields`. A cached subtree contributes
  the same fields, in the same order, as a fresh walk would, so binder checks
  that start from `#[]` still see every field below them. -/
  visit (cache : FieldCache) (e : Expr) (fields : Array ResidueDescriptor) :
      TranslateEnvT (Array ResidueDescriptor) := do
    let sub ← match (← cache.get).get? e with
      | some sub => pure sub
      | none =>
          let sub ← collectNativeFieldsAux cache e #[]
          cache.modify (·.insert e sub)
          pure sub
    return sub.foldl (init := fields) fun acc d =>
      if acc.any (·.type == d.type) then acc else acc.push d

/-- Collect the native carriers of `e`, appending to `fields`. -/
private def collectNativeFields (e : Expr) (fields : Array ResidueDescriptor) :
    TranslateEnvT (Array ResidueDescriptor) := do
  collectNativeFieldsAux.visit (← IO.mkRef {}) e fields

/-- Inspect the optimized residual only. Top-level theorem parameters and their
matching primality hypotheses stay in scope for admission and the continuation.
Admission evidence must not escape this callback or be cached across queries. -/
def withNativeFieldQuery (e : Expr)
    (k : Array Expr → Expr → Array NativeFieldAdmission → TranslateEnvT α) : TranslateEnvT α :=
  Optimize.forallTelescope e fun parameters body => do
    let mut fields := #[]
    for parameter in parameters do
      fields ← collectNativeFields (← inferType parameter) fields
    fields ← collectNativeFields body fields
    let mut admitted := #[]
    for field in fields do
      admitted := admitted.push (← admitNativeField field)
    k parameters body admitted

/-- Inspect native requirements while retaining the opened parameter scope. -/
def withNativeFieldRequirements (e : Expr)
    (k : Array NativeFieldAdmission → TranslateEnvT α) : TranslateEnvT α :=
  withNativeFieldQuery e fun _ _ fields => k fields

/-- Backend policy uses the ordinary explicit-option/environment resolution.
Query theory requirements do not imply any per-executable capability. -/
def finiteFieldBackendPolicy (options : BlasterOptions) (environment : Option String) :
    Except String SmtSolver := do
  validateSolverOptions options
  if options.solverMode != .single then
    throw s!"native finite-field queries do not support solver-mode: {options.solverMode}; use single mode with solver: cvc5"
  let solver ← resolveSolverConfig options environment
  unless solver == .cvc5 do
    let origin := if options.solver.isSome then "explicit solver option"
      else if environment.isSome then "BLASTER_SOLVER" else "default (BLASTER_SOLVER unset)"
    throw s!"native finite-field query resolved backend {solver} via {origin}; use solver: cvc5"
  return solver

/-- Preflight before any native theory emission. Concurrent sessions already
started before optimization are retired through the existing exit path before
raising the policy diagnostic. Dry runs do not discover or probe executables;
`setBlasterProcess` remains responsible for their ordinary setup records. -/
def preflightFiniteFields (e : Expr)
    (probe : IO SolverCandidate := probeFiniteFieldSolver) :
    TranslateEnvT (Option SolverCandidate) := do
  modify fun env => { env with smtEnv.nativeFieldQualified := false }
  let options := (← get).optEnv.options.solverOptions
  match validateSolverOptions options with
  | .error message => throwEnvError message
  | .ok () => pure ()
  withNativeFieldRequirements e fun fields => do
    if fields.isEmpty then return none
    match finiteFieldBackendPolicy options (← IO.getEnv "BLASTER_SOLVER") with
    | .error message =>
        discard exitSmt
        throwEnvError message
    | .ok _ => pure ()
    if options.onlySmtLib then
      modify fun env => { env with smtEnv.nativeFieldQualified := true }
      return none
    try
      let candidate ← probe
      modify fun env => { env with smtEnv.nativeFieldQualified := true }
      return some candidate
    catch error : Exception =>
      throwEnvError m!"native finite-field solving capability preflight failed: {error.toMessageData}"

end Blaster.Smt
