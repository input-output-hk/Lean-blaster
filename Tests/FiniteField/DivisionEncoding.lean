import Tests.Pure
import Blaster.FiniteField.DivisionEncoding
import Blaster.Smt.Translate.FiniteField
import Lean.Util.CollectAxioms

/-! Pure scoped-inverse transcripts, optimizer boundaries, and transitive proof
trust guards. No executable solver is selected or started by these tests. -/
namespace Test.FiniteFieldDivisionEncoding

open Lean Meta Blaster.FiniteField Blaster.Optimize Blaster.Smt

private def options : TranslateEnv :=
  { (default : TranslateEnv) with
    optEnv.options.solverOptions := {
      -- Transcript mode cannot solve; declare the same outcome checked below
      -- so the strict cvc5 lane does not mistake a dry run for a solver failure.
      solver := some .cvc5, onlySmtLib := true, timeout := some 1,
      solveResult := .ExpectedUndetermined } }

private def body (name : Name) : MetaM Expr := do
  let .defnInfo info ← getConstInfo name | throwError "missing fixture {name}"
  return info.value

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def transcript (env : TranslateEnv) : String :=
  String.intercalate "\n" (env.smtEnv.smtCommands.toList.map toString)

private def require (text fragment : String) : MetaM Unit := do
  unless contains text fragment do throwError "missing {fragment}:\n{text}"

private def witnesses (env : TranslateEnv) : Array SourceAssociation :=
  env.smtEnv.sourceAssociations.filter (·.inverseGraph.isSome)

private def witnessAt (env : TranslateEnv) (index := 0) : MetaM SourceAssociation := do
  let some entry := (witnesses env)[index]? | throwError "missing inverse witness {index}"
  return entry

private def sourceVariable (env : TranslateEnv) (name : Name) : MetaM SourceAssociation := do
  let some entry := env.smtEnv.sourceAssociations.find?
      (fun entry => entry.source.isFVar && entry.userName == name)
    | throwError "missing source variable {name}"
  return entry

private def graph (p : Nat) (denominator witness : String) : String :=
  s!"(assert (or (and (= {denominator} #f0m{p}) (= {witness} #f0m{p})) (= (ff.mul {denominator} {witness}) #f1m{p})))"

private def checkPure (env : TranslateEnv) : MetaM Unit := do
  unless env.smtEnv.sessions.isEmpty do throwError "pure test started a solver"
  let text := transcript env
  for forbidden in #["(declare-datatypes", "(to_int", "(mod ", "(div ",
      "ff.inv", "ff.div", "(forall ", "(exists ", "(get-model"] do
    if contains text forbidden then throwError "unsupported command escaped: {forbidden}"
  let entries := witnesses env
  let assertions := (env.smtEnv.smtCommands.map toString).filter
    (fun command => command.startsWith "(assert ")
  unless assertions.size == entries.size + 1 do
    throwError "expected one positive graph per witness and one negated goal: {text}"
  unless assertions.back!.startsWith "(assert (not " do
    throwError "residual goal was not negated after the graph assertions: {text}"
  for assertion in assertions.pop do
    unless assertion.startsWith "(assert (or (and " do
      throwError "graph is not a positive query-level assertion: {assertion}"
  for entry in entries do
    let some info := entry.inverseGraph | throwError "missing inverse metadata"
    unless entry.polarity == .negated && info.graphPolarity == .positive do
      throwError "graph polarity confused with query polarity"
    let some p := entry.modulus | throwError "inverse witness has no modulus"
    require text s!"(declare-const {entry.symbol} @FF{p})"
    unless (toString entry.symbol).startsWith "@ffinv" do
      throwError "inverse witness does not have a fresh reserved symbol"
    withLCtx entry.localContext entry.localInstances do
      for expr in #[entry.source, entry.type, info.denominator] do
        let .ok _ := Kernel.check (← getEnv) (← getLCtx) expr
          | throwError "inverse metadata escaped its local scope"
      unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx)
          (← inferType entry.source) entry.type do
        throwError "inverse source type does not describe its expression"
      unless entry.source.getAppFn.isConstOf ``Inv.inv &&
          entry.source.getAppArgs.back! == info.denominator do
        throwError "inverse association source is not the denominator's inverse"
      unless (← getResidueModulus? entry.type).isSome do
        throwError "inverse source has lost its nominal carrier"
      let primeType := mkApp (mkConst ``PrimeModulus) (mkNatLit p)
      let primeEvidence ← synthInstance primeType
      let .ok _ := Kernel.check (← getEnv) (← getLCtx) primeEvidence
        | throwError "inverse metadata lost its saved local prime instance"

private def directAction (query : Expr) : TranslateEnvT Unit := do
  let candidate ← preflightFiniteFields query
  unless candidate.isNone do throwError "transcript translation selected a solver executable"
  setBlasterProcess candidate
  let some term ← translatePolynomial query | throwError "native inverse query fell through"
  assertTerm (notSmt term)

private def direct (name : Name) : MetaM TranslateEnv := do
  let (_, env) ← (directAction (← body name)).run options
  checkPure env
  return env

private def inverse : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), x⁻¹ = x
private def division : Prop := ∀ (_ : PrimeModulus 7) (a b : Residue 7), a / b = a
private def sharing : Prop := ∀ (_ : PrimeModulus 7) (a b c : Residue 7),
  a / b = c / b ∧ b⁻¹ = a
private def distinct : Prop := ∀ (_ : PrimeModulus 7) (a b c : Residue 7), a / b = a / c
private def arithmeticDenominator : Prop := ∀ (_ : PrimeModulus 7) (a b c : Residue 7),
  (a / b) / (c + a) = c
private def twoFields : Prop := ∀ (_ : PrimeModulus 7) (_ : PrimeModulus 11)
    (a b : Residue 7) (c d : Residue 11), a / b = a ∧ c / d = c
private abbrev modulusAlias : Nat := 3 + 4
private instance aliasNonzero : NeZero modulusAlias := ⟨by decide⟩
private def aliasFields : Prop := ∀ (_ : PrimeModulus 7)
    (a : Residue modulusAlias) (b : Residue 7), a⁻¹ = a ∧ b⁻¹ = b
private def aliasSharing : Prop := ∀ (_ : PrimeModulus 7) (a : Residue modulusAlias),
  @Inv.inv (Residue modulusAlias) inferInstance a = @Inv.inv (Residue 7) inferInstance a
private def nested : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), (x⁻¹)⁻¹ = x
private def booleanQuery : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7) (b : Bool),
  ((¬ (x⁻¹ = y) ∨ x / y = x) ↔ (x = y → y⁻¹ ≠ x)) ∧
  (if b then x⁻¹ else x / y) = (if y⁻¹ = x then y else x)
private def assumptions : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7),
  x / y = x → y⁻¹ ≠ x → x / y ≠ y
private def zeroCases : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7),
  x / 0 = 0 ∧ (0 : Residue 7)⁻¹ = 0 ∧ (0 : Residue 7) / 0 = 0

run_meta do
  let env ← direct ``inverse
  let x := toString (← sourceVariable env `x).symbol
  unless (witnesses env).size == 1 do throwError "inverse did not introduce exactly one witness"
  let y := toString (← witnessAt env).symbol
  require (transcript env) (graph 7 x y)
  require (transcript env) s!"(assert (not (= {y} {x})))"
  let env ← direct ``division
  let a ← sourceVariable env `a
  let b ← sourceVariable env `b
  unless (witnesses env).size == 1 do throwError "division introduced a numerator witness"
  let entry ← witnessAt env
  let some info := entry.inverseGraph | throwError "missing division witness"
  unless info.denominator == b.source && info.denominator != a.source do
    throwError "division inverted the numerator instead of the denominator"
  require (transcript env) (graph 7 (toString b.symbol) (toString entry.symbol))
  require (transcript env)
    s!"(assert (not (= (@FF7.mul {a.symbol} {entry.symbol}) {a.symbol})))"
  let env ← direct ``sharing
  unless (witnesses env).size == 1 do throwError "division/inverse did not share the exact denominator"
  let b ← sourceVariable env `b
  require (transcript env) (graph 7 (toString b.symbol) (toString (← witnessAt env).symbol))
  let env ← direct ``distinct
  unless (witnesses env).size == 2 do throwError "distinct denominators shared a witness"
  for name in #[`b, `c] do
    let denominator ← sourceVariable env name
    let some entry := (witnesses env).find?
        (fun entry => entry.inverseGraph.any (·.denominator == denominator.source))
      | throwError "missing denominator {name}"
    require (transcript env) (graph 7 (toString denominator.symbol) (toString entry.symbol))
  let env ← direct ``arithmeticDenominator
  unless (witnesses env).size == 2 do throwError "composite denominator was not independently inverted"
  let a ← sourceVariable env `a
  let c ← sourceVariable env `c
  let some composite := (witnesses env).find?
      (fun entry => entry.inverseGraph.any (fun info => !info.denominator.isFVar))
    | throwError "missing compound denominator"
  require (transcript env)
    (graph 7 s!"(@FF7.add {c.symbol} {a.symbol})" (toString composite.symbol))

run_meta do
  let env ← direct ``twoFields
  unless (witnesses env).size == 2 do throwError "different moduli shared an inverse witness"
  for (p, name) in #[(7, `b), (11, `d)] do
    let denominator ← sourceVariable env name
    let some entry := (witnesses env).find? (·.modulus == some p)
      | throwError "missing inverse witness for modulus {p}"
    require (transcript env) (graph p (toString denominator.symbol) (toString entry.symbol))
  let env ← direct ``aliasFields
  unless occurrences (transcript env) "(define-sort @FF7 " == 1 &&
      (witnesses env).size == 2 && (witnesses env).all (·.modulus == some 7) do
    throwError "modulus aliases were not normalized while keeping denominators separate"
  let env ← direct ``nested
  unless (witnesses env).size == 2 do throwError "nested inverse lost one dependency"
  let aliases ← direct ``aliasSharing
  unless (witnesses aliases).size == 1 do
    throwError "an exact denominator at equivalent moduli did not share its witness"
  let x ← sourceVariable env `x
  let some inner := (witnesses env).find?
      (fun entry => entry.inverseGraph.any (·.denominator == x.source))
    | throwError "missing inner inverse"
  let some outer := (witnesses env).find? (fun entry => entry.symbol != inner.symbol)
    | throwError "missing outer inverse"
  require (transcript env) (graph 7 (toString x.symbol) (toString inner.symbol))
  require (transcript env) (graph 7 (toString inner.symbol) (toString outer.symbol))
  require (transcript env) s!"(assert (not (= {outer.symbol} {x.symbol})))"
  let some innerInfo := inner.inverseGraph | throwError "missing inner metadata"
  let some outerInfo := outer.inverseGraph | throwError "missing outer metadata"
  unless innerInfo.scope == outerInfo.scope do throwError "one query acquired multiple inverse scopes"
  let query ← body ``inverse
  let action : TranslateEnvT Unit := do
    directAction query
    directAction query
  let (_, repeated) ← action.run options
  let entries := witnesses repeated
  unless entries.size == 2 do throwError "translation calls shared an inverse cache"
  let firstEntry ← witnessAt repeated
  let secondEntry ← witnessAt repeated 1
  let some first := firstEntry.inverseGraph | throwError "missing first scope"
  let some second := secondEntry.inverseGraph | throwError "missing second scope"
  unless first.scope != second.scope && firstEntry.symbol != secondEntry.symbol &&
      first.denominator != second.denominator do
    throwError "independent translation calls reused witness symbols or opened locals"
  for entry in entries do
    withLCtx entry.localContext entry.localInstances do
      let .ok _ := Kernel.check (← getEnv) (← getLCtx) entry.source
        | throwError "a subsequent call invalidated retained source metadata"

run_meta do
  let env ← direct ``booleanQuery
  unless (witnesses env).size == 2 do throwError "Boolean polarity duplicated inverse witnesses"
  for fragment in #["(ite ", "(=> ", "(or ", "(not (= ", "(assert (not (and "] do
    require (transcript env) fragment
  let env ← direct ``assumptions
  unless (witnesses env).size == 1 do throwError "witness-dependent assumptions were not shared"
  let x ← sourceVariable env `x
  let y ← sourceVariable env `y
  let witness ← witnessAt env
  let quotient := s!"(@FF7.mul {x.symbol} {witness.symbol})"
  require (transcript env) (graph 7 (toString y.symbol) (toString witness.symbol))
  require (transcript env)
    s!"(assert (not (=> (= {quotient} {x.symbol}) (=> (not (= {witness.symbol} {x.symbol})) (not (= {quotient} {y.symbol}))))))"
  let env ← direct ``zeroCases
  unless (witnesses env).size == 1 do throwError "zero denominator did not share its total inverse"
  require (transcript env) (graph 7 "#f0m7" (toString (← witnessAt env).symbol))
  for name in #[``inverse, ``division, ``nested, ``booleanQuery, ``assumptions] do
    let ((result, _), env) ← (Translate.main (mkConst name) false).run options
    unless isUndeterminedResult result do throwError "transcript path claimed a verified result"
    checkPure env
    unless !(witnesses env).isEmpty do throwError "optimizer erased native inverse translation"

private def inverseOperation [PrimeModulus 7] (x : Residue 7) := x⁻¹
private def divisionOperation [PrimeModulus 7] (x y : Residue 7) := x / y
private def rawDivision (x y : Fin 7) := x / y

run_meta do
  for name in #[``inverseOperation, ``divisionOperation] do
    lambdaTelescope (← body name) fun _ expression => do
      let action : TranslateEnvT Unit := do
        updateLocalContext (← mkLocalContext)
        unless (← isOpaqueFunExpr expression.getAppFn expression.getAppArgs) &&
            (← isNotFoldable expression.getAppFn expression.getAppArgs) do
          throwError "native inverse/division escaped opacity"
        unless (← getUnfoldFunDef? expression.getAppFn expression.getAppArgs).isNone &&
            (← reduceApp? expression.getAppFn expression.getAppArgs).isNone do
          throwError "inverse/division unfolded its representation"
        let normalized ← Optimize.main expression
        unless normalized.getAppFn == expression.getAppFn do
          throwError "optimizer rewrote the inverse/division head"
      discard <| action.run options
  lambdaTelescope (← body ``rawDivision) fun _ expression => do
    if ← isOpaqueResidueOperation expression.getAppFn.constName! expression.getAppArgs then
      throwError "raw Fin.div acquired finite-field opacity"
  let action : TranslateEnvT Unit := do
    let result ← translatePolynomial (← body ``rawDivision)
    unless result.isNone && (← get).smtEnv.smtCommands.isEmpty do
      throwError "raw Fin.div entered native finite-field translation"
  discard <| action.run options

private def quantified : Prop := ∀ (_ : PrimeModulus 7), ∃ x : Residue 7, x⁻¹ = 0
private def lambdaQuery : Prop := ∀ (_ : PrimeModulus 7),
  (fun x : Residue 7 => x⁻¹) = (fun x => x)
private def variablePower : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7) (n : Nat), x⁻¹ ^ n = x
private def integerPower : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), x ^ (-1 : Int) = x
private def representation : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), (x⁻¹).rep.val = 0
private def representationCast : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7),
  x⁻¹ = Residue.mk (3 : Fin 7)
private def missingEvidence : Prop := ∀ (x y : Residue 7), x = y

private def reject (name : Name) (fragment : String) (throughMain := false) : MetaM Unit := do
  let query ← body name
  let message ← try
    discard <| (directAction query).run options
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some message := message | throwError "unsupported inverse query accepted: {name}"
  unless contains message fragment do throwError "wrong rejection for {name}: {message}"
  -- Optimization may eliminate a residual lambda; rejection is required for
  -- unsupported operations that survive into the native translation boundary.
  unless throughMain do return
  let action : TranslateEnvT Unit := do
    let error ← try
      discard <| Translate.main (mkConst name) false
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    let some error := error | throwError "main accepted unsupported inverse query: {name}"
    unless contains error fragment do throwError "wrong main rejection for {name}: {error}"
    let text := transcript (← get)
    for forbidden in #["(declare-datatypes", "(to_int", "(mod ", "ff.inv", "ff.div", "(assert "] do
      if contains text forbidden then throwError "rejected query emitted {forbidden}"
    unless (← get).smtEnv.sessions.isEmpty do throwError "rejection started a solver"
  discard <| action.run options

run_meta do
  for name in #[``quantified, ``lambdaQuery] do reject name "residual quantified"
  for name in #[``variablePower, ``integerPower, ``representation, ``representationCast] do
    reject name "unsupported" true
  discard <| direct ``inverse
  reject ``missingEvidence "missing checked PrimeModulus"

theorem zeroInverse [PrimeModulus 7] : (0 : Residue 7)⁻¹ = 0 := Residue.inv_zero
theorem zeroDivision [PrimeModulus 7] : (3 : Residue 7) / 0 = 0 := by
  rw [Residue.div_eq_mul_inv, Residue.inv_zero, Lean.Grind.Semiring.mul_zero]
private instance primeSeven : PrimeModulus 7 := ⟨by
  apply prime_of_bounded 7 2 (by decide) (by decide)
  intro m hm hm2
  have heq : m = 2 := by omega
  subst m
  decide⟩

theorem fieldDivision : (3 : Residue 7) / 2 = 5 := by decide
theorem rawFinDivision : (3 : Fin 7) / 2 = 1 := by decide

-- Each new proof has an executable, transitive kernel trust guard. The existing
-- field audit is deliberately not modified or used as a substitute for this list.
run_cmd Lean.Elab.Command.liftCoreM do
  let audit : Name → CoreM Unit := fun declaration => do
    unless ((← getEnv).checked.get.find? declaration).isSome do
      throwError "missing division axiom audit declaration: {declaration}"
    for axiomName in ← collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected division axiom in {declaration}: {axiomName}"
  for declaration in #[``Residue.inverseGraph_residual, ``Residue.inverseGraph_negated,
      ``Residue.inverseGraph_assumptions, ``Residue.divisionGraph_residual,
      ``Residue.inverseGraph_scoped, ``Residue.inverseGraph_nested,
      ``aliasNonzero, ``primeSeven, ``zeroInverse, ``zeroDivision, ``fieldDivision, ``rawFinDivision] do
    audit declaration
  let rejected : Name → CoreM Unit := fun name => do
    let failed ← try
      audit name
      pure false
    catch _ => pure true
    unless failed do throwError "division audit accepted forbidden dependency: {name}"
  rejected `Test.FiniteFieldDivisionEncoding.missingAuditTarget
  let inner := `Test.FiniteFieldDivisionEncoding.temporaryInner
  let outer := `Test.FiniteFieldDivisionEncoding.temporaryOuter
  for forbidden in #[``sorryAx, ``Lean.trustCompiler, ``Lean.ofReduceBool] do
    withEnv (← getEnv) do
      for (name, dependency) in #[(inner, forbidden), (outer, inner)] do
        let info ← getConstInfo dependency
        addDecl (.defnDecl {
          name := name, levelParams := info.levelParams, type := info.type,
          value := mkConst dependency (info.levelParams.map Level.param),
          hints := .abbrev, safety := .safe })
      unless (← collectAxioms outer).contains forbidden do
        throwError "division audit did not follow transitive dependencies"
      rejected outer
  for name in #[inner, outer] do
    if (← getEnv).contains name then throwError "division audit leaked a negative control"

end Test.FiniteFieldDivisionEncoding
