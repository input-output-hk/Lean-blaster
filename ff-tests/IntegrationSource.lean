import Blaster

namespace TestsFF.Integration

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

/-! Cross-feature M1 observations through the staged native solver, not Lean
proofs. Polynomial and total-division translation share a multi-field query;
positive graph obligations must remain outside nested implication polarity.
Fresh sessions must not inherit witnesses or optional model requests. M2 proof
reconstruction, proof-solver qualification, rule audit and FF optimizer rewrites
remain unfinished; these checks do not extend the `blasterProven` boundary. -/

private instance evidence2 : PrimeModulus 2 := ⟨by
  apply prime_of_bounded 2 1 (by decide) (by decide)
  intro m hm hm2
  omega⟩

private instance evidence7 : PrimeModulus 7 := ⟨by
  apply prime_of_bounded 7 2 (by decide) (by decide)
  intro m hm hm2
  have heq : m = 2 := by omega
  subst m
  decide⟩

-- The polynomial premises force the unique zero counterexample in both fields.
-- At zero both inner implications hold; their division graphs must not acquire
-- the negative polarity of an implication antecedent or of the overall goal.
private def mixedCounterexample : Prop :=
  ∀ (x : Residue 2) (y : Residue 7),
    (x ^ (2 : Nat) = 0 ∧ y ^ (2 : Nat) = 0) →
    (x / x = 1 → x ≠ 0) → (y / y = 1 → y ≠ 0) →
    x / x = 1 ∨ y / y = 1

-- This identity includes the totalized zero branch, not only nonzero division.
private def mixedPolynomialDivision : Prop :=
  ∀ (x : Residue 2) (y : Residue 7),
    (x / x = 1 → x ≠ 0) → (y / y = 1 → y ≠ 0) →
    (x ^ (2 : Nat) / x) * x = x ^ (2 : Nat) ∧
    (y ^ (2 : Nat) / y) * y = y ^ (2 : Nat)

private structure Case where
  declaration : Name
  falsified : Bool
  generateCex : Bool := true

-- Interleave verdicts and model settings to expose stale session evidence.
private def cases : Array Case := #[
  { declaration := ``mixedCounterexample, falsified := true },
  { declaration := ``mixedPolynomialDivision, falsified := false },
  { declaration := ``mixedCounterexample, falsified := true, generateCex := false }
]

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def runCase (executable : String) (test : Case) : MetaM (Array SourceAssociation) := do
  let environment : TranslateEnv :=
    { (default : TranslateEnv) with optEnv.options.solverOptions := {
        solver := some .cvc5
        timeout := some 30
        generateCex := test.generateCex
        solveResult := if test.falsified then .ExpectedFalsified else .ExpectedValid } }
  let ((result, _), finalEnvironment) ←
    (Translate.main (mkConst test.declaration)).run environment
  let state := finalEnvironment.smtEnv
  unless state.sessions.isEmpty && state.emitProc.isNone &&
      !state.nativeFieldQualified && state.singleSolver == some .cvc5 &&
      state.configuredSolvers == #[.cvc5] && state.solverRecords.size == 1 do
    throwError "{test.declaration}: expected one retired native cvc5 session"
  let some record := state.solverRecords[0]?
    | throwError "{test.declaration}: missing solver record"
  unless record.solver == .cvc5 && record.version == "offline capability-qualified" &&
      record.commandLine.startsWith (executable ++ " ") do
    throwError "{test.declaration}: did not use the staged, qualified cvc5 route"
  let some checkCommand := record.checkCommand
    | throwError "{test.declaration}: optimizer-only success is not integration"
  let expected := if test.falsified then "sat" else "unsat"
  unless toString checkCommand == "(check-sat)" &&
      record.stdout.any (fun response => response.trim == expected) &&
      record.failedStage.isNone && record.stderr.isEmpty do
    throwError "{test.declaration}: expected an actual successful {expected} check-sat"
  let commands := state.smtCommands.toList.map toString
  let transcript := String.intercalate "\n" commands
  for modulus in #[2, 7] do
    for fragment in #[s!"(_ FiniteField {modulus})", s!"@FF{modulus}.pow2",
        s!"@FF{modulus}.mul"] do
      unless contains transcript fragment do
        throwError "{test.declaration}: missing integrated native operation {fragment}"
  let variables := state.sourceAssociations.filter (·.source.isFVar)
  let witnesses := state.sourceAssociations.filter (·.inverseGraph.isSome)
  unless variables.size == 2 && witnesses.size == 2 && state.topLevelVars.size == 2 do
    throwError "{test.declaration}: expected exactly two source variables and two shared inverse witnesses"
  let assertions := commands.filter (·.startsWith "(assert ")
  unless assertions.length == witnesses.size + 1 &&
      assertions.any (·.startsWith "(assert (not ") do
    throwError "{test.declaration}: expected positive graphs plus one negated source query"
  for entry in state.sourceAssociations do
    unless entry.polarity == .negated do
      throwError "{test.declaration}: source assertion polarity was lost"
    withLCtx entry.localContext entry.localInstances do
      let .ok _ := Kernel.check (← getEnv) (← getLCtx) entry.source
        | throwError "{test.declaration}: source metadata escaped its query context"
  for entry in witnesses do
    let some graph := entry.inverseGraph | throwError "missing graph metadata"
    let some modulus := entry.modulus | throwError "missing graph modulus"
    unless graph.graphPolarity == .positive && graph.scope != .anonymous do
      throwError "{test.declaration}: graph ownership or positive polarity was lost"
    let some denominator := variables.find? (fun source =>
        source.source == graph.denominator && source.modulus == some modulus)
      | throwError "{test.declaration}: inverse denominator is not owned by this query"
    let some obligation := translateInverseGraph modulus
        (smtSimpleVarId denominator.symbol) (smtSimpleVarId entry.symbol)
      | throwError "{test.declaration}: invalid inverse graph modulus"
    let assertion := toString (SmtCommand.assertTerm obligation)
    unless (assertions.filter (· == assertion)).length == 1 do
      throwError "{test.declaration}: inverse graph must be asserted positively exactly once"
  unless (record.setupCommands.toList.map toString ++ commands ++
      [toString checkCommand] ++ record.modelCommands.toList).all
      (fun command => !contains command "(get-proof") do
    throwError "{test.declaration}: M1 observations must not request proofs"
  match result with
  | .Valid =>
      if test.falsified then throwError "{test.declaration}: SAT must remain Falsified"
      unless record.modelCommands.isEmpty && record.modelResponses.isEmpty do
        throwError "{test.declaration}: UNSAT retained stale SAT evidence"
  | .Falsified counterexample =>
      unless test.falsified do throwError "{test.declaration}: expected Valid from UNSAT"
      if test.generateCex then
        unless counterexample.length == 2 && record.modelCommands.size == 2 &&
            record.modelResponses.size == 2 do
          throwError "{test.declaration}: expected evidence only for the two source variables"
        for (name, modulus) in #[(`x, 2), (`y, 7)] do
          let some association := variables.find? (fun entry =>
              entry.userName == name && entry.modulus == some modulus)
            | throwError "{test.declaration}: missing typed source variable {name}"
          let literal := s!"#f0m{modulus}"
          let display := s!"{name}: (0 : Blaster.FiniteField.Residue {modulus}) [{literal}]"
          unless counterexample.contains display do
            throwError "{test.declaration}: missing forced zero counterexample {display}"
          let request := toString (SmtCommand.getValue (smtSimpleVarId association.symbol))
          unless (record.modelCommands.filter (· == request)).size == 1 do
            throwError "{test.declaration}: missing source-owned model request"
          for index in [:record.modelCommands.size] do
            if record.modelCommands[index]! == request then
              let response := record.modelResponses[index]!
              unless response.trim == s!"(({association.symbol} {literal}))" &&
                  record.stdout.contains response do
                throwError "{test.declaration}: model response belongs to another source/session"
      else
        unless counterexample.isEmpty && record.modelCommands.isEmpty &&
            record.modelResponses.isEmpty do
          throwError "{test.declaration}: disabled evidence must preserve SAT without model requests"
  | .Undetermined => throwError "{test.declaration}: Undetermined is not accepted"
  return variables ++ witnesses

private def withCheckedEvidence (declarations : List Name) (action : MetaM Unit) : MetaM Unit :=
  match declarations with
  | [] => action
  | declaration :: rest => do
      let proof := mkConst declaration
      withLetDecl declaration (← inferType proof) proof fun _ =>
        withCheckedEvidence rest action

run_meta do
  let some executable ← IO.getEnv "BLASTER_FF_CVC5"
    | throwError "BLASTER_FF_CVC5 must name the staged solver; run make test-cvc5-ff"
  unless executable.startsWith "/" && (← (System.FilePath.mk executable).pathExists) do
    throwError "BLASTER_FF_CVC5 must name an existing absolute executable path"
  withCheckedEvidence [``evidence2, ``evidence7] do
    let mut retained : Array SourceAssociation := #[]
    let mut sat := 0
    let mut unsat := 0
    for test in cases do
      let current ← runCase executable test
      for entry in current do
        for prior in retained do
          if entry.source.isFVar && prior.source.isFVar && entry.source == prior.source then
            throwError "integration: a subsequent query reused a source variable"
          if let some graph := entry.inverseGraph then
            if let some previous := prior.inverseGraph then
              unless graph.scope != previous.scope && entry.symbol != prior.symbol do
                throwError "integration: inverse witness ownership leaked across sessions"
      retained := retained ++ current
      if test.falsified then sat := sat + 1 else unsat := unsat + 1
    -- The later sessions must not invalidate an earlier query's saved context.
    for entry in retained do
      withLCtx entry.localContext entry.localInstances do
        let .ok _ := Kernel.check (← getEnv) (← getLCtx) entry.source
          | throwError "integration: subsequent session invalidated retained source metadata"
    unless sat > 0 && unsat > 0 do
      throwError "Integration must execute nonzero live SAT and UNSAT cases"
    IO.println s!"TestsFF.Integration: executed {sat} SAT and {unsat} UNSAT integrated live native cases"

run_cmd do
  for declaration in #[``evidence2, ``evidence7] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected integration fixture axiom in {declaration}: {axiomName}"

end TestsFF.Integration
