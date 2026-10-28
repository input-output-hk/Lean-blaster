import Blaster

namespace TestsFF.Model

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

/-! Live typed counterexamples through the actual source translator. The pinned,
offline-qualified cvc5 process must return the uniquely forced representative;
its own get-value response is paired with the retained source symbol and name.
These SAT observations never constitute Lean proofs. -/

private theorem evidence2 : PrimeModulus 2 :=
  ⟨prime_of_bounded 2 1 (by decide) (by decide) (by decide)⟩

private theorem evidence3 : PrimeModulus 3 :=
  ⟨prime_of_bounded 3 1 (by decide) (by decide) (by decide)⟩

private theorem evidence7 : PrimeModulus 7 :=
  ⟨prime_of_bounded 7 2 (by decide) (by decide) (by decide)⟩

private def f2Model : Prop := ∀ x : Residue 2, x + 1 ≠ 0
private def f3Model : Prop := ∀ x : Residue 3, x + 1 ≠ 0
private def f7Model : Prop := ∀ x : Residue 7, x + 1 ≠ 0

-- Negating the disjunction forces all three representatives in one solver
-- record, so matching a value from another variable cannot satisfy this case.
private def mixedModels : Prop :=
  ∀ (x : Residue 2) (y : Residue 3) (z : Residue 7),
    x + 1 ≠ 0 ∨ y + 1 ≠ 0 ∨ z + 1 ≠ 0

private structure ExpectedValue where
  userName : Name
  modulus : Nat
  value : Nat

private structure Case where
  declaration : Name
  values : Array ExpectedValue
  generateCex : Bool := true

private def mixedValues : Array ExpectedValue := #[
  { userName := `x, modulus := 2, value := 1 },
  { userName := `y, modulus := 3, value := 2 },
  { userName := `z, modulus := 7, value := 6 }
]

private def cases : Array Case := #[
  { declaration := ``f2Model,
    values := #[{ userName := `x, modulus := 2, value := 1 }] },
  { declaration := ``f3Model,
    values := #[{ userName := `x, modulus := 3, value := 2 }] },
  { declaration := ``f7Model,
    values := #[{ userName := `x, modulus := 7, value := 6 }] },
  { declaration := ``mixedModels, values := mixedValues },
  { declaration := ``mixedModels, values := mixedValues, generateCex := false }
]

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def runCase (executable : String) (test : Case) : MetaM Unit := do
  let environment : TranslateEnv :=
    { (default : TranslateEnv) with optEnv.options.solverOptions := {
        solver := some .cvc5
        timeout := some 30
        generateCex := test.generateCex
        solveResult := .ExpectedFalsified } }
  let ((result, _), finalEnvironment) ←
    (Translate.main (mkConst test.declaration)).run environment
  let state := finalEnvironment.smtEnv
  unless state.sessions.isEmpty && state.emitProc.isNone &&
      !state.nativeFieldQualified && state.singleSolver == some .cvc5 do
    throwError "{test.declaration}: native model session was not retired"
  unless state.configuredSolvers == #[.cvc5] && state.solverRecords.size == 1 do
    throwError "{test.declaration}: expected only the pinned cvc5 solver"
  let some record := state.solverRecords[0]?
    | throwError "{test.declaration}: missing live solver record"
  unless record.solver == .cvc5 && record.version == "offline capability-qualified" &&
      record.commandLine.startsWith (executable ++ " ") do
    throwError "{test.declaration}: solver was not the offline-qualified pinned executable"
  let some checkCommand := record.checkCommand
    | throwError "{test.declaration}: no actual check-sat command"
  unless toString checkCommand == "(check-sat)" &&
      record.stdout.any (fun response => response.trim == "sat") do
    throwError "{test.declaration}: missing exact live SAT response"
  unless record.failedStage.isNone && record.stderr.isEmpty do
    throwError "{test.declaration}: solver/model failure or unexpected stderr"
  let commands := record.setupCommands.toList.map toString ++
    state.smtCommands.toList.map toString ++ [toString checkCommand] ++
    record.modelCommands.toList
  unless commands.all (fun command => !contains command "(get-proof") do
    throwError "{test.declaration}: SAT counterexamples must not request proofs"
  let .Falsified counterexample := result
    | throwError "{test.declaration}: the live SAT verdict must remain Falsified"
  if test.generateCex then
    unless counterexample.length == test.values.size &&
        record.modelCommands.size == test.values.size &&
        record.modelResponses.size == test.values.size do
      throwError "{test.declaration}: missing or extra model displays/requests/responses"
  else
    unless counterexample.isEmpty && record.modelCommands.isEmpty &&
        record.modelResponses.isEmpty do
      throwError "{test.declaration}: disabled counterexamples must not request or display evidence"
  for expected in test.values do
    let associations := state.sourceAssociations.filter fun entry =>
      entry.userName == expected.userName && entry.modulus == some expected.modulus &&
        entry.source.isFVar
    unless associations.size == 1 do
      throwError "{test.declaration}: missing unique source association for {expected.userName}"
    let some association := associations[0]?
      | throwError "{test.declaration}: missing source association"
    unless commands.any (fun command =>
        contains command s!"(_ FiniteField {expected.modulus})") do
      throwError "{test.declaration}: missing native field declaration"
    if test.generateCex then
      let literal := s!"#f{expected.value}m{expected.modulus}"
      let display := s!"{expected.userName}: ({expected.value} : Blaster.FiniteField.Residue {expected.modulus}) [{literal}]"
      unless counterexample.contains display do
        throwError "{test.declaration}: missing exact typed display {display}; got {counterexample}"
      let request := toString (SmtCommand.getValue (smtSimpleVarId association.symbol))
      let matchingRequests := record.modelCommands.filter (· == request)
      unless matchingRequests.size == 1 do
        throwError "{test.declaration}: source symbol lacks its own unique get-value request"
      for index in [:record.modelCommands.size] do
        if record.modelCommands[index]! == request then
          let response := record.modelResponses[index]!
          unless response.trim == s!"(({association.symbol} {literal}))" &&
              record.stdout.contains response do
            throwError "{test.declaration}: expected this source symbol's exact literal in its solver record"

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
  withCheckedEvidence [``evidence2, ``evidence3, ``evidence7] do
    for test in cases do
      runCase executable test
    IO.println s!"TestsFF.Model: executed {cases.size} live SAT model cases (4 typed, 1 disabled)"

run_cmd do
  for declaration in #[``evidence2, ``evidence3, ``evidence7] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected model fixture axiom in {declaration}: {axiomName}"

end TestsFF.Model
