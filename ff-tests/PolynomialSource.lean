import Blaster
import Tests.FiniteField.LargePrime

namespace TestsFF.Polynomial

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField
open Test.FiniteFieldLargePrime

private instance : NeZero curve25519 := ⟨by decide⟩

/-! Live source-to-solver regressions for the separately qualified native profile.
Every case calls `Translate.main`, requires a real cvc5 check-sat transcript, and
checks its exact result. SAT evidence is an observation, never a Lean proof.
Prime evidence below is checked and installed as local definitions, not assumed
as theorem parameters. Run through `make test-cvc5-ff`; no PATH fallback or skip.
-/

private theorem evidence2 : PrimeModulus 2 :=
  ⟨prime_of_bounded 2 1 (by decide) (by decide) (by decide)⟩

private theorem evidence7 : PrimeModulus 7 :=
  ⟨prime_of_bounded 7 2 (by decide) (by decide) (by decide)⟩

private def f2FalseImplication : Prop :=
  ∀ x : Residue 2, 2 * x = 0 → x = 0

private def f2Characteristic : Prop :=
  ∀ x : Residue 2, x + x = 0

private def f7SquareSat : Prop :=
  ∀ x : Residue 7, x * x ≠ 2

private def f7SquareUnsat : Prop :=
  ∀ x : Residue 7, x * x ≠ 3

private def f7ZeroProduct : Prop :=
  ∀ x y : Residue 7, x * y = 0 → x = 0 ∨ y = 0

private def branchArithmetic : Prop :=
  ∀ x y : Residue 7,
    (if x = y then x - y else y - x) =
      -(if x = y then y - x else x - y)

-- Keep a variable-dependent residual so these cannot pass solely by evaluating
-- a closed proposition before the native translator is reached.
private def zeroPowZero : Prop :=
  ∀ x : Residue 7, x * ((0 : Residue 7) ^ (0 : Nat)) = x

private def zeroPowPositive : Prop :=
  ∀ x : Residue 7, x + ((0 : Residue 7) ^ (3 : Nat)) = x

private def powPredNonzero : Prop :=
  ∀ x : Residue 7, x ≠ 0 → x ^ (6 : Nat) = 1

-- The missing nonzero guard must yield the concrete zero counterexample.
private def powPredAtZero : Prop :=
  ∀ x : Residue 7, x ^ (6 : Nat) = 1

private def powPrime : Prop :=
  ∀ x : Residue 7, x ^ (7 : Nat) = x

private def largeDistributive : Prop :=
  ∀ x y : Residue curve25519, x * (y + 1) = x * y + x

private def largeFalseIdentity : Prop :=
  ∀ x : Residue curve25519, x + 1 = x

private def independentCharacteristics : Prop :=
  ∀ (x : Residue 2) (y : Residue 7), 2 * x = 0 ∧ 7 * y = 0

private def independentCounterexample : Prop :=
  ∀ (x : Residue 2) (y : Residue 7), x + 1 = 0 → y + 1 = 0

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private structure Case where
  declaration : Name
  falsified : Bool := false
  moduli : Array Nat
  requiredCommands : Array String := #[]
  concreteValue : Option (Nat × Nat) := none

private def cases : Array Case := #[
  { declaration := ``f2FalseImplication, falsified := true, moduli := #[2],
    concreteValue := some (1, 2) },
  { declaration := ``f2Characteristic, moduli := #[2] },
  { declaration := ``f7SquareSat, falsified := true, moduli := #[7] },
  { declaration := ``f7SquareUnsat, moduli := #[7] },
  { declaration := ``f7ZeroProduct, moduli := #[7] },
  { declaration := ``zeroPowZero, moduli := #[7], requiredCommands := #["@FF7.pow0"] },
  { declaration := ``zeroPowPositive, moduli := #[7], requiredCommands := #["@FF7.pow3"] },
  { declaration := ``powPredNonzero, moduli := #[7], requiredCommands := #["@FF7.pow6"] },
  { declaration := ``powPredAtZero, falsified := true, moduli := #[7],
    requiredCommands := #["@FF7.pow6"], concreteValue := some (0, 7) },
  { declaration := ``powPrime, moduli := #[7], requiredCommands := #["@FF7.pow7"] },
  { declaration := ``branchArithmetic, moduli := #[7],
    requiredCommands := #["(ite ", "@FF7.sub", "@FF7.neg"] },
  { declaration := ``largeDistributive, moduli := #[curve25519] },
  { declaration := ``largeFalseIdentity, falsified := true, moduli := #[curve25519] },
  { declaration := ``independentCharacteristics, moduli := #[2, 7] },
  { declaration := ``independentCounterexample, falsified := true, moduli := #[2, 7] }
]

private def hasConcreteValue (text : String) (value modulus : Nat) : Bool :=
  contains text s!"#f{value}m{modulus}" ||
  contains text s!"(as ff{value} (_ FiniteField {modulus}))"

private def runCase (test : Case) : MetaM Unit := do
  let environment : TranslateEnv :=
    { (default : TranslateEnv) with optEnv.options.solverOptions := {
        solver := some .cvc5
        timeout := some 30
        solveResult := if test.falsified then .ExpectedFalsified else .ExpectedValid } }
  let ((result, _), finalEnvironment) ←
    (Translate.main (mkConst test.declaration)).run environment
  let state := finalEnvironment.smtEnv
  unless !state.nativeFieldQualified && state.singleSolver == some .cvc5 do
    throwError "{test.declaration}: native session was not retired"
  unless state.solverRecords.size == 1 do
    throwError "{test.declaration}: expected exactly one live solver record"
  let some record := state.solverRecords[0]?
    | throwError "{test.declaration}: missing live solver record"
  unless record.version == "offline capability-qualified" do
    throwError "{test.declaration}: solver was not qualified by native preflight"
  unless record.solver == .cvc5 && record.checkCommand.isSome do
    throwError "{test.declaration}: no actual cvc5 check-sat"
  unless record.failedStage.isNone do
    throwError "{test.declaration}: solver failure: {reprStr record.failedStage}"
  let expectedResponse := if test.falsified then "sat" else "unsat"
  unless record.stdout.any (fun response => response.trim == expectedResponse) do
    throwError "{test.declaration}: missing exact {expectedResponse} solver response"
  let commands := String.intercalate "\n" (state.smtCommands.toList.map toString)
  for modulus in test.moduli do
    unless contains commands s!"(_ FiniteField {modulus})" do
      throwError "{test.declaration}: missing native field {modulus}"
    unless state.sourceAssociations.any (fun entry =>
        entry.modulus == some modulus && entry.source.isFVar) do
      throwError "{test.declaration}: missing source variable for field {modulus}"
  for fragment in test.requiredCommands do
    unless contains commands fragment do
      throwError "{test.declaration}: missing translated operation {fragment}"
  match result with
  | .Valid =>
      if test.falsified then throwError "{test.declaration}: expected Falsified, got Valid"
  | .Falsified counterexample =>
      unless test.falsified do throwError "{test.declaration}: expected Valid, got Falsified"
      unless !counterexample.isEmpty &&
          counterexample.all (fun entry => !entry.isEmpty && !contains entry "unavailable") do
        throwError "{test.declaration}: missing concrete counterexample: {counterexample}"
      unless !record.modelCommands.isEmpty && !record.modelResponses.isEmpty do
        throwError "{test.declaration}: missing actual model request/response"
      let model := String.intercalate "\n" record.modelResponses.toList
      let rendered := String.intercalate "\n" counterexample
      if let some (value, modulus) := test.concreteValue then
        unless hasConcreteValue model value modulus && hasConcreteValue rendered value modulus do
          throwError "{test.declaration}: expected concrete field value {value} modulo {modulus}; got {model} / {rendered}"
  | .Undetermined => throwError "{test.declaration}: Undetermined is not accepted"

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
  withCheckedEvidence [``evidence2, ``evidence7, ``curve25519_evidence] do
    let mut sat := 0
    let mut unsat := 0
    for test in cases do
      runCase test
      if test.falsified then sat := sat + 1 else unsat := unsat + 1
    unless sat > 0 && unsat > 0 do
      throwError "Polynomial integration must execute nonzero live SAT and UNSAT cases"
    IO.println s!"TestsFF.Polynomial: executed {sat} SAT and {unsat} UNSAT live native polynomial cases"

run_cmd do
  for declaration in #[``evidence2, ``evidence7, ``curve25519_evidence] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected polynomial fixture axiom in {declaration}: {axiomName}"

end TestsFF.Polynomial
