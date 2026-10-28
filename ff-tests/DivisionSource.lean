import Blaster

namespace TestsFF.Division

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

/-! Live FFM-18 regressions exercise the original total inverse/division source
through `Translate.main`. Both SAT and UNSAT must come from the staged,
offline-qualified cvc5 executable. Solver observations are not Lean proofs;
the separate source checks below are kernel-checked and audited for M1 axioms.
Graph witnesses must survive translation even under nested Boolean assumptions.
Run via `make test-cvc5-ff`; no download, PATH fallback, or skip is allowed. -/

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

-- The variable-dependent residuals prevent a closed arithmetic evaluation from
-- substituting for the required live translation and check-sat observation.
private def zeroInverse : Prop :=
  ∀ x : Residue 7, x + (0 : Residue 7)⁻¹ = x

private def divisionByZero : Prop :=
  ∀ x : Residue 7, x / 0 = 0

private def zeroOverZero : Prop :=
  ∀ x : Residue 7, x + (0 : Residue 7) / 0 = x

private def nonzeroSelfDivision : Prop :=
  ∀ x : Residue 7, x ≠ 0 → x / x = 1

private def unguardedSelfDivision : Prop :=
  ∀ x : Residue 7, x / x = 1

private def characteristicTwoInverse : Prop :=
  ∀ x : Residue 2, x⁻¹ = x

private def characteristicTwoDivision : Prop :=
  ∀ x : Residue 2, x ≠ 0 → x / x = 1

private def characteristicTwoUnguarded : Prop :=
  ∀ x : Residue 2, x / x = 1

private def distinctModuli : Prop :=
  ∀ (x : Residue 2) (y : Residue 7), x⁻¹ = x ∧ y⁻¹⁻¹ = y

private def distinctModuliFalse : Prop :=
  ∀ (x : Residue 2) (y : Residue 7), x / x = 1 ∨ y / y = 1

private def nestedInverse : Prop :=
  ∀ x : Residue 7, x⁻¹⁻¹ = x

private def denominatorOrder : Prop :=
  ∀ a : Residue 7, (a / 3) * 3 = a

-- 3/2 = 5, whereas 2/3 = 3: this must not become valid by swapping operands.
private def swappedDivision : Prop :=
  ∀ a : Residue 7, a / 3 = 3 / a

private def divisionAsMultiplication : Prop :=
  ∀ a b : Residue 7, a / b = a * b

private def inverseAlwaysZero : Prop :=
  ∀ x : Residue 7, x⁻¹ = 0

private def nestedBooleanAssumption : Prop :=
  ∀ a b : Residue 7,
    ((a / b = 0 ∨ a / b = 1) ∧ b ≠ 0) → a = 0 ∨ a = b

private def nestedBooleanFalse : Prop :=
  ∀ a b : Residue 7,
    ((a / b = 0 ∨ a / b = 1) ∧ b ≠ 0) → a = b

private def iteDivision : Prop :=
  ∀ a b : Residue 7,
    (if b = 0 then a / b else (a / b) * b) = (if b = 0 then 0 else a)

private def nestedIteAssumption : Prop :=
  ∀ a b : Residue 7,
    (if a = 0 then a / b else (if b = 0 then b / a else a / a)) = 0 →
      a = 0 ∨ b = 0

private def nestedIteFalse : Prop :=
  ∀ a b : Residue 7,
    (if a = 0 then a / b else (if b = 0 then b / a else a / a)) = 0 → a = 0

private def nestedImplicationAssumption : Prop :=
  ∀ x : Residue 7, (x / x = 0 → x = 0) → (x ≠ 0 → x / x = 1)

-- At zero the inner implication is true and the conclusion is false. A graph
-- asserted with goal polarity (or buried in the antecedent) can mask this SAT.
private def nestedImplicationFalse : Prop :=
  ∀ x : Residue 7, (x / x = 1 → x ≠ 0) → x / x = 1

-- These checks use the actual executable Residue inverse/division, not graph
-- witnesses, external solvers, native_decide, or fabricated field assumptions.
private theorem sourceZeroInverse : zeroInverse := by
  intro x
  rw [Residue.inv_zero, Lean.Grind.Semiring.add_zero]

private theorem sourceDivisionByZero : divisionByZero := by
  intro x
  rw [Residue.div_eq_mul_inv, Residue.inv_zero, Lean.Grind.Semiring.mul_zero]

private theorem sourceNonzeroSelf : nonzeroSelfDivision := by
  intro x hx
  exact Residue.mul_inv_cancel hx

private theorem sourceNestedInverse : nestedInverse := by
  intro x
  exact Residue.inv_inv x

private theorem sourceConcreteDivision :
    (0 : Residue 7) / 0 = 0 ∧ (2 : Residue 7) / 3 = 3 ∧
    (3 : Residue 7) / 2 = 5 ∧ (0 : Residue 2)⁻¹ = 0 ∧
    (1 : Residue 2)⁻¹ = 1 := by decide

private theorem sourceUnguardedFalse : ¬ unguardedSelfDivision := by
  intro h
  exact (by decide : (0 : Residue 7) / 0 ≠ 1) (h 0)

private theorem sourceCharacteristicTwoFalse : ¬ characteristicTwoUnguarded := by
  intro h
  exact (by decide : (0 : Residue 2) / 0 ≠ 1) (h 0)

private theorem sourceDistinctModuliFalse : ¬ distinctModuliFalse := by
  intro h
  exact (by decide : ¬ ((0 : Residue 2) / 0 = 1 ∨ (0 : Residue 7) / 0 = 1)) (h 0 0)

private theorem sourceSwappedFalse : ¬ swappedDivision := by
  intro h
  exact (by decide : (2 : Residue 7) / 3 ≠ 3 / 2) (h 2)

private theorem sourceMultiplicationFalse : ¬ divisionAsMultiplication := by
  intro h
  exact (by decide : (2 : Residue 7) / 3 ≠ 2 * 3) (h 2 3)

private theorem sourceInverseZeroFalse : ¬ inverseAlwaysZero := by
  intro h
  exact (by decide : (1 : Residue 7)⁻¹ ≠ 0) (h 1)

private theorem sourceBooleanFalse : ¬ nestedBooleanFalse := by
  intro h
  exact (by decide : (0 : Residue 7) ≠ 1) (h 0 1 (by decide))

private theorem sourceIteFalse : ¬ nestedIteFalse := by
  intro h
  exact (by decide : (1 : Residue 7) ≠ 0) (h 1 0 (by decide))

private theorem sourceImplicationFalse : ¬ nestedImplicationFalse := by
  intro h
  exact (by decide : (0 : Residue 7) / 0 ≠ 1) (h 0 (by decide))

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private structure Case where
  declaration : Name
  falsified : Bool := false
  moduli : Array Nat := #[7]
  requiredCommands : Array String := #[]

private def cases : Array Case := #[
  { declaration := ``zeroInverse },
  { declaration := ``divisionByZero },
  { declaration := ``zeroOverZero },
  { declaration := ``nonzeroSelfDivision },
  { declaration := ``unguardedSelfDivision, falsified := true },
  { declaration := ``characteristicTwoInverse, moduli := #[2] },
  { declaration := ``characteristicTwoDivision, moduli := #[2] },
  { declaration := ``characteristicTwoUnguarded, falsified := true, moduli := #[2] },
  { declaration := ``distinctModuli, moduli := #[2, 7] },
  { declaration := ``distinctModuliFalse, falsified := true, moduli := #[2, 7] },
  { declaration := ``nestedInverse },
  { declaration := ``denominatorOrder },
  { declaration := ``swappedDivision, falsified := true },
  { declaration := ``divisionAsMultiplication, falsified := true },
  { declaration := ``inverseAlwaysZero, falsified := true },
  { declaration := ``nestedBooleanAssumption },
  { declaration := ``nestedBooleanFalse, falsified := true },
  { declaration := ``iteDivision, requiredCommands := #["(ite "] },
  { declaration := ``nestedIteAssumption, requiredCommands := #["(ite "] },
  { declaration := ``nestedIteFalse, falsified := true, requiredCommands := #["(ite "] },
  { declaration := ``nestedImplicationAssumption },
  { declaration := ``nestedImplicationFalse, falsified := true }
]

private def runCase (executable : String) (test : Case) : MetaM Unit := do
  let environment : TranslateEnv :=
    { (default : TranslateEnv) with optEnv.options.solverOptions := {
        solver := some .cvc5
        timeout := some 30
        solveResult := if test.falsified then .ExpectedFalsified else .ExpectedValid } }
  let ((result, _), finalEnvironment) ←
    (Translate.main (mkConst test.declaration)).run environment
  let state := finalEnvironment.smtEnv
  unless state.sessions.isEmpty && state.emitProc.isNone &&
      !state.nativeFieldQualified && state.singleSolver == some .cvc5 do
    throwError "{test.declaration}: native division session was not retired"
  unless state.configuredSolvers == #[.cvc5] && state.solverRecords.size == 1 do
    throwError "{test.declaration}: expected exactly the staged cvc5 solver"
  let some record := state.solverRecords[0]?
    | throwError "{test.declaration}: missing live solver record"
  unless record.solver == .cvc5 && record.version == "offline capability-qualified" &&
      record.commandLine.startsWith (executable ++ " ") do
    throwError "{test.declaration}: solver was not the offline-qualified staged executable"
  let some checkCommand := record.checkCommand
    | throwError "{test.declaration}: no actual check-sat command"
  let expectedResponse := if test.falsified then "sat" else "unsat"
  unless toString checkCommand == "(check-sat)" &&
      record.stdout.any (fun response => response.trim == expectedResponse) do
    throwError "{test.declaration}: missing exact live {expectedResponse} response"
  unless record.failedStage.isNone && record.stderr.isEmpty do
    throwError "{test.declaration}: solver failure or unexpected stderr"
  let commands := String.intercalate "\n" (state.smtCommands.toList.map toString)
  unless contains commands "@ffinv" && contains commands "ff.mul" do
    throwError "{test.declaration}: missing inverse graph encoding"
  for modulus in test.moduli do
    unless contains commands s!"(_ FiniteField {modulus})" &&
        state.sourceAssociations.any (fun entry =>
          entry.modulus == some modulus && entry.source.isFVar) &&
        state.sourceAssociations.any (fun entry =>
          entry.modulus == some modulus && entry.inverseGraph.isSome) do
      throwError "{test.declaration}: missing typed source or inverse graph for field {modulus}"
  for fragment in test.requiredCommands do
    unless contains commands fragment do
      throwError "{test.declaration}: missing translated operation {fragment}"
  unless record.modelCommands.all (fun command => !contains command "(get-proof") do
    throwError "{test.declaration}: division observations must not request proofs"
  match result with
  | .Valid =>
      if test.falsified then throwError "{test.declaration}: expected Falsified, got Valid"
  | .Falsified counterexample =>
      unless test.falsified do throwError "{test.declaration}: expected Valid, got Falsified"
      unless !counterexample.isEmpty &&
          counterexample.all (fun entry => !entry.isEmpty && !contains entry "unavailable") &&
          !record.modelCommands.isEmpty && !record.modelResponses.isEmpty do
        throwError "{test.declaration}: missing actual concrete counterexample evidence"
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
  withCheckedEvidence [``evidence2, ``evidence7] do
    let mut sat := 0
    let mut unsat := 0
    for test in cases do
      runCase executable test
      if test.falsified then sat := sat + 1 else unsat := unsat + 1
    unless sat > 0 && unsat > 0 do
      throwError "Division integration must execute nonzero live SAT and UNSAT cases"
    IO.println s!"TestsFF.Division: executed {sat} SAT and {unsat} UNSAT live native inverse/division cases"

run_cmd do
  for declaration in #[``evidence2, ``evidence7, ``sourceZeroInverse,
      ``sourceDivisionByZero, ``sourceNonzeroSelf, ``sourceNestedInverse,
      ``sourceConcreteDivision, ``sourceUnguardedFalse, ``sourceCharacteristicTwoFalse,
      ``sourceDistinctModuliFalse, ``sourceSwappedFalse, ``sourceMultiplicationFalse,
      ``sourceInverseZeroFalse, ``sourceBooleanFalse, ``sourceIteFalse,
      ``sourceImplicationFalse] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected division fixture axiom in {declaration}: {axiomName}"

end TestsFF.Division
