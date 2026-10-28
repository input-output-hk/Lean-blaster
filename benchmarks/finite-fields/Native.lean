/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Blaster
import Tests.FiniteField.LargePrime

namespace FFM20.Native

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField
open Test.FiniteFieldLargePrime

-- These are proved nominal instances, not field laws supplied as assumptions.
private instance evidence7 : PrimeModulus 7 :=
  ⟨prime_of_bounded 7 2 (by decide) (by decide) (by decide)⟩
private instance : NeZero curve25519 := ⟨by decide⟩
private instance evidenceCurve : PrimeModulus curve25519 := curve25519_evidence

-- Direct variables replace the finitely used Context slots in the parent corpus.
private def square : Prop := ∀ x y : Residue 7,
  (x + y) ^ (2 : Nat) = x ^ (2 : Nat) + 2 * (x * y) + y ^ (2 : Nat)
private def falseGoal : Prop := ∀ x : Residue 7, x = x + 1
private def largeIdentity : Prop := ∀ x : Residue curve25519,
  (x + 1) * (x - 1) = x ^ (2 : Nat) - 1
private def fiveConstraints : Prop := ∀ x y m s : Residue 7,
  x = 2 ∧ y = 3 ∧ m = x * y ∧ s = m + x ∧ s = 0 → False
private def chain : Prop := ∀ x y u v w t z a b out : Residue curve25519,
  u = x + y ∧ v = u * x ∧ w = v + y ∧ t = w * x ∧
    z = t + y ∧ a = z * x ∧ b = a + y ∧ out = b * x →
  out = x ^ (5 : Nat) + x ^ (4 : Nat) * y + x ^ (3 : Nat) * y +
    x ^ (2 : Nat) * y + x * y
private def selfDivision : Prop := ∀ x : Residue 7, x ≠ 0 → x / x = 1
private def representation : Prop := ∀ x : Residue 7, x.rep.val < 3
private def wrap : Prop := (5 : Residue 7) + 3 = 1

-- Independent source check, not reconstruction of the solver result. The
-- historical modulus/source remains absent: this is explicitly a new F7 probe.
private theorem sourceSelfDivision : selfDivision := by
  intro x hx
  exact Residue.mul_inv_cancel hx

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def withCheckedEvidence (declarations : List Name) (action : MetaM Unit) : MetaM Unit :=
  match declarations with
  | [] => action
  | declaration :: rest => do
      let proof := mkConst declaration
      withLetDecl declaration (← inferType proof) proof fun _ =>
        withCheckedEvidence rest action

private def unavailable (reason : String) : Json :=
  Json.mkObj [("seconds", Json.null), ("reason", toJson reason)]

private def traceStage (label : String) : Json :=
  Json.mkObj [("source", toJson "Blaster.Logging.profileTask / stdout"),
    ("label", toJson label), ("resolution_ms", toJson (1 : Nat))]

private def commonMetrics (id route : String) : List (String × Json) := [
  ("case", toJson id), ("category", toJson "native-pipeline"),
  ("route", toJson route),
  ("proof_expr_nodes", Json.null),
  ("proof_expr_nodes_reason", toJson "Translate.main returns a verdict and optimized expression, not a reconstructed proof."),
  ("proof_reading", unavailable "Production native proof reading is unavailable."),
  ("proof_checking", unavailable "No native solver proof is reconstructed or kernel checked."),
  ("verified_transport", unavailable "No verified transport from native solver status to a Lean theorem."),
  ("value_display", unavailable "Not independently instrumented; model extraction is included in Solve and rendering is outside that trace."),
  ("solver_only", unavailable "Solve includes solver protocol and optional model extraction; no independent solver-only timer is retained."),
  ("preflight", unavailable "Capability qualification/process setup has no separate production timer."),
  ("axiom_audit", toJson "Checked source/evidence declarations against propext, Classical.choice, Quot.sound; solver verdict is not a theorem.")]

private def runCase (id : String) : MetaM Unit := do
  let (declaration, modulus, falsified, allowOptimizer, unsupported) ←
    match id with
    | "native-f7-square" => pure (``square, 7, false, false, false)
    | "native-f7-false" => pure (``falseGoal, 7, true, false, false)
    | "native-curve25519-identity" => pure (``largeIdentity, curve25519, false, false, false)
    | "native-f7-circuit" => pure (``fiveConstraints, 7, false, true, false)
    | "native-curve25519-circuit" => pure (``chain, curve25519, false, true, false)
    | "native-f7-self-division" => pure (``selfDivision, 7, false, false, false)
    | "native-unsupported-representation" => pure (``representation, 7, false, false, true)
    | "native-f7-closed-wrap" => pure (``wrap, 7, false, true, false)
    | _ => throwError "unknown FFM20_NATIVE_CASE: {id}"
  let environment : TranslateEnv :=
    { (default : TranslateEnv) with optEnv.options.solverOptions := {
        solver := some .cvc5, timeout := some 20, verbose := 1,
        solveResult := if falsified then .ExpectedFalsified else .ExpectedValid } }
  -- Catch inside the state transformer to retain the rejection transcript.
  let action : TranslateEnvT (Except String (Result × Expr)) := do
    try
      return .ok (← Translate.main (mkConst declaration))
    catch error =>
      return .error (← error.toMessageData.toString)
  let (outcome, finalEnvironment) ← action.run environment
  let state := finalEnvironment.smtEnv
  let commands := String.intercalate "\n" (state.smtCommands.toList.map toString)
  match outcome with
  | .error message =>
      unless unsupported && contains message "unsupported" do
        throwError "{id}: unexpected pipeline error: {message}"
      unless state.solverRecords.all (fun record => record.checkCommand.isNone) do
        throwError "unsupported representation reached check-sat"
      unless !(contains commands "(assert ") do
        throwError "unsupported representation emitted a query assertion"
      IO.println s!"FFM20_UNSUPPORTED {id}: {message}"
      IO.println ("FFM20_METRIC " ++ (Json.mkObj (commonMetrics id "unsupported" ++ [
        ("optimization", unavailable "Admission rejected during optimization; no completed End trace."),
        ("translation", unavailable "Rejected before translation."),
        ("solving", unavailable "Unsupported representation rejected before check-sat."),
        ("diagnostic", toJson message), ("smt_commands", toJson commands),
        ("solver_record_count", toJson state.solverRecords.size)])).compress)
  | .ok (result, _) =>
      if unsupported then throwError "unsupported representation was accepted"
      match result with
      | .Valid => if falsified then throwError "expected Falsified, got Valid"
      | .Falsified _ => unless falsified do throwError "expected Valid, got Falsified"
      | .Undetermined => throwError "Undetermined is not an accepted result"
      if state.solverRecords.isEmpty then
        unless allowOptimizer && isValidResult result do
          throwError "{id}: required native check-sat was bypassed"
        IO.println s!"FFM20_OPTIMIZER_ONLY {id}"
        IO.println ("FFM20_METRIC " ++ (Json.mkObj (commonMetrics id "optimizer-only" ++ [
          ("optimization", traceStage "Optimization"),
          ("translation", unavailable "Optimizer discharged the goal before translation."),
          ("solving", unavailable "Optimizer discharged the goal; no solver session."),
          ("result", toJson "Valid"), ("smt_commands", toJson commands)])).compress)
      else
        unless state.solverRecords.size == 1 do throwError "expected one solver record"
        let some record := state.solverRecords[0]? | throwError "missing solver record"
        unless record.solver == .cvc5 && record.version == "offline capability-qualified" &&
            record.checkCommand.isSome && record.failedStage.isNone do
          throwError "{id}: no successful qualified native cvc5 check-sat"
        let response := if falsified then "sat" else "unsat"
        unless record.stdout.any (fun text => text.trim == response) do
          throwError "{id}: missing exact {response} response"
        unless contains commands s!"(_ FiniteField {modulus})" do
          throwError "{id}: no native FiniteField sort"
        if id == "native-f7-closed-wrap" then
          -- The translator records the nominal sort itself, even without variables.
          unless state.sourceAssociations.all (fun entry => !entry.source.isFVar) do
            throwError "{id}: a closed constant identity acquired a variable association"
        else
          unless state.sourceAssociations.any (fun entry =>
              entry.modulus == some modulus && entry.source.isFVar) do
            throwError "{id}: no typed nominal source association"
        if falsified then
          unless !record.modelCommands.isEmpty && !record.modelResponses.isEmpty do
            throwError "{id}: missing actual get-value request/response"
          let .Falsified counterexample := result | throwError "missing falsified result"
          unless !counterexample.isEmpty &&
              counterexample.all (fun value => !value.isEmpty && !contains value "unavailable") do
            throwError "{id}: counterexample display unavailable"
        unless state.sessions.isEmpty && !state.nativeFieldQualified do
          throwError "{id}: native solver session was not retired"
        IO.println s!"FFM20_NATIVE_CHECK {id} {response}"
        IO.println ("FFM20_METRIC " ++ (Json.mkObj (commonMetrics id "native-cvc5" ++ [
          ("optimization", traceStage "Optimization"),
          ("translation", traceStage "Translation"),
          ("submission", traceStage "Submitting Smt Query"),
          ("solving", traceStage "Solve"),
          ("result", toJson response),
          ("counterexample_display", toJson (match result with
            | .Falsified values => values
            | _ => [])),
          ("solver_command_line", toJson record.commandLine),
          ("check_command", toJson (record.checkCommand.map toString)),
          ("smt_commands", toJson commands),
          ("solver_stdout", toJson record.stdout), ("solver_stderr", toJson record.stderr),
          ("model_commands", toJson record.modelCommands),
          ("model_responses", toJson record.modelResponses)])).compress)

run_cmd do
  for declaration in #[``evidence7, ``evidenceCurve, ``sourceSelfDivision,
      ``square, ``falseGoal, ``largeIdentity, ``fiveConstraints, ``chain,
      ``selfDivision, ``representation, ``wrap] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected native harness source axiom {axiomName} in {declaration}"

run_meta do
  let some executable ← IO.getEnv "BLASTER_FF_CVC5"
    | throwError "BLASTER_FF_CVC5 must name the staged solving executable"
  unless executable.startsWith "/" && (← (System.FilePath.mk executable).pathExists) do
    throwError "BLASTER_FF_CVC5 must be an existing absolute path"
  let some id ← IO.getEnv "FFM20_NATIVE_CASE"
    | throwError "FFM20_NATIVE_CASE must select exactly one native benchmark"
  withCheckedEvidence [``evidence7, ``evidenceCurve] (runCase id)

end FFM20.Native
