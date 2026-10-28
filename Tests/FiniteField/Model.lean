import Blaster.Smt.Env

/-! Solver-independent model decoding and actual pipe/session lifecycle checks.
Shell children implement only the protocol responses under test; no solver or
proof acquisition is used. Native qualification is injected at this boundary. -/
namespace Test.FiniteFieldModel

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField
open Blaster.Smt.FiniteFieldModel

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def requireValue (symbol : String) (modulus value : Nat) (response : String) : IO Unit := do
  match decodeResponse symbol modulus response with
  | .ok actual =>
      unless actual == value do throw <| IO.userError s!"expected {value}, got {actual}"
  | .error diagnostic =>
      throw <| IO.userError s!"failed to decode {response}: {diagnostic}"

private def rejectValue (modulus : Nat) (response : String) : IO Unit := do
  match decodeResponse "x" modulus response with
  | .ok value => throw <| IO.userError s!"accepted invalid model as {value}"
  | .error diagnostic =>
      unless diagnostic.utf8ByteSize ≤ 160 do
        throw <| IO.userError "unbounded decoder diagnostic"

#eval do
  requireValue "x" 7 6 "((x #f6m7))"
  requireValue "x" 2 0 "((x #f0m2))"
  requireValue "x" 2 1 "((x #f1m2))"
  requireValue "x" 3 2 " \r\n( ( x\n #f2m3 ) ) \r\n"
  requireValue "|x y|" 7 6 "((|x y| #f6m7))"
  let p := 170141183460469231731687303715884105727
  requireValue "x" p (p - 1) s!"((x #f{p - 1}m{p}))"
  for raw in ["", "((x #f6m7)", "((x #f6m7)))", "((x #f6m7)) junk",
      "((y #f6m7))", "((x #f6m7) (y #f1m7))", "((x #f6m7 #f0m7))",
      "((x#f6m7))", "((x #f6m3))", "((x #f-1m7))", "((x #f7m7))",
      "((x #f8m7))", "((x #f+6m7))", "((x #fm7))", "((x #f6m))",
      "((x #f6m-7))", "((x #f６m7))", "((x #f6m7.0))",
      "((x (let ((v #f6m7)) v)))", "((x (ff.add #f1m7 #f5m7)))",
      "((x (as ff6 F)))", "((x (as ff6 (_ FiniteField 7))))",
      "((x (as ff6 (_ FiniteField 3))))", "((x ff6))",
      "(error \"no model\")", "sat"] do
    rejectValue 7 raw
  rejectValue 0 "((x #f0m0))"
  rejectValue 1 "((x #f0m1))"
  rejectValue 7 ("((x #f" ++ String.mk (List.replicate (maxResponseBytes + 1) '6') ++ "m7))")
  rejectValue 7 (String.mk (List.replicate (maxResponseBytes + 1) ' '))
  match decodeLiteral 7 "#f6m7" with
  | .ok 6 => pure ()
  | _ => throw <| IO.userError "literal boundary lost F7 representative 6"

-- The bounded reader preserves the next response and counts bytes, not lines.
#eval IO.FS.withTempDir fun directory => do
  let path := directory / "model"
  let first := " \r\n((|x (y)|\n #f6m7))\r\n"
  let second := "((z #f2m3))\n"
  IO.FS.writeFile path (first ++ second)
  let h ← IO.FS.Handle.mk path .read
  unless (← readResponse h) == first && (← readResponse h) == second do
    throw <| IO.userError "model reader consumed another variable's response"
  let short := "((x #f6m7))\n"
  let atLimit := String.mk (List.replicate (maxResponseBytes - short.utf8ByteSize) ' ') ++ short
  IO.FS.writeFile path atLimit
  let h ← IO.FS.Handle.mk path .read
  unless (← readResponse h) == atLimit do
    throw <| IO.userError "model reader rejected its exact byte boundary"
  for raw in ["((x #f6m7))", "((x #f6m7)\n", " " ++ atLimit,
      String.mk (List.replicate maxResponseBytes ' '),
      "((x #f6m7)) extra\n", "((x #f６m7))\n"] do
    IO.FS.writeFile path raw
    let h ← IO.FS.Handle.mk path .read
    let rejected ← try
      discard <| readResponse h
      pure false
    catch _ => pure true
    unless rejected do throw <| IO.userError "bounded reader accepted invalid response"

private def spawnChild (verdict response : String) : IO PipedChild :=
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c",
      "while IFS= read -r line; do case \"$line\" in " ++
      "'(check-sat)'*) " ++ (if verdict == "stall" then ":; " else s!"echo '{verdict}'; ") ++
      ";; '(get-value ('*) " ++
      (if response == "stall" then ":; "
       else if response == "eof" then "exit 18; "
       else s!"printf '%s\\n' '{response}'; ") ++
      ";; '(exit)') exit 0;; esac; done"]
    stdin := .piped, stdout := .piped, stderr := .piped }

private def residue (p : Nat) : Expr := mkApp (mkConst ``Residue) (mkRawNatLit p)

private def environment (sessions : Array SolverSession) (type : Expr)
    (claimedType : Option Expr := none) (modulus : Option Nat := some 7)
    (native := true) (generateCex := true) (mode : SolverMode := .single) : MetaM TranslateEnv :=
  withLocalDeclD `x type fun x => do
    let association : SourceAssociation := {
      symbol := mkNormalSymbol "x", userName := `x, source := x,
      type := claimedType.getD type, modulus, polarity := .negated,
      localContext := ← getLCtx, localInstances := ← getLocalInstances }
    return { (default : TranslateEnv) with
      optEnv.options.solverOptions := { solverMode := mode, generateCex }
      smtEnv.sessions := sessions
      smtEnv.configuredSolvers := sessions.map (·.solver)
      smtEnv.singleSolver := if mode == .single then sessions[0]?.map (·.solver) else none
      smtEnv.nativeFieldQualified := native
      smtEnv.sourceAssociations := #[association]
      smtEnv.topLevelVars := #[[(mkNormalSymbol "x", `x)]]
      smtEnv.solverRecords := sessions.map fun session =>
        { solver := session.solver, version := "fake", commandLine := "shell builtins", setupCommands := #[] } }

private def assertStopped (session : SolverSession) : MetaM Unit := do
  let output ← IO.Process.output { cmd := "/bin/kill", args := #["-0", toString session.process.pid] }
  unless output.exitCode != 0 do throwError "model path retained a live child"

private def run (env : TranslateEnv) : MetaM (Result × TranslateEnv) := do
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  try
    let result ← (withSmtSessionOwner checkSat).run env
    unless result.2.smtEnv.sessions.isEmpty && result.2.smtEnv.emitProc.isNone &&
        !result.2.smtEnv.nativeFieldQualified do
      throwError "model path retained session ownership"
    return result
  finally
    Core.setMessageLog saved
    for session in env.smtEnv.sessions do assertStopped session

private def checkModel (response : String) (expected : Option String)
    (type : Expr := residue 7) (claimedType : Option Expr := none)
    (modulus : Option Nat := some 7) (native := true) (generateCex := true) : MetaM Unit := do
  let child ← spawnChild "sat" response
  let sessions := #[{ solver := .cvc5, process := child }]
  let env ← environment sessions type claimedType modulus native generateCex
  let (result, finalEnv) ← run env
  let .Falsified values := result | throwError "optional model changed SAT: {reprStr result}"
  let some record := finalEnv.smtEnv.solverRecords[0]?
    | throwError "missing model session record"
  unless record.stdout.contains "sat\n" do throwError "missing producing session SAT"
  if !generateCex then
    unless values == [] && record.modelCommands.isEmpty && record.modelResponses.isEmpty do
      throwError "absent optional evidence was requested or synthesized"
  else if let some expected := expected then
    unless values == [s!"x: {expected}"] && record.failedStage.isNone do
      throwError "wrong source/type display: {values}; {record.failureResponse.getD ""}"
    unless record.modelCommands == #["(get-value (x))"] &&
        record.modelResponses == #[response ++ "\n"] do
      throwError "evidence lost producing session transcript"
  else
    unless values == ["x: <counterexample unavailable>"] do
      throwError "invalid model escaped as a value: {values}"
    let some diagnostic := record.failureResponse | throwError "missing model diagnostic"
    unless contains diagnostic "x:" && diagnostic.utf8ByteSize ≤ 256 &&
        record.failedStage == some "model evidence" do
      throwError "unbounded/missing per-variable model diagnostic: {diagnostic}"

#eval checkModel "((x #f6m7))" (some "(6 : Blaster.FiniteField.Residue 7) [#f6m7]")
#eval checkModel "((x #f2m7))" (some "(2 : Blaster.FiniteField.Residue 7) [#f2m7]")
#eval checkModel "((x #f1m2))" (some "(1 : Blaster.FiniteField.Residue 2) [#f1m2]") (residue 2) none (some 2)
#eval checkModel "((x #f2m3))" (some "(2 : Blaster.FiniteField.Residue 3) [#f2m3]") (residue 3) none (some 3)
#eval checkModel "((x #f6m7))" none (mkConst ``Nat)
#eval checkModel "((x #f6m7))" none (residue 7) (some (residue 3))
#eval checkModel "((x #f6m7))" none (residue 7) none (some 3)
#eval checkModel "((x #f6m7))" none (residue 7) none none
#eval checkModel "((x #f6m3))" none
#eval checkModel "((x #f-1m7))" none
#eval checkModel "((x #f7m7))" none
#eval checkModel "((x (let ((v #f6m7)) v)))" none
#eval checkModel "((x (as ff6 (_ FiniteField 7))))" none
#eval checkModel "((y #f6m7))" none
#eval checkModel "((x #f6m7)) trailing" none
#eval checkModel "((x #f6m7)" none
#eval checkModel ("((x #f" ++ String.mk (List.replicate (maxResponseBytes + 1) '6') ++ "m7))") none
#eval checkModel "eof" none
#eval checkModel "stall" none
#eval checkModel "stall" none (residue 7) none (some 7) true false
-- Ordinary raw handling, including let sharing, remains unchanged.
#eval checkModel "((x (let ((v 4)) (+ v v))))" (some "(let ((v 4)) (+ v v))") (mkConst ``Nat) none none false
#eval checkModel "((x true))" (some "true") (mkConst ``Bool) none none

-- Missing/ambiguous metadata is not permission to display an untyped FF value.
run_meta do
  for duplicate in [false, true] do
    let child ← spawnChild "sat" "((x #f6m7))"
    let env ← environment #[{ solver := .cvc5, process := child }] (residue 7)
    let associations := if duplicate then env.smtEnv.sourceAssociations ++ env.smtEnv.sourceAssociations else #[]
    let (result, finalEnv) ← run { env with smtEnv.sourceAssociations := associations }
    match result with
    | .Falsified ["x: <counterexample unavailable>"] => pure ()
    | _ => throwError "missing/ambiguous metadata changed SAT or allowed raw evidence"
    let some record := finalEnv.smtEnv.solverRecords[0]? | throwError "missing metadata failure record"
    unless record.modelCommands.isEmpty && record.failedStage == some "model evidence" do
      throwError "invalid metadata was used to request a model"

-- Keep earlier validated evidence, but do not reuse a failed frame for a later
-- variable or restart its solver after retirement.
run_meta do
  let child ← spawnChild "sat" "((x #f6m7))"
  let mut env ← environment #[{ solver := .cvc5, process := child }] (residue 7)
  for name in [`y, `z] do
    let association ← withLocalDeclD name (residue 7) fun source => do
      let association : SourceAssociation := {
        symbol := mkNormalSymbol (toString name), userName := name,
        source, type := residue 7, modulus := some 7, polarity := .negated,
        localContext := ← getLCtx, localInstances := ← getLocalInstances }
      pure association
    env := { env with
      smtEnv.sourceAssociations := env.smtEnv.sourceAssociations.push association
      smtEnv.topLevelVars := env.smtEnv.topLevelVars.push [(association.symbol, name)] }
  let (result, finalEnv) ← run env
  match result with
  | .Falsified ["x: (6 : Blaster.FiniteField.Residue 7) [#f6m7]",
      "y: <counterexample unavailable>", "z: <counterexample unavailable>"] => pure ()
  | _ => throwError "failed variable corrupted partial model evidence: {reprStr result}"
  let some record := finalEnv.smtEnv.solverRecords[0]? | throwError "missing partial model record"
  unless record.modelCommands == #["(get-value (x))", "(get-value (y))"] do
    throwError "model retrieval continued/restarted after invalid framing"
  let diagnostic := record.failureResponse.getD ""
  unless contains diagnostic "y:" && contains diagnostic "z:" && diagnostic.utf8ByteSize ≤ 512 do
    throwError "partial evidence lost bounded per-variable diagnostics"

-- First-mode evidence must come from the SAT producer, never its stalled peer.
run_meta do
  let loser ← spawnChild "stall" "((x #f1m7))"
  let winner ← spawnChild "sat" "((x #f6m7))"
  let sessions := #[{ solver := .z3, process := loser }, { solver := .cvc5, process := winner }]
  let env ← environment sessions (residue 7) none (some 7) true true .first
  let (result, finalEnv) ← run env
  match result with
  | .Falsified ["x: (6 : Blaster.FiniteField.Residue 7) [#f6m7]"] => pure ()
  | _ => throwError "first mode used another session's evidence: {reprStr result}"
  let some loserRecord := finalEnv.smtEnv.solverRecords[0]?
    | throwError "missing losing session record"
  let some winnerRecord := finalEnv.smtEnv.solverRecords[1]?
    | throwError "missing winning session record"
  unless loserRecord.modelCommands.isEmpty && loserRecord.modelResponses.isEmpty &&
      winnerRecord.modelResponses == #["((x #f6m7))\n"] do
    throwError "model evidence crossed session ownership"

end Test.FiniteFieldModel
