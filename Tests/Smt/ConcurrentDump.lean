import Blaster

namespace Test.ConcurrentDump

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def ownedOutput (args : IO.Process.SpawnArgs) : IO String := do
  let output ← OwnedProcess.output args ((← IO.monoMsNow) + 30000)
  unless output.exitCode == 0 do
    throw <| IO.userError s!"{args.cmd} failed:\n{output.stdout}\n{output.stderr}"
  return output.stdout

private def source : String :=
  "import Blaster\n" ++
  "#blaster (solver-mode: agree) (dump-smt-lib: 1) (solve-result: 1) [∀ (x : Int), x ≠ 3]\n"

private def testLabeledTranscripts : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr source
    handle.flush
    let output ← ownedOutput { cmd := "lake", args := #["lean", path.toString] }
    for expected in ["SMT Query [z3]:", "SMT Query [cvc5]:", "(check-sat)", "(exit)"] do
      unless contains output expected do
        throw <| IO.userError s!"concurrent dump omitted {expected}\n{output}"

private def bmcSource : String :=
  "import Blaster\nimport Blaster.StateMachine\n" ++
  "open Blaster.StateMachine\n" ++
  "instance counter : StateMachine Int Int where\n" ++
  "  init input := input\n  next input _ := input\n" ++
  "  assumptions input _ := 0 ≤ input\n  invariants _ state := 0 ≤ state\n" ++
  "#bmc (solver-mode: agree) (dump-smt-lib: 1) (max-depth: 2) [counter]\n"

private def testBmcDumpUsesCurrentAssumptions : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr bmcSource
    handle.flush
    let output ← ownedOutput { cmd := "lake", args := #["lean", path.toString] }
    let checks := (output.splitOn "\n").filter (·.startsWith "(check-sat-assuming")
    unless checks.length ≥ 4 do
      throw <| IO.userError s!"BMC dump omitted incremental checks:\n{output}"
    let firstZ3 := checks[0]!
    let firstCvc5 := checks[1]!
    let secondZ3 := checks[2]!
    let secondCvc5 := checks[3]!
    unless firstZ3 == firstCvc5 && secondZ3 == secondCvc5 && firstZ3 != secondZ3 do
      throw <| IO.userError s!"BMC dumps used stale or backend-divergent assumptions: {checks}"

private def transcript (record : SolverRecord) (canonical : Array SmtCommand) : String :=
  let check := record.checkCommand.map (fun command => [toString command]) |>.getD []
  String.intercalate "\n" <|
    record.setupCommands.toList.map toString ++ canonical.toList.map toString ++
    check ++ record.modelCommands.toList ++ ["(exit)"]

private def runTranscript (solver : SmtSolver) (contents : String) : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr (contents ++ "\n")
    handle.flush
    let output ←
      match solver with
      | .z3 => ownedOutput { cmd := "z3", args := #["-smt2", path.toString] }
      | .cvc5 => ownedOutput {
          cmd := "cvc5"
          args := #[
            "--lang", "smt2", "--incremental", "--parsing-mode=lenient",
            "--dt-nested-rec", path.toString
          ]
        }
    unless (output.splitOn "\n").contains "sat" do
      throw <| IO.userError
        s!"{solver} transcript did not reproduce sat\n{contents}\nstdout:\n{output}"

private def testExactIncrementalTranscripts : MetaM Unit := do
  let base : TranslateEnv := default
  let options : BlasterOptions := { solverMode := .agree, generateCex := true }
  let env := {
    base with
    optEnv.options := { base.optEnv.options with solverOptions := options }
  }
  let flagSymbol := mkNormalSymbol "flag"
  let flag := smtSimpleVarId flagSymbol
  let firstCommand := SmtCommand.checkSatAssuming #[flag]
  let secondCommand := SmtCommand.checkSatAssuming #[notSmt flag]
  let (firstChecks, finalEnv) ← (withSmtSessionOwner do
    setBlasterProcess
    declareConst flagSymbol boolSort
    discard <| checkSatAssuming #[flag]
    let firstChecks := (← get).smtEnv.solverRecords.map fun record =>
      record.checkCommand.map toString |>.getD "<none>"
    discard <| checkSatAssuming #[notSmt flag]
    return firstChecks).run env
  let expectedFirst := toString firstCommand
  let expectedSecond := toString secondCommand
  unless firstChecks.size == 2 && firstChecks.all (· == expectedFirst) do
    throwError "first check transcript mismatch: {firstChecks}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "transcript test owner left solver sessions active"
  let records := finalEnv.smtEnv.solverRecords
  unless records.size == 2 do throwError "expected two solver records, got {records.size}"
  for record in records do
    unless record.checkCommand.map toString == some expectedSecond do
      throwError "{record.solver} retained a stale check command: {record.checkCommand}"
    unless record.modelCommands.size == 1 && record.modelResponses.size == 1 do
      throwError "{record.solver} retained stale model work: commands={record.modelCommands}, responses={record.modelResponses}"
    let saved := transcript record finalEnv.smtEnv.smtCommands
    unless contains saved expectedSecond && !contains saved expectedFirst do
      throwError "{record.solver} transcript did not isolate the second check:\n{saved}"
    runTranscript record.solver saved

-- All subprocesses (including fresh replay controls) have the production owner.
-- A broken barrier is bounded, and assertion failures still retire every child.
private def awaitOwned (task : Task (Except IO.Error α)) : IO α := do
  let deadline := (← IO.monoMsNow) + 30000
  while !(← IO.hasFinished task) do
    if (← IO.monoMsNow) ≥ deadline then
      throw <| IO.userError "restart regression subprocess exceeded 30s"
    IO.sleep 5
  IO.ofExcept (← IO.wait task)


private def restartMachineSource (mode : String) : String :=
  "import Blaster\nimport Blaster.StateMachine\nopen Blaster.StateMachine\n" ++
  "instance restartCounter : StateMachine Int Int where\n" ++
  "  init input := input * input\n" ++
  "  next _ state := state + 1\n" ++
  "  assumptions _ _ := True\n" ++
  "  invariants _ state := state ≠ -1\n" ++
  (if mode == "bmc" then
    "#bmc (solver-mode: first) (dump-smt-lib: 1) (max-depth: 3) [restartCounter]\n"
   else
    "#kind (solver-mode: first) (dump-smt-lib: 1) (max-depth: 3) (solve-result: 2) [restartCounter]\n")

private def restartEvidenceSource : String :=
  "import Blaster\nopen Lean Blaster.Options Blaster.Optimize Blaster.Smt\n" ++
  "def currentEvidence : MetaM Unit := do\n" ++
  "  let base : TranslateEnv := default\n" ++
  "  let env := { base with optEnv.options.solverOptions := { solverMode := .first, generateCex := true } }\n" ++
  "  let symbol := mkNormalSymbol \"restartFlag\"\n" ++
  "  let flag := smtSimpleVarId symbol\n" ++
  "  let (_, finalEnv) ← (withSmtSessionOwner do\n" ++
  "    setBlasterProcess\n" ++
  "    declareConst symbol boolSort\n" ++
  "    assertTerm (orSmt flag (notSmt flag))\n" ++
  "    for assumption in [flag, notSmt flag, flag] do\n" ++
  "      let result ← checkSatAssuming #[assumption]\n" ++
  "      unless isFalsifiedResult result do throwError \"current assumption was not sat\"\n" ++
  "      let records := (← get).smtEnv.solverRecords\n" ++
  "      let expected := toString (SmtCommand.checkSatAssuming #[assumption])\n" ++
  "      unless records.all (fun record => record.checkCommand.map toString == some expected) do\n" ++
  "        throwError \"stale current assumption in solver records\"\n" ++
  "      let evidence := records.filter (fun record => !record.modelCommands.isEmpty)\n" ++
  "      unless evidence.size == 1 do throwError \"stale evidence survived a restart\"\n" ++
  "      let some record := evidence[0]? | throwError \"missing winning evidence\"\n" ++
  "      unless record.modelCommands.size == 1 && record.modelResponses.size == 1 do\n" ++
  "        throwError \"current model work was accumulated across checks\"\n" ++
  "      let expectedValue := if toString assumption == toString flag then \"true\" else \"false\"\n" ++
  "      unless ((record.modelResponses[0]!).splitOn expectedValue).length > 1 do\n" ++
  "        throwError \"model did not satisfy the current assumption\"\n" ++
  "    ).run env\n" ++
  "  unless finalEnv.smtEnv.sessions.isEmpty do throwError \"owner left live sessions\"\n" ++
  "#eval currentEvidence\n"

private def testForcedRestarts (mode : String) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let fixture := (← IO.currentDir) / "Tests" / "Smt" / "restart-solver.py"
    let controller ← OwnedProcess.spawn {
      cmd := "python3", args := #[fixture.toString, "serve", directory.toString, mode]
    }
    try
      let ready ← controller.asTask controller.stdout.getLine
      unless (← awaitOwned ready).trim == "ready" do
        throw <| IO.userError "restart controller failed before readiness"
      let sourcePath := directory / "Restart.lean"
      IO.FS.writeFile sourcePath
        (if mode == "evidence" then restartEvidenceSource else restartMachineSource mode)
      let originalPath := (← IO.getEnv "PATH").getD ""
      let output ← ownedOutput {
        cmd := "lake"
        args := #["lean", sourcePath.toString]
        env := #[("PATH", some s!"{directory}:{originalPath}")]
      }
      if mode != "evidence" then
        unless contains output "(check-sat-assuming" do
          throw <| IO.userError s!"{mode} goal never reached an SMT check:\n{output}"
      let finish ← controller.asTask do
        controller.stdin.putStr "finish\n"
        controller.stdin.flush
        controller.stdout.getLine
      unless (← awaitOwned finish).trim == "finished" do
        let stderr ← controller.cleanup true
        throw <| IO.userError s!"{mode} restart/phase assertions failed:\n{stderr}"
      let manifest ← IO.FS.readFile (directory / "manifest")
      for row in manifest.splitOn "\n" do
        let fields := row.splitOn " "
        let backend := fields[0]!
        let stem := fields[1]!
        let path := directory / s!"{stem}.smt2"
        let args := if backend == "z3" then #["-smt2", path.toString] else
          #["--lang", "smt2", "--incremental", "--parsing-mode=lenient",
            "--dt-nested-rec", path.toString]
        let fresh ← ownedOutput { cmd := backend, args }
        IO.FS.writeFile (directory / s!"{stem}.fresh") fresh
      let compared ← ownedOutput {
        cmd := "python3", args := #[fixture.toString, "compare", directory.toString, mode]
      }
      unless compared.trim == "verified" do
        throw <| IO.userError s!"{mode} fresh replay comparison failed: {compared}"
    finally
      discard <| controller.cleanup true

private def testQuotedModelTerms : MetaM Unit := do
  let text := "a\"b\\c\nd\r"
  for solver in [SmtSolver.z3, .cvc5] do
    for (sort, term, expected) in
        [(intSort, natLitSmt 7, "7"), (stringSort, strLitSmt text, text.quote)] do
      let base : TranslateEnv := default
      let env := { base with optEnv.options.solverOptions := {
        solver := some solver, generateCex := true } }
      let symbol := mkNormalSymbol "quoted (value"
      let (result, finalEnv) ← (withSmtSessionOwner do
        setBlasterProcess
        declareConst symbol sort
        assertTerm (eqSmt (smtSimpleVarId symbol) term)
        modify fun env => { env with smtEnv.topLevelVars := #[[(symbol, `quotedValue)]] }
        checkSat).run env
      match result with
      | .Falsified [actual] =>
          unless actual == s!"quotedValue: {expected}" do
            throwError "model changed the forced value: {actual}, expected {expected}"
      | other => throwError "quoted identifier lost usable evidence: {reprStr other}"
      let some record := finalEnv.smtEnv.solverRecords[0]?
        | throwError "quoted model query never reached a solver"
      unless record.modelResponses.any (contains · "|quoted (value|") && record.failedStage.isNone do
        throwError "quoted model was not complete real solver evidence: {reprStr record.modelResponses}"

#eval testQuotedModelTerms

#eval testLabeledTranscripts
#eval testBmcDumpUsesCurrentAssumptions
#eval testExactIncrementalTranscripts
#eval testForcedRestarts "bmc"
#eval testForcedRestarts "kind"
#eval testForcedRestarts "evidence"

end Test.ConcurrentDump
