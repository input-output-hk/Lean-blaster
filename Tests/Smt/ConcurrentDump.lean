import Blaster

namespace Test.ConcurrentDump

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def source : String :=
  "import Blaster\n" ++
  "#blaster (solver-mode: agree) (dump-smt-lib: 1) (solve-result: 1) [∀ (x : Int), x ≠ 3]\n"

private def testLabeledTranscripts : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr source
    handle.flush
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #[path.toString]
    }
    unless output.exitCode == 0 do
      throw <| IO.userError <| "concurrent dump subprocess failed\n" ++ output.stdout ++ output.stderr
    for expected in ["SMT Query [z3]:", "SMT Query [cvc5]:", "(check-sat)", "(exit)"] do
      unless contains output.stdout expected do
        throw <| IO.userError s!"concurrent dump omitted {expected}\n{output.stdout}"

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
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #[path.toString]
    }
    unless output.exitCode == 0 do
      throw <| IO.userError <| "BMC dump subprocess failed\n" ++ output.stdout ++ output.stderr
    let checks := (output.stdout.splitOn "\n").filter (·.startsWith "(check-sat-assuming")
    unless checks.length ≥ 4 do
      throw <| IO.userError s!"BMC dump omitted incremental checks:\n{output.stdout}"
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
      | .z3 => IO.Process.output { cmd := "z3", args := #["-smt2", path.toString] }
      | .cvc5 => IO.Process.output {
          cmd := "cvc5"
          args := #[
            "--lang", "smt2", "--incremental", "--parsing-mode=lenient",
            "--dt-nested-rec", path.toString
          ]
        }
    unless output.exitCode == 0 do
      throw <| IO.userError
        s!"{solver} rejected saved transcript\n{contents}\nstdout:\n{output.stdout}\nstderr:\n{output.stderr}"
    unless (output.stdout.splitOn "\n").contains "sat" do
      throw <| IO.userError
        s!"{solver} transcript did not reproduce sat\nstdout:\n{output.stdout}\nstderr:\n{output.stderr}"

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

#eval testLabeledTranscripts
#eval testBmcDumpUsesCurrentAssumptions
#eval testExactIncrementalTranscripts

end Test.ConcurrentDump
