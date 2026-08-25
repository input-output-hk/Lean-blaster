import Blaster.Smt.Env

namespace Test.CrashLifecycle

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def spawnFakeChild
    (response : String) (delaySeconds : String := "0")
    (modelDelaySeconds : String := "0") (stderr : String := "")
    (closeStdout : Bool := false) (modelResponse : String := "()") : IO PipedChild := do
  let afterRead :=
    if closeStdout then
      s!"echo '{stderr}' >&2; exec 1>&-; sleep 10"
    else
      s!"sleep {delaySeconds}; echo '{response}'; " ++
      "while IFS= read -r line; do " ++
      s!"case \"$line\" in '(get-model)') sleep {modelDelaySeconds}; echo '{modelResponse}';; " ++
      "'(get-value ('*) echo '((x 0))';; '(exit)') exit 0;; esac; done"
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", "IFS= read -r first; " ++ afterRead]
    stdin := .piped
    stdout := .piped
    stderr := .piped
    setsid := true
  }

private def spawnDeadChild (stderr : String) : IO PipedChild :=
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", s!"echo '{stderr}' >&2; exit 17"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
    setsid := true
  }

private def record (solver : SmtSolver) : SolverRecord :=
  { solver, version := "fake 1.0", commandLine := s!"fake-{solver}", setupCommands := #[] }

private def environment
    (mode : SolverMode) (sessions : Array SolverSession)
    (generateCex : Bool := false) : TranslateEnv :=
  let base : TranslateEnv := default
  let options : BlasterOptions := { solverMode := mode, generateCex }
  let optEnv := { base.optEnv with options := { base.optEnv.options with solverOptions := options } }
  let smtEnv := {
    base.smtEnv with
    sessions
    configuredSolvers := if mode == .single then #[.z3] else #[.z3, .cvc5]
    singleSolver := if mode == .single then some .z3 else none
    solverRecords := sessions.map fun session => record session.solver
  }
  { base with optEnv, smtEnv }

private def processAlive (process : PipedChild) : IO Bool := do
  let output ← IO.Process.output {
    cmd := "/bin/kill"
    args := #["-0", toString process.pid]
  }
  return output.exitCode == 0

private def assertStopped (label : String) (process : PipedChild) : MetaM Unit := do
  if ← processAlive process then
    throwError "{label}: solver process {process.pid} remained alive"

private def runFirst
    (z3 cvc5 : PipedChild) (generateCex : Bool := false) : MetaM (Result × TranslateEnv) := do
  let env := environment .first #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    generateCex
  (do
    let result ← checkSat
    discard exitSmt
    return result).run env

private def expectValid (label : String) : Result → MetaM Unit
  | .Valid => pure ()
  | result => throwError "{label}: expected Valid, got {reprStr result}"

private def testZ3WinsAndCvc5IsReaped : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (result, _) ← runFirst z3 cvc5
  expectValid "z3 winner" result
  assertStopped "z3 winner" z3
  assertStopped "cvc5 loser" cvc5

private def testCvc5WinsAndZ3IsReaped : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat"
  let (result, _) ← runFirst z3 cvc5
  expectValid "cvc5 winner" result
  assertStopped "z3 loser" z3
  assertStopped "cvc5 winner" cvc5

private def testClosedStdoutDoesNotBeatDecisiveSolver : MetaM Unit := do
  let usefulStderr := "FAKE_CLOSED_STDOUT: deliberate stderr"
  let z3 ← spawnFakeChild "" "0" "0" usefulStderr true
  let cvc5 ← spawnFakeChild "unsat" "0.05"
  let (result, finalEnv) ← runFirst z3 cvc5
  expectValid "closed stdout fallback" result
  let stderr := finalEnv.smtEnv.solverRecords.find? (·.solver == .z3)
    |>.map (fun record => String.intercalate "\n" record.stderr.toList) |>.getD ""
  unless contains stderr usefulStderr do
    throwError "failing child stderr was not preserved: {stderr}"
  assertStopped "closed child" z3
  assertStopped "decisive child" cvc5

private def observeSingleCrash (process : PipedChild) : MetaM (String × Bool) := do
  let env := environment .single #[{ solver := .z3, process }]
  let (message, finalEnv) ← (do
    let message ←
      try
        discard checkSat
        pure "solver unexpectedly returned a result"
      catch error : Exception => error.toMessageData.toString
    discard exitSmt
    return message).run env
  return (message, finalEnv.smtEnv.sessions.isEmpty)

private def testCrashPreservesStderrWithoutDuplicateCleanup : MetaM Unit := do
  let usefulStderr := "FAKE_LIVE_CHILD: deliberate stderr"
  let live ← spawnFakeChild "" "0" "0" usefulStderr true
  let (message, cleared) ← observeSingleCrash live
  unless contains message "closed stdout" do
    throwError "contextual solver EOF error was lost: {message}"
  unless contains message usefulStderr do
    throwError "solver stderr was lost: {message}"
  if contains message "no such process" || contains message "No such process" then
    throwError "duplicate cleanup masked the original failure: {message}"
  unless cleared do throwError "retired solver remained in session state"
  assertStopped "crashed child" live

private def testAlreadyExitedChildIsHandled : MetaM Unit := do
  let usefulStderr := "FAKE_DEAD_CHILD: deliberate stderr"
  let dead ← spawnDeadChild usefulStderr
  let (message, cleared) ← observeSingleCrash dead
  unless contains message "closed stdout" && contains message usefulStderr do
    throwError "already-exited solver diagnostics were lost: {message}"
  unless cleared do throwError "already-exited solver remained in session state"
  assertStopped "already-exited child" dead

private def testModelFailurePreservesSatVerdict : MetaM Unit := do
  let process ← spawnFakeChild "sat" "0" "0" "" false "(error \"model unavailable\")"
  let env := environment .single #[{ solver := .z3, process }] true
  let (result, finalEnv) ← (do
    let result ← checkSat
    discard exitSmt
    return result).run env
  match result with
  | .Falsified _ => pure ()
  | other => throwError "model failure erased sat verdict: {reprStr other}"
  let rawModels := finalEnv.smtEnv.solverRecords.find? (·.solver == .z3)
    |>.map (fun record => String.intercalate "\n" record.modelResponses.toList) |>.getD ""
  unless contains rawModels "model unavailable" do
    throwError "raw failed model response was not preserved: {rawModels}"
  assertStopped "model-failed child" process

private def runCancelled
    (z3 cvc5 : PipedChild) (modelExtraction : Bool) : MetaM (String × TranslateEnv) := do
  let token ← IO.CancelToken.new
  let cancellation ← BaseIO.asTask do
    IO.sleep (if modelExtraction then 100 else 50)
    token.set
  let env := environment .first #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    modelExtraction
  let result ← withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
    (do
      let message ←
        try
          discard checkSat
          pure "solver unexpectedly ignored cancellation"
        catch error : Exception => error.toMessageData.toString
      discard exitSmt
      return message).run env
  let _ := cancellation.get
  return result

private def testCancellationReapsBothChildren : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (message, finalEnv) ← runCancelled z3 cvc5 false
  unless contains message "interrupted" || contains message "cancel" do
    throwError "cancellation exception was lost: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "cancellation left owned sessions in state"
  assertStopped "cancelled z3" z3
  assertStopped "cancelled cvc5" cvc5

private def testCancellationDuringModelExtraction : MetaM Unit := do
  let z3 ← spawnFakeChild "sat" "0" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (message, finalEnv) ← runCancelled z3 cvc5 true
  unless contains message "interrupted" || contains message "cancel" do
    throwError "model-extraction cancellation exception was lost: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "model-extraction cancellation left sessions in state"
  assertStopped "model-cancelled z3" z3
  assertStopped "model-cancelled cvc5" cvc5

private def testAgreementFailureSavesArtifacts : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      let z3 ← spawnFakeChild "unsat"
      let cvc5 ← spawnFakeChild "sat"
      let env := environment .agree
        #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
      let (message, finalEnv) ← (do
        let message ←
          try
            discard checkSat
            pure "agreement unexpectedly succeeded"
          catch error : Exception => error.toMessageData.toString
        discard exitSmt
        return message).run env
      unless contains message "Hard solver disagreement" do
        throwError "hard disagreement was not reported: {message}"
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "agreement failure left sessions in state"
      let entries ← (".blaster" : System.FilePath).readDir
      let some artifact := entries[0]? | throwError "agreement artifact directory was not created"
      for file in ["summary.txt", "z3.smt2", "cvc5.smt2"] do
        unless ← (artifact.path / file).pathExists do
          throwError "agreement artifact is missing {file}"
      assertStopped "disagreeing z3" z3
      assertStopped "disagreeing cvc5" cvc5
    finally
      IO.Process.setCurrentDir original

private def testCrashLifecycle : MetaM Unit := do
  testZ3WinsAndCvc5IsReaped
  testCvc5WinsAndZ3IsReaped
  testClosedStdoutDoesNotBeatDecisiveSolver
  testCrashPreservesStderrWithoutDuplicateCleanup
  testAlreadyExitedChildIsHandled
  testModelFailurePreservesSatVerdict
  testCancellationReapsBothChildren
  testCancellationDuringModelExtraction
  testAgreementFailureSavesArtifacts

#guard_msgs in
#eval testCrashLifecycle

end Test.CrashLifecycle
