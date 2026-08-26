import Blaster.Smt.Env

namespace Test.CrashLifecycle

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def withoutLoggedMessages (action : MetaM α) : MetaM α := do
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  try action
  finally Core.setMessageLog saved

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

private def spawnCommandChild
    (rejectDeclaration : Bool) (verdict : String := "unsat")
    (stderr : String := "") (commandDelaySeconds : String := "0") : IO PipedChild := do
  let declarationResponse :=
    if rejectDeclaration then
      s!"echo '{stderr}' >&2; echo '(error \"declaration rejected\")'"
    else
      s!"sleep {commandDelaySeconds}; echo success"
  let script :=
    "while IFS= read -r line; do case \"$line\" in " ++
    s!"'(declare-const '*) {declarationResponse};; " ++
    s!"'(check-sat)') echo '{verdict}';; " ++
    "'(get-model)') echo '()';; '(exit)') exit 0;; " ++
    s!"*) sleep {commandDelaySeconds}; echo success;; esac; done"
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", script]
    stdin := .piped
    stdout := .piped
    stderr := .piped
    setsid := true
  }

private def spawnObservedModelWinner
    (loserPid : UInt32) (marker : System.FilePath) : IO PipedChild :=
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c",
      "IFS= read -r first; echo sat; while IFS= read -r line; do " ++
      "case \"$line\" in '(get-model)') " ++
      s!"if /bin/kill -0 {loserPid} 2>/dev/null; then echo alive > '{marker}'; else echo dead > '{marker}'; fi; " ++
      "sleep 0.05; echo '()';; '(exit)') exit 0;; esac; done"]
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

private def record (solver : SmtSolver) (timeoutMs : Option Nat := none) : SolverRecord :=
  { solver, version := "fake 1.0", commandLine := s!"fake-{solver}",
    setupCommands := #[], timeoutMs }

private def environment
    (mode : SolverMode) (sessions : Array SolverSession)
    (generateCex : Bool := false)
    (z3TimeoutMs : Option Nat := none) (cvc5TimeoutMs : Option Nat := none) : TranslateEnv :=
  let base : TranslateEnv := default
  let options : BlasterOptions := { solverMode := mode, generateCex }
  let optEnv := { base.optEnv with options := { base.optEnv.options with solverOptions := options } }
  let timeoutFor
    | SmtSolver.z3 => z3TimeoutMs
    | SmtSolver.cvc5 => cvc5TimeoutMs
  let smtEnv := {
    base.smtEnv with
    sessions
    configuredSolvers := if mode == .single then #[.z3] else #[.z3, .cvc5]
    singleSolver := if mode == .single then some .z3 else none
    solverRecords := sessions.map fun session => record session.solver (timeoutFor session.solver)
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
    (z3 cvc5 : PipedChild) (generateCex : Bool := false)
    (z3TimeoutMs : Option Nat := none) (cvc5TimeoutMs : Option Nat := none) :
    MetaM (Result × TranslateEnv) := do
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    generateCex z3TimeoutMs cvc5TimeoutMs
  (do
    let result ← checkSat
    discard exitSmt
    return result).run env

private def expectValid (label : String) : Result → MetaM Unit
  | .Valid => pure ()
  | result => throwError "{label}: expected Valid, got {reprStr result}"


private def expectFalsified (label : String) : Result → MetaM Unit
  | .Falsified _ => pure ()
  | result => throwError "{label}: expected Falsified, got {reprStr result}"
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

private def testLoserLivesThroughWinnerModel : MetaM Unit := do
  IO.FS.withTempDir fun directory => do
    let marker := directory / "loser-state"
    let loser ← spawnFakeChild "unsat" "10"
    let winner ← spawnObservedModelWinner loser.pid marker
    let (result, _) ← runFirst winner loser true
    expectFalsified "observed model winner" result
    let observed ← IO.FS.readFile marker
    unless observed.trim == "alive" do
      throwError "loser was not alive during winner model retrieval: {observed}"
    assertStopped "model winner" winner
    assertStopped "model loser" loser

private def testFirstRetiresRejectedDeclaration : MetaM Unit := do
  let usefulStderr := "FAKE_REJECTED_DECLARATION"
  let z3 ← spawnCommandChild true "unsat" usefulStderr
  let cvc5 ← spawnCommandChild false
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
  let (result, finalEnv) ← (do
    declareConst (mkNormalSymbol "bad") intSort
    let result ← checkSat
    discard exitSmt
    return result).run env
  expectValid "healthy solver after declaration rejection" result
  let some failure := finalEnv.smtEnv.solverRecords.find? (·.solver == .z3)
    | throwError "missing rejected-solver diagnostic record"
  unless failure.failedCommand.any (contains · "(declare-const bad Int)") do
    throwError "failed declaration was not retained: {failure.failedCommand}"
  unless failure.failureResponse.any (contains · "declaration rejected") do
    throwError "failed declaration response was not retained: {failure.failureResponse}"
  unless contains (String.intercalate "\n" failure.stderr.toList) usefulStderr do
    throwError "failed declaration stderr was not retained: {failure.stderr}"
  assertStopped "rejected z3" z3
  assertStopped "healthy cvc5" cvc5

private def testAgreeRejectsDeclarationWithArtifacts : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      let usefulStderr := "FAKE_AGREE_REJECTED_DECLARATION"
      let z3 ← spawnCommandChild true "unsat" usefulStderr
      let cvc5 ← spawnCommandChild false
      let env := environment .agree
        #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
      let (message, finalEnv) ← (do
        discard checkSat
        let message ←
          try
            declareConst (mkNormalSymbol "bad") intSort
            pure "agreement unexpectedly accepted rejected declaration"
          catch error : Exception => error.toMessageData.toString
        return message).run env
      unless contains message "Agreement infrastructure failure" &&
          contains message "(declare-const bad Int)" do
        throwError "agreement declaration failure lacked context: {message}"
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "agreement declaration failure left sessions active"
      let entries ← (".blaster" : System.FilePath).readDir
      let some artifact := entries[0]? | throwError "command failure artifact was not created"
      let summary ← IO.FS.readFile (artifact.path / "summary.txt")
      let z3Transcript ← IO.FS.readFile (artifact.path / "z3.smt2")
      unless contains summary "(declare-const bad Int)" && contains summary usefulStderr &&
          contains summary "check command: <none>" && !contains z3Transcript "(check-sat)" do
        throwError "command failure artifact retained stale check data: {summary}\n{z3Transcript}"
      assertStopped "agree rejected z3" z3
      assertStopped "agree retired cvc5" cvc5
    finally
      IO.Process.setCurrentDir original

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

private def testOwnerCleansUnexpectedPrecheckException : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
  let (message, finalEnv) ← (do
    let message ←
      try
        withSmtSessionOwner do
          throwError "intentional exception before check-sat"
        pure "owner unexpectedly returned"
      catch error : Exception => error.toMessageData.toString
    return message).run env
  unless contains message "intentional exception before check-sat" do
    throwError "owner masked the original exception: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "owner left sessions installed after a precheck exception"
  assertStopped "precheck z3" z3
  assertStopped "precheck cvc5" cvc5

private def testCancellationBeforeSolving : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let token ← IO.CancelToken.new
  token.set
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
  let (message, finalEnv) ← withTheReader Core.Context
      (fun context => { context with cancelTk? := some token }) <| (do
    let message ←
      try
        withSmtSessionOwner checkCancelTk?
        pure "cancellation unexpectedly returned"
      catch error : Exception => error.toMessageData.toString
    return message).run env
  unless contains message "interrupted" || contains message "cancel" do
    throwError "precheck cancellation was converted to an ordinary error: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "precheck cancellation left sessions installed"
  assertStopped "precheck-cancelled z3" z3
  assertStopped "precheck-cancelled cvc5" cvc5

private def testCancellationDuringCommandSubmission : MetaM Unit := do
  let z3 ← spawnCommandChild false "unsat" "" "10"
  let cvc5 ← spawnCommandChild false "unsat" "" "10"
  let token ← IO.CancelToken.new
  let cancellation ← BaseIO.asTask do
    IO.sleep 50
    token.set
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
  let (message, finalEnv) ← withTheReader Core.Context
      (fun context => { context with cancelTk? := some token }) <| (do
    let message ←
      try
        withSmtSessionOwner do
          declareConst (mkNormalSymbol "blocked") intSort
        pure "command submission unexpectedly ignored cancellation"
      catch error : Exception => error.toMessageData.toString
    return message).run env
  let _ := cancellation.get
  unless contains message "interrupted" || contains message "cancel" do
    throwError "command-submission cancellation was converted to a solver error: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "command-submission cancellation left sessions installed"
  assertStopped "command-cancelled z3" z3
  assertStopped "command-cancelled cvc5" cvc5

-- The timed child sleeps past the 1 s response-drain grace. The healthy child
-- answers after that deadline but before its own, so test order cannot create
-- the timeout being asserted.
private def testZ3TimeoutDoesNotBeatCvc5 : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "1.20"
  let (result, finalEnv) ← runFirst z3 cvc5 false (some 30) (some 500)
  expectValid "cvc5 after z3 timeout" result
  let some z3Record := finalEnv.smtEnv.solverRecords.find? (·.solver == .z3)
    | throwError "missing z3 timeout record"
  unless z3Record.failedStage == some "check timeout" do
    throwError "z3 timeout was not a real runtime outcome: {z3Record.failedStage}"
  assertStopped "timed-out z3" z3
  assertStopped "healthy cvc5 after timeout" cvc5

private def testCvc5TimeoutDoesNotBeatZ3 : MetaM Unit := do
  let z3 ← spawnFakeChild "sat" "1.20"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (result, finalEnv) ← runFirst z3 cvc5 false (some 500) (some 30)
  expectFalsified "z3 after cvc5 timeout" result
  let some cvc5Record := finalEnv.smtEnv.solverRecords.find? (·.solver == .cvc5)
    | throwError "missing cvc5 timeout record"
  unless cvc5Record.failedStage == some "check timeout" do
    throwError "cvc5 timeout was not a real runtime outcome: {cvc5Record.failedStage}"
  assertStopped "healthy z3 after timeout" z3
  assertStopped "timed-out cvc5" cvc5

private def testBothTimeoutsAreInfrastructureFailure : MetaM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    false (some 30) (some 30)
  let (message, finalEnv) ← (do
    let message ←
      try
        discard checkSat
        pure "both timeouts unexpectedly returned a verdict"
      catch error : Exception => error.toMessageData.toString
    discard exitSmt
    return message).run env
  unless contains message "timedOut" || contains message "timeout" do
    throwError "both timeouts were hidden behind Undetermined: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "both-timeout path left sessions installed"
  assertStopped "both-timeout z3" z3
  assertStopped "both-timeout cvc5" cvc5

private def testAgreementTimeoutIsInfrastructureFailure : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      let z3 ← spawnFakeChild "unsat" "10"
      let cvc5 ← spawnFakeChild "unsat" "0.10"
      let env := environment .agree
        #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
        false (some 30) (some 500)
      let (message, finalEnv) ← (do
        let message ←
          try
            discard checkSat
            pure "agreement timeout unexpectedly succeeded"
          catch error : Exception => error.toMessageData.toString
        discard exitSmt
        return message).run env
      unless contains message "timedOut" && contains message "Agreement artifacts" do
        throwError "agreement timeout was not an infrastructure failure: {message}"
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "agreement timeout left sessions installed"
      assertStopped "agreement timed-out z3" z3
      assertStopped "agreement decisive cvc5" cvc5
    finally
      IO.Process.setCurrentDir original

private def testSingleTimeoutIsVisibleFailure : MetaM Unit := do
  let process ← spawnFakeChild "unsat" "10"
  let env := environment .single #[{ solver := .z3, process }] false (some 30)
  let (message, finalEnv) ← (do
    let message ←
      try
        discard checkSat
        pure "single timeout unexpectedly returned a verdict"
      catch error : Exception => error.toMessageData.toString
    discard exitSmt
    return message).run env
  unless contains message "configured timeout=30ms" do
    throwError "single timeout was hidden or imprecise: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "single timeout left its child installed"
  assertStopped "single timed-out child" process

private def testProtocolFailureDoesNotBeatHealthySolver : MetaM Unit := do
  let z3 ← spawnFakeChild "not-a-verdict"
  let cvc5 ← spawnFakeChild "unsat" "0.05"
  let (result, finalEnv) ← runFirst z3 cvc5
  expectValid "healthy solver after protocol failure" result
  let some z3Record := finalEnv.smtEnv.solverRecords.find? (·.solver == .z3)
    | throwError "missing protocol-failure record"
  unless z3Record.failedStage == some "check protocol" do
    throwError "malformed response was not classified as protocol failure"
  assertStopped "protocol-failed z3" z3
  assertStopped "healthy cvc5 after protocol failure" cvc5

private def testInfrastructurePlusUnknownIsNotUndetermined : MetaM Unit := do
  let usefulStderr := "FAKE_INFRASTRUCTURE_WITH_UNKNOWN"
  let z3 ← spawnFakeChild "unknown"
  let cvc5 ← spawnFakeChild "" "0" "0" usefulStderr true
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
  let (message, finalEnv) ← (do
    let message ←
      try
        discard checkSat
        pure "infrastructure plus unknown unexpectedly returned"
      catch error : Exception => error.toMessageData.toString
    discard exitSmt
    return message).run env
  unless contains message "infrastructure failed" && contains message usefulStderr do
    throwError "infrastructure failure was hidden behind Undetermined: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "infrastructure-plus-unknown left sessions installed"
  assertStopped "ordinary unknown z3" z3
  assertStopped "failed cvc5 with unknown peer" cvc5

private def testBothOrdinaryUnknownRemainUndetermined : MetaM Unit := do
  let z3 ← spawnFakeChild "unknown"
  let cvc5 ← spawnFakeChild "unknown"
  let (result, _) ← runFirst z3 cvc5
  match result with
  | .Undetermined => pure ()
  | other => throwError "ordinary unknown was not preserved: {reprStr other}"
  assertStopped "unknown z3" z3
  assertStopped "unknown cvc5" cvc5

private def testAgreementUsesCompletePeerEvidence : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      let z3 ← spawnFakeChild "sat" "0" "0" "" false "(error \"z3 model unavailable\")"
      let cvc5 ← spawnFakeChild "sat" "0" "0" "" false "()"
      let env := environment .agree
        #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }] true
      let (result, finalEnv) ← (do
        let result ← checkSat
        discard exitSmt
        return result).run env
      match result with
      | .Falsified evidence =>
          unless evidence.map String.trim == ["()"] do
            throwError "complete cvc5 evidence did not outrank failed Z3 evidence: {evidence}"
      | other => throwError "model failure erased agreement verdict: {reprStr other}"
      let entries ← (".blaster" : System.FilePath).readDir
      let some artifact := entries[0]? | throwError "incomplete-model artifact was not created"
      let summary ← IO.FS.readFile (artifact.path / "summary.txt")
      unless contains summary "z3 model unavailable" && contains summary "raw model responses" do
        throwError "incomplete-model artifact omitted raw diagnostics: {summary}"
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "incomplete-model agreement left sessions installed"
      assertStopped "model-failed agreement z3" z3
      assertStopped "complete-evidence cvc5" cvc5
    finally
      IO.Process.setCurrentDir original

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

#eval testZ3WinsAndCvc5IsReaped
#eval testCvc5WinsAndZ3IsReaped
#eval testLoserLivesThroughWinnerModel
#eval testClosedStdoutDoesNotBeatDecisiveSolver
#eval testFirstRetiresRejectedDeclaration
#eval testAgreeRejectsDeclarationWithArtifacts
#eval testCrashPreservesStderrWithoutDuplicateCleanup
#eval testAlreadyExitedChildIsHandled
#eval testModelFailurePreservesSatVerdict
#eval testOwnerCleansUnexpectedPrecheckException
#eval testCancellationBeforeSolving
#eval testCancellationDuringCommandSubmission
#eval testCancellationReapsBothChildren
#eval testCancellationDuringModelExtraction
#eval testZ3TimeoutDoesNotBeatCvc5
#eval testCvc5TimeoutDoesNotBeatZ3
#eval withoutLoggedMessages testBothTimeoutsAreInfrastructureFailure
#eval testSingleTimeoutIsVisibleFailure
#eval testProtocolFailureDoesNotBeatHealthySolver
#eval withoutLoggedMessages testInfrastructurePlusUnknownIsNotUndetermined
#eval testBothOrdinaryUnknownRemainUndetermined
#eval testAgreementUsesCompletePeerEvidence
#eval testAgreementTimeoutIsInfrastructureFailure
#eval testAgreementFailureSavesArtifacts

end Test.CrashLifecycle
