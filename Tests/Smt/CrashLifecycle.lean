import Blaster.Smt.Env

namespace Test.CrashLifecycle

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private abbrev LifecycleM := ReaderT (IO.Ref (Array OwnedProcess)) MetaM

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def withoutLoggedMessages (action : LifecycleM α) : LifecycleM α := do
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  try action
  finally Core.setMessageLog saved


private def spawnOwned (args : IO.Process.SpawnArgs) : LifecycleM OwnedProcess := do
  let child ← OwnedProcess.spawn args
  (← read : IO.Ref (Array OwnedProcess)).modify (·.push child)
  return child

-- Every test has an outer resource owner, including failures during assertions
-- or while spawning the second backend.
private def withCleanup (action : LifecycleM Unit) : MetaM Unit := do
  let children ← IO.mkRef (#[] : Array OwnedProcess)
  try action.run children
  finally
    for child in ← children.get do
      discard <| child.cleanup true

private def spawnFakeChild
    (response : String) (delaySeconds : String := "0")
    (modelDelaySeconds : String := "0") (stderr : String := "")
    (closeStdout : Bool := false) (modelResponse : String := "()") : LifecycleM OwnedProcess := do
  let afterRead :=
    if closeStdout then
      s!"echo '{stderr}' >&2; exec 1>&-; sleep 10"
    else
      s!"sleep {delaySeconds}; echo '{response}'; " ++
      "while IFS= read -r line; do " ++
      s!"case \"$line\" in '(get-model)') sleep {modelDelaySeconds}; echo '{modelResponse}';; " ++
      "'(get-value ('*) echo '((x 0))';; '(exit)') exit 0;; esac; done"
  spawnOwned {
    cmd := "/bin/sh"
    args := #["-c", "IFS= read -r first; " ++ afterRead]
  }

private def spawnCommandChild
    (rejectDeclaration : Bool) (verdict : String := "unsat")
    (stderr : String := "") (commandDelaySeconds : String := "0") : LifecycleM OwnedProcess := do
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
  spawnOwned {
    cmd := "/bin/sh"
    args := #["-c", script]
  }

private def spawnObservedModelWinner
    (loserPid : UInt32) (marker : System.FilePath) : LifecycleM OwnedProcess :=
  spawnOwned {
    cmd := "/bin/sh"
    args := #["-c",
      "IFS= read -r first; echo sat; while IFS= read -r line; do " ++
      "case \"$line\" in '(get-model)') " ++
      s!"if /bin/kill -0 {loserPid} 2>/dev/null; then echo alive > '{marker}'; else echo dead > '{marker}'; fi; " ++
      "echo '()';; '(exit)') exit 0;; esac; done"]
  }

private def spawnDeadChild (stderr : String) : LifecycleM OwnedProcess :=
  spawnOwned {
    cmd := "/bin/sh"
    args := #["-c", s!"echo '{stderr}' >&2; exit 17"]
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

private def processAlive (process : OwnedProcess) : IO Bool := do
  let output ← IO.Process.output {
    cmd := "/bin/kill"
    args := #["-0", toString process.pid]
  }
  return output.exitCode == 0

private def assertStopped (label : String) (process : OwnedProcess) : LifecycleM Unit := do
  if ← processAlive process then
    throwError "{label}: solver process {process.pid} remained alive"

private def runFirst
    (z3 cvc5 : OwnedProcess) (generateCex : Bool := false)
    (z3TimeoutMs : Option Nat := none) (cvc5TimeoutMs : Option Nat := none) :
    LifecycleM (Result × TranslateEnv) := do
  let env := environment .first
    #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    generateCex z3TimeoutMs cvc5TimeoutMs
  (do
    let result ← checkSat
    discard exitSmt
    return result).run env

private def expectValid (label : String) : Result → LifecycleM Unit
  | .Valid => pure ()
  | result => throwError "{label}: expected Valid, got {reprStr result}"


private def expectFalsified (label : String) : Result → LifecycleM Unit
  | .Falsified _ => pure ()
  | result => throwError "{label}: expected Falsified, got {reprStr result}"
private def testZ3WinsAndCvc5IsReaped : LifecycleM Unit := do
  let z3 ← spawnFakeChild "unsat"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (result, _) ← runFirst z3 cvc5
  expectValid "z3 winner" result
  assertStopped "z3 winner" z3
  assertStopped "cvc5 loser" cvc5

private def testCvc5WinsAndZ3IsReaped : LifecycleM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat"
  let (result, _) ← runFirst z3 cvc5
  expectValid "cvc5 winner" result
  assertStopped "z3 loser" z3
  assertStopped "cvc5 winner" cvc5

private def testClosedStdoutDoesNotBeatDecisiveSolver : LifecycleM Unit := do
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

private def testLoserDeadBeforeWinnerModel : LifecycleM Unit := do
  for winnerIsZ3 in [true, false] do
    IO.FS.withTempDir fun directory => do
      let marker := directory / "loser-state"
      let loser ← spawnOwned {
        cmd := "/bin/sh"
        args := #["-c", "trap '' TERM; while IFS= read -r line; do :; done"]
      }
      let winner ← spawnObservedModelWinner loser.pid marker
      let (z3, cvc5) := if winnerIsZ3 then (winner, loser) else (loser, winner)
      let (result, _) ← runFirst z3 cvc5 true
      expectFalsified "observed model winner" result
      let observed ← IO.FS.readFile marker
      unless observed.trim == "dead" do
        throwError "loser remained alive during winner model retrieval: {observed}"
      assertStopped "model winner" winner
      assertStopped "model loser" loser

private def testFirstRetiresRejectedDeclaration : LifecycleM Unit := do
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

private def testAgreeRejectsDeclarationWithArtifacts : LifecycleM Unit := do
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

private def observeSingleCrash (process : OwnedProcess) : LifecycleM (String × Bool) := do
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

private def testCrashPreservesStderrWithoutDuplicateCleanup : LifecycleM Unit := do
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

private def testAlreadyExitedChildIsHandled : LifecycleM Unit := do
  let usefulStderr := "FAKE_DEAD_CHILD: deliberate stderr"
  let dead ← spawnDeadChild usefulStderr
  let (message, cleared) ← observeSingleCrash dead
  unless contains message "closed stdout" && contains message usefulStderr do
    throwError "already-exited solver diagnostics were lost: {message}"
  unless cleared do throwError "already-exited solver remained in session state"
  assertStopped "already-exited child" dead

private def testModelFailurePreservesSatVerdict : LifecycleM Unit := do
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

private def testOwnerCleansUnexpectedPrecheckException : LifecycleM Unit := do
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

private def testCancellationBeforeSolving : LifecycleM Unit := do
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

private def testCancellationDuringCommandSubmission : LifecycleM Unit := do
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
private def testZ3TimeoutDoesNotBeatCvc5 : LifecycleM Unit := do
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

private def testCvc5TimeoutDoesNotBeatZ3 : LifecycleM Unit := do
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

private def testBothTimeoutsAreInfrastructureFailure : LifecycleM Unit := do
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

private def testAgreementTimeoutIsInfrastructureFailure : LifecycleM Unit := do
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

private def testSingleTimeoutIsVisibleFailure : LifecycleM Unit := do
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

private def testProtocolFailureDoesNotBeatHealthySolver : LifecycleM Unit := do
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

private def testInfrastructurePlusUnknownIsNotUndetermined : LifecycleM Unit := do
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

private def testBothOrdinaryUnknownRemainUndetermined : LifecycleM Unit := do
  let z3 ← spawnFakeChild "unknown"
  let cvc5 ← spawnFakeChild "unknown"
  let (result, _) ← runFirst z3 cvc5
  match result with
  | .Undetermined => pure ()
  | other => throwError "ordinary unknown was not preserved: {reprStr other}"
  assertStopped "unknown z3" z3
  assertStopped "unknown cvc5" cvc5

private def testAgreementUsesCompletePeerEvidence : LifecycleM Unit := do
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
      unless contains summary "z3 model unavailable" && contains summary "raw model responses" &&
          contains summary "modelFailed" do
        throwError "incomplete-model artifact omitted raw diagnostics: {summary}"
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "incomplete-model agreement left sessions installed"
      assertStopped "model-failed agreement z3" z3
      assertStopped "complete-evidence cvc5" cvc5
    finally
      IO.Process.setCurrentDir original

private def runCancelled
    (z3 cvc5 : OwnedProcess) (modelExtraction : Bool) : LifecycleM (String × TranslateEnv) := do
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

private def testCancellationReapsBothChildren : LifecycleM Unit := do
  let z3 ← spawnFakeChild "unsat" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (message, finalEnv) ← runCancelled z3 cvc5 false
  unless contains message "interrupted" || contains message "cancel" do
    throwError "cancellation exception was lost: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "cancellation left owned sessions in state"
  assertStopped "cancelled z3" z3
  assertStopped "cancelled cvc5" cvc5

private def testCancellationDuringModelExtraction : LifecycleM Unit := do
  let z3 ← spawnFakeChild "sat" "0" "10"
  let cvc5 ← spawnFakeChild "unsat" "10"
  let (message, finalEnv) ← runCancelled z3 cvc5 true
  unless contains message "interrupted" || contains message "cancel" do
    throwError "model-extraction cancellation exception was lost: {message}"
  unless finalEnv.smtEnv.sessions.isEmpty do
    throwError "model-extraction cancellation left sessions in state"
  assertStopped "model-cancelled z3" z3
  assertStopped "model-cancelled cvc5" cvc5

private def testAgreementFailureSavesArtifacts : LifecycleM Unit := do
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

private def spawnFixture
    (mode : String) (directory : System.FilePath) (verdict := "unsat") : LifecycleM OwnedProcess :=
  spawnOwned {
    cmd := "/bin/sh"
    args := #["Tests/Smt/lifecycle-solver.sh", mode, directory.toString, verdict]
  }

private partial def awaitMarkerUntil (path : System.FilePath) (deadline : Nat) : IO Unit := do
  if ← path.pathExists then return
  if (← IO.monoMsNow) ≥ deadline then
    throw <| IO.userError s!"fixture never acknowledged {path}"
  IO.sleep 10
  awaitMarkerUntil path deadline

private def awaitMarker (path : System.FilePath) : IO Unit := do
  awaitMarkerUntil path ((← IO.monoMsNow) + 10000)

private partial def assertPidStoppedUntil
    (label : String) (pid : String) (deadline : Nat) : LifecycleM Unit := do
  let output ← IO.Process.output { cmd := "/bin/kill", args := #["-0", pid] }
  if output.exitCode != 0 then return
  -- An orphan zombie is stopped; only its new OS parent can reap it.
  let status ← IO.Process.output { cmd := "/bin/ps", args := #["-p", pid, "-o", "stat="] }
  if status.exitCode == 0 && status.stdout.trim.startsWith "Z" then return
  if (← IO.monoMsNow) ≥ deadline then
    throwError "{label}: descendant {pid} remained alive after cleanup"
  IO.sleep 10
  assertPidStoppedUntil label pid deadline

private def assertDescendantsStopped (directory : System.FilePath) : LifecycleM Unit := do
  for name in ["branch.pid", "leaf.pid"] do
    let path := directory / name
    if ← path.pathExists then
      let pid := (← IO.FS.readFile path).trim
      assertPidStoppedUntil name pid ((← IO.monoMsNow) + 5000)

private def assertWithin (label : String) (started budget : Nat) : LifecycleM Unit := do
  let elapsed := (← IO.monoMsNow) - started
  unless elapsed < budget do
    throwError "{label}: elapsed {elapsed}ms exceeded outer bound {budget}ms"

private def testCleanupIgnoresExitAndTerm : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "silent" directory
    awaitMarker (directory / "ready")
    let request ← process.asTask do
      process.stdin.putStr "(exit)\n"
      process.stdin.flush
    awaitMarker (directory / "exit-requested")
    unless ← processAlive process do
      throwError "ignore-exit fixture exited before cleanup was exercised"
    let pending ← process.asTask process.stdout.getLine
    let started ← IO.monoMsNow
    let token ← IO.CancelToken.new
    token.set
    let stderr ← withTheReader Core.Context
      (fun context => { context with cancelTk? := some token }) <|
        (do return ← process.cleanup : LifecycleM String)
    let repeated ← process.cleanup true
    assertWithin "TERM-resistant cleanup" started operationBudgetMs
    unless stderr == repeated do
      throwError "repeated cleanup changed retained diagnostics"
    unless (← IO.hasFinished request) && (← IO.hasFinished pending) do
      throwError "cleanup returned with an owned I/O task still running"
    assertStopped "TERM-resistant child" process

private def testWrapperGrandchildrenAndInheritedPipes : LifecycleM Unit := do
  for mode in ["tree", "orphan-tree"] do
    IO.FS.withTempDir fun directory => do
      let process ← spawnFixture mode directory
      awaitMarker (directory / "ready")
      awaitMarker (directory / "branch.pid")
      awaitMarker (directory / "leaf.pid")
      if mode == "orphan-tree" then
        let deadline := (← IO.monoMsNow) + 10000
        while !(← process.exited) do
          if (← IO.monoMsNow) ≥ deadline then
            throwError "wrapper did not exit before inherited-pipe cleanup"
          IO.sleep 10
      let pending ← process.asTask process.stdout.getLine
      let started ← IO.monoMsNow
      discard process.cleanup
      assertWithin "inherited-pipe cleanup" started operationBudgetMs
      unless ← IO.hasFinished pending do
        throwError "inherited stdout kept an owned read alive after cleanup"
      assertStopped "wrapper" process
      assertDescendantsStopped directory

private def testStderrFloodIsDrainedAndBounded : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "flood" directory
    -- This marker is after a write much larger than a pipe's capacity.
    awaitMarker (directory / "flood-complete")
    let stderr ← process.cleanup true
    unless contains stderr "USEFUL_STDERR_PREFIX" || contains stderr "USEFUL_STDERR_SUFFIX" do
      throwError "stderr truncation discarded both useful diagnostic boundaries"
    unless contains stderr "truncat" do
      throwError "bounded stderr omitted its truncation indication"
    unless stderr.length < 128 * 1024 do
      throwError "stderr retention was not bounded: {stderr.length} characters"
    let repeated ← process.cleanup
    unless repeated == stderr do
      throwError "idempotent cleanup lost bounded stderr diagnostics"
    assertStopped "stderr-flood child" process

private def testSilentCommandAndBlockedWriteAreBounded : LifecycleM Unit := do
  for blockedWrite in [false, true] do
    IO.FS.withTempDir fun directory => do
      let process ← spawnFixture (if blockedWrite then "no-read" else "silent") directory
      awaitMarker (directory / "ready")
      let env := environment .single #[{ solver := .z3, process }]
      let name := if blockedWrite then String.mk (List.replicate (4 * 1024 * 1024) 'x') else "silent"
      let started ← IO.monoMsNow
      let (message, finalEnv) ← (do
        try
          withSmtSessionOwner <| declareConst (mkNormalSymbol name) intSort
          pure "silent command unexpectedly succeeded"
        catch error : Exception =>
          if error.isInterrupt || error.isRuntime then throw error
          error.toMessageData.toString).run env
      let expected := if blockedWrite then "command write: operation deadline exceeded"
        else "command acknowledgement: operation deadline exceeded"
      unless contains message expected do throwError "wrong blocked-I/O failure: {message}"
      if !blockedWrite && !contains message "SILENT_PROTOCOL_DIAGNOSTIC" then
        throwError "command deadline discarded useful stderr"
      assertWithin "silent command/write" started (operationBudgetMs + 10000)
      unless finalEnv.smtEnv.sessions.isEmpty do
        throwError "command deadline left an installed session"
      if !blockedWrite then awaitMarker (directory / "command-requested")
      assertStopped "silent command child" process
      assertDescendantsStopped directory

private def testSilentModelPreservesSatWithinEvidenceBudget : LifecycleM Unit := do
  for mode in [SolverMode.single, .first] do
    for solver in [SmtSolver.z3, .cvc5] do
      IO.FS.withTempDir fun directory => do
        let process ← spawnFixture "silent-model" directory "sat"
        let mut sessions := #[{ solver, process : SolverSession }]
        if mode == .first then
          let loserDir := directory / "loser"
          IO.FS.createDir loserDir
          let loser ← spawnFixture "silent" loserDir
          sessions := sessions.push {
            solver := if solver == .z3 then .cvc5 else .z3, process := loser }
        let env := environment mode sessions true
        let env := if mode == .single then
          { env with smtEnv := { env.smtEnv with
            configuredSolvers := #[solver], singleSolver := some solver } } else env
        let started ← IO.monoMsNow
        let (result, finalEnv) ← (withSmtSessionOwner checkSat).run env
        assertWithin "silent model" started (evidenceBudgetMs + 3000)
        expectFalsified "silent model must not erase sat" result
        awaitMarker (directory / "model-requested")
        let some record := finalEnv.smtEnv.solverRecords.find? (·.solver == solver)
          | throwError "silent model lost its solver record"
        unless record.failedStage == some "model evidence" && record.failureResponse.isSome do
          throwError "silent model did not retain incomplete-evidence diagnostics"
        for session in sessions do assertStopped "silent-model check" session.process

private def testReadyDisagreementNeverRequestsModels : LifecycleM Unit := do
  for satIsZ3 in [true, false] do
    let original ← IO.currentDir
    IO.FS.withTempDir fun directory => do
      let satDir := directory / "sat"
      let unsatDir := directory / "unsat"
      IO.FS.createDirAll satDir
      IO.FS.createDirAll unsatDir
      let sat ← spawnFixture "ready" satDir "sat"
      let unsat ← spawnFixture "ready" unsatDir "unsat"
      -- Both verdicts are already in their pipes before the orchestrator runs.
      -- The sat fixture never answers a model request.
      awaitMarker (satDir / "verdict-ready")
      awaitMarker (unsatDir / "verdict-ready")
      let (z3, cvc5) := if satIsZ3 then (sat, unsat) else (unsat, sat)
      try
        IO.Process.setCurrentDir directory
        let env := environment .agree
          #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }] true
        let started ← IO.monoMsNow
        let (message, finalEnv) ← (do
          try
            discard checkSat
            pure "disagreement unexpectedly returned a result"
          catch error : Exception => error.toMessageData.toString).run env
        unless contains message "Hard solver disagreement" do
          throwError "ready sat/unsat verdicts did not report disagreement: {message}"
        assertWithin "ready disagreement" started (operationBudgetMs + 5000)
        if (← (satDir / "model-requested").pathExists) ||
            (← (unsatDir / "model-requested").pathExists) then
          throwError "model evidence was requested before verdict disagreement was resolved"
        unless finalEnv.smtEnv.sessions.isEmpty do
          throwError "disagreement left active sessions"
        assertStopped "disagreeing sat child" sat
        assertStopped "disagreeing unsat child" unsat
      finally IO.Process.setCurrentDir original

private def testReadyUnknownDoesNotBeatDecisiveVerdict : LifecycleM Unit := do
  for unknownIsZ3 in [true, false] do
    IO.FS.withTempDir fun directory => do
      let unknownDir := directory / "unknown"
      let validDir := directory / "valid"
      IO.FS.createDirAll unknownDir
      IO.FS.createDirAll validDir
      let unknown ← spawnFixture "ready" unknownDir "unknown"
      let valid ← spawnFixture "ready" validDir "unsat"
      awaitMarker (unknownDir / "verdict-ready")
      awaitMarker (validDir / "verdict-ready")
      let (z3, cvc5) := if unknownIsZ3 then (unknown, valid) else (valid, unknown)
      let (result, _) ← runFirst z3 cvc5
      expectValid "simultaneous unknown/unsat" result
      assertStopped "ready unknown" unknown
      assertStopped "ready unsat" valid

private def testMalformedAndClosedRepliesRetainDiagnostics : LifecycleM Unit := do
  for mode in ["closed", "malformed"] do
    for failedIsZ3 in [true, false] do
      IO.FS.withTempDir fun directory => do
        let failed ← spawnFixture mode directory
        let unknown ← spawnFakeChild "unknown"
        let (z3, cvc5) := if failedIsZ3 then (failed, unknown) else (unknown, failed)
        let env := environment .first
          #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
        let (message, finalEnv) ← (do
          try
            discard checkSat
            pure "infrastructure failure unexpectedly returned a result"
          catch error : Exception => error.toMessageData.toString).run env
        let solver := if failedIsZ3 then SmtSolver.z3 else .cvc5
        let some record := finalEnv.smtEnv.solverRecords.find? (·.solver == solver)
          | throwError "missing failed solver record"
        let stderr := String.intercalate "\n" record.stderr.toList
        let diagnostic := if mode == "closed" then "CLOSED_STDOUT_DIAGNOSTIC"
          else "MALFORMED_REPLY_DIAGNOSTIC"
        unless contains message "infrastructure" && contains stderr diagnostic do
          throwError "infrastructure failure was hidden or lost stderr: {message}\n{stderr}"
        if mode == "malformed" then
          unless record.failureResponse.any (contains · "not-a-verdict") do
            throwError "malformed reply was not preserved verbatim"
        assertStopped "failed solver with unknown peer" failed
        assertStopped "ordinary unknown peer" unknown

private def testHandshakeCancellationAcrossStages : LifecycleM Unit := do
  for stage in ["command", "check", "model"] do
    IO.FS.withTempDir fun directory => do
      let process ← spawnFixture (if stage == "model" then "silent-model" else "silent") directory "sat"
      let token ← IO.CancelToken.new
      let cancellation ← IO.asTask do
        awaitMarker (directory / s!"{stage}-requested")
        token.set
      let original ← IO.currentDir
      try
        IO.Process.setCurrentDir directory
        let env := environment .single #[{ solver := .z3, process }] (stage == "model")
        let (message, finalEnv) ← withTheReader Core.Context
            (fun context => { context with cancelTk? := some token }) <| (do
          try
            withSmtSessionOwner do
              if stage == "command" then
                declareConst (mkNormalSymbol "cancelled") intSort
              else
                discard checkSat
            pure "operation ignored interruption"
          catch error : Exception => error.toMessageData.toString).run env
        discard <| IO.ofExcept cancellation.get
        unless contains message "interrupted" || contains message "cancel" do
          throwError "{stage} cancellation became an infrastructure failure: {message}"
        unless finalEnv.smtEnv.sessions.isEmpty do
          throwError "{stage} cancellation left an installed session"
        let artifacts ← (directory / ".blaster").readDir
        let some artifact := artifacts[0]? | throwError "cancellation artifact was not retained"
        let summary ← IO.FS.readFile (artifact.path / "summary.txt")
        let query ← IO.FS.readFile (artifact.path / "z3.smt2")
        let expected := if stage == "command" then "(declare-const cancelled Int)"
          else if stage == "model" then "(get-model)" else "(check-sat)"
        unless contains summary "reason: cancelled" && contains query expected do
          throwError "cancellation artifact lost its current {stage} query"
        assertStopped "handshake-cancelled child" process
      finally IO.Process.setCurrentDir original

private def testVersionProbeDeadlineAndCancellation : LifecycleM Unit := do
  for cancelled in [false, true] do
    IO.FS.withTempDir fun directory => do
      let token ← IO.CancelToken.new
      let cancellation ← IO.asTask do
        if cancelled then
          awaitMarker (directory / "ready")
          token.set
      let candidate : SolverCandidate := {
        cmd := "/bin/sh"
        prefixArgs := #["Tests/Smt/lifecycle-solver.sh", "silent", directory.toString] }
      let started ← IO.monoMsNow
      let outcome ← probeSolverCandidate SmtSolver.cvc5.descriptor candidate
        (some (started + if cancelled then 5000 else 500)) (some token)
      discard <| IO.ofExcept cancellation.get
      match outcome with
      | .ran _ _ => throwError "stalled version probe unexpectedly completed"
      | .failed error =>
          unless contains error (if cancelled then "cancelled" else "deadline") do
            throwError "version probe lost failed stage: {error}"
      assertWithin "version probe" started 10000
      let pid ← IO.FS.readFile (directory / "leader.pid")
      let alive ← IO.Process.output { cmd := "/bin/kill", args := #["-0", pid.trim] }
      unless alive.exitCode != 0 do throwError "version probe left an unreaped child {pid}"

private def testUnsupportedEvidenceIsNotAConcreteValue : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "unsupported" directory "sat"
    let env := environment .single #[{ solver := .z3, process }] true
    let env := { env with smtEnv.topLevelVars := #[[(mkNormalSymbol "x", `x)]] }
    let (result, finalEnv) ← (withSmtSessionOwner checkSat).run env
    match result with
    | .Falsified [value] =>
        unless contains value "unsupported SMT value" && contains value "@opaque" do
          throwError "uninterpreted value was presented as a Lean value: {value}"
    | other => throwError "unsupported evidence changed sat: {reprStr other}"
    let some record := finalEnv.smtEnv.solverRecords[0]?
      | throwError "unsupported evidence lost its record"
    unless record.failedStage == some "model evidence" &&
        record.modelResponses.any (contains · "((x @opaque))") do
      throwError "unsupported evidence was not marked incomplete with its raw response"
    assertStopped "unsupported-model child" process

private def startupSource : String := r#"import Blaster.Smt.Env
open Lean Blaster.Options Blaster.Optimize Blaster.Smt
#eval show MetaM Unit from do
  let directory := (← IO.getEnv "BLASTER_TEST_DIR").getD ""
  let stage := (← IO.getEnv "BLASTER_TEST_STAGE").getD ""
  let replay := stage == "replay" || stage == "restart-probe"
  let firstSetup := (← IO.getEnv "BLASTER_TEST_STAGE") == some "first-setup"
  let cancelled := (← IO.getEnv "BLASTER_TEST_CANCEL") == some "1"
  let token ← IO.CancelToken.new
  let watcher ← IO.asTask do
    let deadline := (← IO.monoMsNow) + 10000
    while !(← (System.FilePath.mk directory / "blocked").pathExists) do
      if (← IO.monoMsNow) ≥ deadline then throw <| IO.userError "stage was never reached"
      IO.sleep 5
    if cancelled then token.set
  let base : TranslateEnv := default
  let options : BlasterOptions := if replay || firstSetup then
    { solverMode := .first, generateCex := false }
    else { solver := some .cvc5, generateCex := false }
  let env := { base with optEnv.options.solverOptions := options }
  let ((interrupted, message), finalEnv) ← withTheReader Core.Context
      (fun context => { context with cancelTk? := some token }) <| (do
    try
      withSmtSessionOwner do
        setBlasterProcess
        if replay then
          declareConst (mkNormalSymbol "replayed") intSort
          unless isValidResult (← checkSat) do throwError "initial fake check was not valid"
          unless isValidResult (← checkSat) do throwError "healthy backend lost after replay failure"
        if firstSetup then
          unless isValidResult (← checkSat) do throwError "startup failure suppressed healthy backend"
      return (false, "")
    catch error : Exception => return (error.isInterrupt, ← error.toMessageData.toString)).run env
  discard <| IO.ofExcept watcher.get
  unless finalEnv.smtEnv.sessions.isEmpty do throwError "startup/replay leaked a session"
  if cancelled then
    unless interrupted do throwError "cancellation became an ordinary failure: {message}"
  else if stage == "paced-setup" then
    unless !interrupted && message.isEmpty do
      throwError "healthy aggregate setup exceeded its phase budget: {message}"
  else if replay || firstSetup then
    unless !interrupted && message.isEmpty do
      throwError "healthy fallback did not complete: {message}"
    let some record := finalEnv.smtEnv.solverRecords.find? (·.solver == .cvc5)
      | throwError "missing replay failure record"
    let expectedStage := if stage == "restart-probe" then "process startup"
      else if replay then "canonical query replay" else "solver setup"
    unless record.failedStage == some expectedStage do
      throwError "replay timeout lost its stage: {record.failedStage}"
    if stage == "restart-probe" then
      unless record.failureResponse.any (fun text => (text.splitOn "deliberate restart probe failure").length > 1) do
        throwError "restart discovery stderr was discarded"
  else
    unless (message.splitOn "solver setup").length > 1 do
      throwError "silent setup did not produce a setup failure: {message}"
"#

private def testStartupAndReplayLimits : LifecycleM Unit := do
  let fixture := (← IO.currentDir) / "Tests" / "Smt" / "lifecycle-solver.sh"
  for stage in ["setup", "first-setup", "replay", "restart-probe", "paced-setup"] do
    for cancelled in (if stage == "restart-probe" || stage == "paced-setup" then [false] else [false, true]) do
      IO.FS.withTempDir fun directory => do
        for backend in ["z3", "cvc5"] do
          let path := directory / backend
          IO.FS.writeFile path
            s!"#!/bin/sh\nexec /bin/sh '{fixture}' session '{directory}' {backend} \"$@\"\n"
          let permission ← IO.Process.output { cmd := "/bin/chmod", args := #["+x", path.toString] }
          unless permission.exitCode == 0 do throwError "could not prepare fake solver"
        let source := directory / "Startup.lean"
        IO.FS.writeFile source startupSource
        let output ← OwnedProcess.output {
          cmd := "lake", args := #["lean", source.toString]
          env := #[("PATH", some s!"{directory}:{(← IO.getEnv "PATH").getD ""}"),
            ("BLASTER_TEST_DIR", some directory.toString),
            ("BLASTER_TEST_STAGE", some stage),
            ("BLASTER_TEST_CANCEL", some (if cancelled then "1" else "0"))]
        } ((← IO.monoMsNow) + 20000)
        unless output.exitCode == 0 do
          throwError "{stage} startup/replay regression failed:\n{output.stdout}\n{output.stderr}"
        for entry in ← directory.readDir do
          if entry.path.extension == some "pid" then
            let pid := (← IO.FS.readFile entry.path).trim
            let alive ← IO.Process.output { cmd := "/bin/kill", args := #["-0", pid] }
            unless alive.exitCode != 0 do throwError "{stage} left owned child {pid}"

private def testAgreementFailureStopsUnlimitedPeer : LifecycleM Unit := do
  for failedIsZ3 in [true, false] do
    IO.FS.withTempDir fun directory => do
      let failedDir := directory / "failed"
      let peerDir := directory / "peer"
      IO.FS.createDir failedDir
      IO.FS.createDir peerDir
      let failed ← spawnFixture "silent" failedDir
      let peer ← spawnFixture "silent" peerDir
      let (z3, cvc5) := if failedIsZ3 then (failed, peer) else (peer, failed)
      let env := environment .agree
        #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }] false
        (if failedIsZ3 then some 30 else none) (if failedIsZ3 then none else some 30)
      let started ← IO.monoMsNow
      let (message, _) ← (do
        try
          discard <| withSmtSessionOwner checkSat
          pure "agreement unexpectedly succeeded"
        catch error : Exception => error.toMessageData.toString).run env
      unless contains message "timedOut" do throwError "agreement erased infrastructure failure: {message}"
      assertWithin "failed agreement with unlimited peer" started 5000
      assertStopped "failed agreement solver" failed
      assertStopped "unlimited agreement peer" peer

private def testCancellationDuringCleanup : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "cleanup-cancel" directory
    awaitMarker (directory / "ready")
    let token ← IO.CancelToken.new
    let watcher ← IO.asTask do
      awaitMarker (directory / "term-requested")
      token.set
      IO.FS.writeFile (directory / "cancel-issued") ""
    let env := environment .single #[{ solver := .z3, process }]
    let (interrupted, _) ← withTheReader Core.Context
        (fun context => { context with cancelTk? := some token }) <| (do
      try
        withSmtSessionOwner (pure ())
        pure false
      catch error : Exception => pure error.isInterrupt).run env
    discard <| IO.ofExcept watcher.get
    unless interrupted do throwError "cleanup cancellation was lost"
    assertStopped "cancelled cleanup" process

private def testNormalOwnerUsesExitCommand : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "normal-exit" directory
    awaitMarker (directory / "ready")
    let env := environment .single #[{ solver := .z3, process }]
    discard <| (withSmtSessionOwner (pure ())).run env
    unless ← (directory / "exit-requested").pathExists do
      throwError "normal owner skipped the graceful exit command"
    assertStopped "normal owner" process

private def testZeroSearchTimeoutRemainsUnlimited : LifecycleM Unit := do
  IO.FS.withTempDir fun directory => do
    let process ← spawnFixture "silent" directory
    let token ← IO.CancelToken.new
    let cancellation ← IO.asTask do
      awaitMarker (directory / "check-requested")
      -- Outlive the erroneous zero-plus-1s hard deadline; no solver-speed assumption.
      IO.sleep 1300
      token.set
    let env := environment .single #[{ solver := .z3, process }] false (some 0)
    let (interrupted, _) ← withTheReader Core.Context
        (fun context => { context with cancelTk? := some token }) <| (do
      try
        discard <| withSmtSessionOwner checkSat
        pure false
      catch error : Exception => pure error.isInterrupt).run env
    discard <| IO.ofExcept cancellation.get
    unless interrupted do throwError "zero search timeout expired instead of awaiting cancellation"
    assertStopped "unlimited-search child" process

#eval withCleanup testNormalOwnerUsesExitCommand
#eval withCleanup testZeroSearchTimeoutRemainsUnlimited

#eval withCleanup testCancellationDuringCleanup
#eval withCleanup testAgreementFailureStopsUnlimitedPeer

#eval withCleanup testStartupAndReplayLimits

#eval withCleanup testUnsupportedEvidenceIsNotAConcreteValue

#eval withCleanup testVersionProbeDeadlineAndCancellation

#eval withCleanup testCleanupIgnoresExitAndTerm
#eval withCleanup testWrapperGrandchildrenAndInheritedPipes
#eval withCleanup testStderrFloodIsDrainedAndBounded
#eval withCleanup testSilentCommandAndBlockedWriteAreBounded
#eval withCleanup testSilentModelPreservesSatWithinEvidenceBudget
#eval withCleanup testReadyDisagreementNeverRequestsModels
#eval withCleanup testReadyUnknownDoesNotBeatDecisiveVerdict
#eval withCleanup <| withoutLoggedMessages testMalformedAndClosedRepliesRetainDiagnostics
#eval withCleanup testHandshakeCancellationAcrossStages

#eval withCleanup testZ3WinsAndCvc5IsReaped
#eval withCleanup testCvc5WinsAndZ3IsReaped
#eval withCleanup testLoserDeadBeforeWinnerModel
#eval withCleanup testClosedStdoutDoesNotBeatDecisiveSolver
#eval withCleanup testFirstRetiresRejectedDeclaration
#eval withCleanup testAgreeRejectsDeclarationWithArtifacts
#eval withCleanup testCrashPreservesStderrWithoutDuplicateCleanup
#eval withCleanup testAlreadyExitedChildIsHandled
#eval withCleanup testModelFailurePreservesSatVerdict
#eval withCleanup testOwnerCleansUnexpectedPrecheckException
#eval withCleanup testCancellationBeforeSolving
#eval withCleanup testCancellationDuringCommandSubmission
#eval withCleanup testCancellationReapsBothChildren
#eval withCleanup testCancellationDuringModelExtraction
#eval withCleanup testZ3TimeoutDoesNotBeatCvc5
#eval withCleanup testCvc5TimeoutDoesNotBeatZ3
#eval withCleanup <| withoutLoggedMessages testBothTimeoutsAreInfrastructureFailure
#eval withCleanup testSingleTimeoutIsVisibleFailure
#eval withCleanup testProtocolFailureDoesNotBeatHealthySolver
#eval withCleanup <| withoutLoggedMessages testInfrastructurePlusUnknownIsNotUndetermined
#eval withCleanup testBothOrdinaryUnknownRemainUndetermined
#eval withCleanup testAgreementUsesCompletePeerEvidence
#eval withCleanup testAgreementTimeoutIsInfrastructureFailure
#eval withCleanup testAgreementFailureSavesArtifacts

end Test.CrashLifecycle
