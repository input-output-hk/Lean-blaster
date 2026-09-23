import Blaster.Smt.Env

namespace Test.ResponseLifecycle

open Lean Blaster.Options Blaster.Optimize Blaster.Smt

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

-- This child uses shell builtins only. No descendant can keep its pipes open.
-- Each marker records a command that the child has received.
private def spawnChild (directory : System.FilePath) (name verdict model : String) : IO PipedChild :=
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c",
      "while IFS= read -r line; do case \"$line\" in " ++
      s!"'(check-sat)'*) echo ready > '{directory / (name ++ ".check")}'; " ++
      (if verdict == "stall" then ""
       else if verdict == "eof" then "echo CHECK_FAILURE >&2; exit 17; "
       else s!"echo '{verdict}'; ") ++
      ";; '(get-model)'|'(get-value ('*) " ++
      s!"echo ready > '{directory / (name ++ ".model")}'; " ++
      (if model == "stall" then ""
       else if model == "eof" then "echo MODEL_FAILURE >&2; exit 18; "
       else s!"echo '{model}'; ") ++
      ";; '(exit)') exit 0;; esac; done"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

private def environment (mode : SolverMode) (sessions : Array SolverSession)
    (generateCex : Bool := true) (values : Bool := false) : TranslateEnv :=
  let base : TranslateEnv := default
  { base with
    optEnv.options.solverOptions := { solverMode := mode, generateCex }
    smtEnv.sessions := sessions
    smtEnv.configuredSolvers := sessions.map (·.solver)
    smtEnv.singleSolver := if mode == .single then sessions[0]?.map (·.solver) else none
    smtEnv.solverRecords := sessions.map fun session =>
      { solver := session.solver, version := "fake", commandLine := "shell builtins", setupCommands := #[] }
    smtEnv.topLevelVars := if values then #[[(mkNormalSymbol "x", `x)]] else #[] }

private def assertStopped (session : SolverSession) : MetaM Unit := do
  let output ← IO.Process.output { cmd := "/bin/kill", args := #["-0", toString session.process.pid] }
  unless output.exitCode != 0 do
    throwError "{session.solver}: child {session.process.pid} is still alive"

-- The watchdog starts its response interval only after the child is ready.
-- On expiry it kills the direct children. The normal cleanup path reaps them.
private partial def watch (ready : System.FilePath) (done : IO.Ref Bool)
    (expire : IO Unit) (startupDeadline : Nat) (responseMs : Nat) : IO Unit := do
  if ← done.get then return
  if ← ready.pathExists then
    let deadline := (← IO.monoMsNow) + responseMs
    waitUntilDone deadline
  else if (← IO.monoMsNow) ≥ startupDeadline then expire
  else
    IO.sleep 10
    watch ready done expire startupDeadline responseMs
where
  waitUntilDone (deadline : Nat) : IO Unit := do
    if ← done.get then return
    if (← IO.monoMsNow) ≥ deadline then expire
    else
      IO.sleep 10
      waitUntilDone deadline

private def runCheck (env : TranslateEnv) (ready : System.FilePath) (responseMs : Nat) :
    MetaM (Except String Result × TranslateEnv) := do
  let expired ← IO.mkRef false
  let done ← IO.mkRef false
  let startupDeadline := (← IO.monoMsNow) + 5000
  let expire : IO Unit := do
    expired.set true
    for session in env.smtEnv.sessions do
      try session.process.kill catch _ => pure ()
  let watchdog ← IO.asTask (watch ready done expire startupDeadline responseMs) Task.Priority.dedicated
  try
    let result ← (do
      let result : Except String Result ← try
        pure (Except.ok (← withSmtSessionOwner checkSat) : Except String Result)
      catch error : Exception => pure (Except.error (← error.toMessageData.toString) : Except String Result)
      return result).run env
    if ← expired.get then
      throwError "Response watchdog expired after readiness: {ready.fileName}"
    return result
  finally
    done.set true
    let _ := watchdog.get
    for session in env.smtEnv.sessions do assertStopped session

private def inTempDirectory (action : System.FilePath → MetaM Unit) : MetaM Unit := do
  let original ← IO.currentDir
  IO.FS.withTempDir fun directory => do
    try
      IO.Process.setCurrentDir directory
      action directory
    finally
      IO.Process.setCurrentDir original

private def testAgreementFailure (failedSolver : SmtSolver) : MetaM Unit :=
  inTempDirectory fun directory => do
    let z3 ← spawnChild directory "z3" (if failedSolver == .z3 then "eof" else "stall") "stall"
    let cvc5 ← spawnChild directory "cvc5" (if failedSolver == .cvc5 then "eof" else "stall") "stall"
    let sessions := #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    let (result, _) ← runCheck (environment .agree sessions) (directory / "cvc5.check") 1500
    match result with
    | .error message =>
        unless contains message "CHECK_FAILURE" && contains message "Agreement artifacts" do
          throwError "Agreement waited after {failedSolver} failed: {message}"
    | .ok result => throwError "Agreement accepted a failed solver: {reprStr result}"

#eval testAgreementFailure .z3
#eval testAgreementFailure .cvc5

end Test.ResponseLifecycle
