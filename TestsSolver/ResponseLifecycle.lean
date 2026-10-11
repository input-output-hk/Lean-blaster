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

private def testDisagreementBeforeModel (satSolver : SmtSolver) : MetaM Unit :=
  inTempDirectory fun directory => do
    let z3 ← spawnChild directory "z3" (if satSolver == .z3 then "sat" else "unsat") "stall"
    let cvc5 ← spawnChild directory "cvc5" (if satSolver == .cvc5 then "sat" else "unsat") "stall"
    let sessions := #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    let (result, _) ← runCheck (environment .agree sessions) (directory / "cvc5.check") 1500
    match result with
    | .error message =>
        unless contains message "Hard solver disagreement" do
          throwError "A model wait hid disagreement for {satSolver}: {message}"
    | .ok result => throwError "Agreement accepted opposite verdicts: {reprStr result}"
    for name in ["z3", "cvc5"] do
      if ← (directory / (name ++ ".model")).pathExists then
        throwError "Agreement requested a model before reporting disagreement"

private def testModelFailure (solver : SmtSolver) (values : Bool) (model : String) : MetaM Unit :=
  inTempDirectory fun directory => do
    let process ← spawnChild directory "solver" "sat" model
    let sessions := #[{ solver, process }]
    let (result, finalEnv) ← runCheck (environment .single sessions true values)
      (directory / "solver.model") 7000
    match result with
    | .ok (.Falsified _) => pure ()
    | other => throwError "Model failure lost Falsified ({solver}, values={values}): {reprStr other}"
    let some record := finalEnv.smtEnv.solverRecords[0]? | throwError "Missing solver diagnostics"
    let diagnostic := record.failureResponse.getD ""
    unless contains diagnostic (if model == "stall" then "timeout" else if model == "eof" then "MODEL_FAILURE" else "raw response") do
      throwError "Model failure lost its details: {diagnostic}"

private def testAgreementModelTimeout (timedSolver : SmtSolver) : MetaM Unit :=
  inTempDirectory fun directory => do
    let z3 ← spawnChild directory "z3" "sat" (if timedSolver == .z3 then "stall" else "((x 42))")
    let cvc5 ← spawnChild directory "cvc5" "sat" (if timedSolver == .cvc5 then "stall" else "((x 42))")
    let sessions := #[{ solver := .z3, process := z3 }, { solver := .cvc5, process := cvc5 }]
    let (result, _) ← runCheck (environment .agree sessions true true)
      (directory / s!"{timedSolver}.model") 7000
    match result with
    | .ok (.Falsified ["x: 42"]) => pure ()
    | other => throwError "Agreement lost the complete peer values: {reprStr other}"

#eval testAgreementFailure .z3
#eval testAgreementFailure .cvc5
#eval testDisagreementBeforeModel .z3
#eval testDisagreementBeforeModel .cvc5
#eval testModelFailure .z3 false "stall"
#eval testModelFailure .cvc5 true "stall"
#eval testModelFailure .z3 false "eof"
#eval testModelFailure .cvc5 true "not-a-value"
#eval testAgreementModelTimeout .z3
#eval testAgreementModelTimeout .cvc5

end Test.ResponseLifecycle
