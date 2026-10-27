import Blaster.Smt.Env

namespace Test.CrashLifecycle

open Lean Blaster.Optimize Blaster.Smt

private abbrev PipedChild :=
  IO.Process.Child ⟨.piped, .piped, .piped⟩

private structure Observation where
  message : String
  processCleared : Bool

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def spawnFakeChild (stderr : String) (stayAlive : Bool) : IO PipedChild :=
  let script :=
    if stayAlive then
      s!"echo '{stderr}' >&2; exec 1>&-; exec sleep 10"
    else
      s!"echo '{stderr}' >&2; exit 17"
  IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", script]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

private def observeClosedStdout (p : PipedChild) : MetaM Observation := do
  let env : TranslateEnv := default
  let env := { env with smtEnv.smtProc := some p }
  let (observation, _) ← (do
    let message ←
      try
        discard (getSatResult p)
        pure "solver unexpectedly returned a result"
      catch e : Exception =>
        e.toMessageData.toString
    let processCleared := (← get).smtEnv.smtProc.isNone
    return (Observation.mk message processCleared)).run env
  return observation

private def assertCrash
    (label stderr : String) (observation : Observation) : MetaM Unit := do
  unless contains observation.message "solver closed its output stream" do
    throwError "{label}: contextual solver EOF error was lost:\n{observation.message}"
  unless contains observation.message stderr do
    throwError "{label}: solver stderr was lost:\n{observation.message}"
  if contains observation.message "no such process" ||
      contains observation.message "No such process" then
    throwError "{label}: duplicate cleanup masked the solver failure:\n{observation.message}"
  unless observation.processCleared do
    throwError "{label}: retired solver remained installed in smtProc"

private def testCrashLifecycle : MetaM Unit := do
  let liveStderr := "FAKE_LIVE_CHILD: deliberate stderr"
  let live ← spawnFakeChild liveStderr true
  assertCrash "live child" liveStderr (← observeClosedStdout live)

  let deadStderr := "FAKE_DEAD_CHILD: deliberate stderr"
  let dead ← spawnFakeChild deadStderr false
  assertCrash "already-dead child" deadStderr (← observeClosedStdout dead)

#guard_msgs in
#eval testCrashLifecycle

end Test.CrashLifecycle
