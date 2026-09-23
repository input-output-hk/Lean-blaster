import Lean

namespace Blaster.Smt

/-- Transport budget, independent of the configured solver-search timeout. -/
def operationBudgetMs : Nat := 5000

/-- Aggregate setup/replay budget; individual exchanges retain the shorter transport limit. -/
def setupBudgetMs : Nat := 30000

/-- Maximum duration of post-verdict evidence collection. -/
def evidenceBudgetMs : Nat := 2000

private abbrev PipedChild := IO.Process.Child ⟨.piped, .piped, .piped⟩

@[extern "blaster_process_term_group"]
private opaque terminateGroup (pid : UInt32) : IO Unit

/-- POSIX observation without reaping; `Child.tryWait` would release the PID there. -/
@[extern "blaster_process_exited"]
private opaque processExited (pid : UInt32) : IO Bool

private structure ProcessState where
  tasks : Array (Task Unit) := #[]
  cleanup : Option (Task (Except IO.Error String)) := none

/--
A child whose pipes and termination belong to one lifecycle. Use `asTask` for every protocol read
or write, and `cleanup` rather than waiting for or killing the raw child. Stderr has exactly one
reader, installed by `spawn` before the process is returned.

On POSIX the child owns a new session/process group. Shutdown bounds the graceful and TERM phases,
then kills the whole group and joins all I/O before releasing ownership. Descendants that leave
the group (via `setpgid`/`setsid`), foreign/WSL process trees, uninterruptible kernel waits, and
arbitrary non-I/O actions passed to `asTask` are outside this guarantee. Native Windows retains Lean's direct-child semantics;
it does not claim descendant containment. No blocked task is silently detached on these paths.
-/
structure OwnedProcess where private mk ::
  private child : PipedChild
  private state : Std.Mutex ProcessState
  private drain : Task (Except IO.Error String)
  private exitCode : IO.Ref (Option UInt32)

namespace OwnedProcess

/-- The PID stays reserved until the lifecycle has finished sending group signals. -/
def pid (p : OwnedProcess) : UInt32 := p.child.pid

def stdin (p : OwnedProcess) : IO.FS.Handle := p.child.stdin

def stdout (p : OwnedProcess) : IO.FS.Handle := p.child.stdout

private def stderrLimit : Nat := 65536

/-- Preserve diagnostics even if stderr is malformed UTF-8 or the byte limit splits a character. -/
private def decodeDiagnostic (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  let mut i := 0
  while i < bytes.size do
    match String.utf8DecodeChar? bytes i with
    | some c =>
      result := result.push c
      i := i + c.utf8Size
    | none =>
      result := result.push '�'
      i := i + 1
  return result

private def drainStderr (handle : IO.FS.Handle) : IO String := do
  let mut captured := ByteArray.empty
  let mut truncated := false
  let mut failure := ""
  try
    repeat
      let chunk ← handle.read 4096
      if chunk.isEmpty then break
      let remaining := stderrLimit - captured.size
      if chunk.size > remaining then truncated := true
      if remaining > 0 then
        captured := captured ++ chunk.extract 0 remaining
  catch error =>
    failure := s!"\n[stderr read failed: {error}]"
  let text := (decodeDiagnostic captured).trim
  return text ++ (if truncated then "\n[stderr truncated after 65536 bytes]" else "") ++ failure

/-- Start the drain immediately; all callers get the same piped, privately owned process group. -/
def spawn (args : IO.Process.SpawnArgs) : IO OwnedProcess := do
  let state ← Std.Mutex.new ({} : ProcessState)
  let exitCode ← IO.mkRef none
  let child ← IO.Process.spawn { args with
    stdin := .piped, stdout := .piped, stderr := .piped
    setsid := !System.Platform.isWindows }
  let drain ← IO.asTask (drainStderr child.stderr) .dedicated
  return { child, state, drain, exitCode }

/-- Register I/O atomically with retirement, discarding completed registrations on each operation. -/
def asTask (p : OwnedProcess) (action : IO α) : IO (Task (Except IO.Error α)) :=
  p.state.atomically do
    let state ← get
    if state.cleanup.isSome then
      throw <| IO.userError "solver process has already been retired"
    let tasks ← state.tasks.filterM fun task => return !(← IO.hasFinished task)
    let task ← IO.asTask action .dedicated
    set { state with tasks := tasks.push (task.map (fun _ => ()) (sync := true)) }
    return task

/-- A non-reaping observation, serialized with the sole final wait. -/
def exited (p : OwnedProcess) : IO Bool :=
  p.state.atomically do
    if (← p.exitCode.get).isSome then return true
    -- On Windows `tryWait` polls the original HANDLE without releasing it.
    if System.Platform.isWindows then return (← p.child.tryWait).isSome
    processExited p.pid

private def waitForExit (p : OwnedProcess) (budgetMs : Nat) : IO Bool := do
  let deadline := (← IO.monoMsNow) + budgetMs
  repeat
    if ← p.exited then return true
    if (← IO.monoMsNow) ≥ deadline then return false
    IO.sleep 5
  return false

private def cleanupCore (p : OwnedProcess) (tasks : Array (Task Unit)) (hard : Bool) : IO String := do
  let mut diagnostics := ""
  let mut exitTask : Option (Task (Except IO.Error Unit)) := none
  -- Do not introduce a second writer while a registered operation is still using stdin.
  if !hard && (← tasks.allM fun task => return (← IO.hasFinished task)) then
    exitTask := some (← IO.asTask (do p.stdin.putStr "(exit)\n"; p.stdin.flush) .dedicated)
  let mut exited := false
  if !hard then
    try exited ← waitForExit p 100
    catch error => diagnostics := diagnostics ++ s!"\n[exit observation failed: {error}]"
  if !exited && !System.Platform.isWindows then
    try terminateGroup p.pid
    catch error => diagnostics := diagnostics ++ s!"\n[process-group TERM failed: {error}]"
    try discard <| waitForExit p 100
    catch error => diagnostics := diagnostics ++ s!"\n[exit observation failed: {error}]"
  -- Even a naturally exited leader can leave grandchildren holding pipes open. Never reap it
  -- until the last group signal has been sent: the unreaped leader reserves its PID/PGID.
  try p.child.kill
  catch error => diagnostics := diagnostics ++ s!"\n[process kill failed: {error}]"
  let reaped ← p.state.atomically do
    let result ← p.child.wait.toBaseIO
    if let .ok code := result then p.exitCode.set (some code)
    return result
  if let .error error := reaped then
    diagnostics := diagnostics ++ s!"\n[process wait failed: {error}]"
  for task in tasks do discard <| IO.wait task
  if let some task := exitTask then discard <| IO.wait task
  let stderr ← IO.wait p.drain
  match stderr with
  | .ok text => return text ++ diagnostics
  | .error error => return s!"[stderr drain failed: {error}]" ++ diagnostics

/--
Retire, terminate and reap once, then join registered I/O and the already-running stderr drain.
Concurrent and repeated calls share the first cleanup task and its diagnostics. No new I/O is
accepted once retirement begins. `hard` skips the protocol-exit grace period, not ownership joins.
-/
def cleanup (p : OwnedProcess) (hard : Bool := false) : IO String := do
  let task ← p.state.atomically do
    let state ← get
    if let some task := state.cleanup then return task
    let task ← IO.asTask (cleanupCore p state.tasks hard) .dedicated
    set { state with tasks := #[], cleanup := some task }
    return task
  IO.ofExcept (← IO.wait task)

/-- Bounded noninteractive invocation, with the same ownership as an interactive session. -/
def output (args : IO.Process.SpawnArgs) (deadline : Nat)
    (cancelTk? : Option IO.CancelToken := none) : IO IO.Process.Output := do
  let checkActive : IO Unit := do
    if let some token := cancelTk? then
      if ← token.isSet then throw <| IO.userError "operation cancelled"
    if (← IO.monoMsNow) ≥ deadline then
      throw <| IO.userError "operation deadline exceeded"
  checkActive
  let process ← spawn args
  try
    let response ← process.asTask process.stdout.readToEnd
    while !(← IO.hasFinished response) || !(← process.exited) do
      checkActive
      IO.sleep 5
    checkActive
    let stdout ← IO.ofExcept response.get
    let stderr ← process.cleanup true
    let some exitCode ← process.exitCode.get
      | throw <| IO.userError "child exit status unavailable after cleanup"
    return { exitCode, stdout, stderr }
  catch error =>
    let stderr ← process.cleanup true
    throw <| IO.userError s!"{error}\n{stderr}"

end OwnedProcess
end Blaster.Smt
