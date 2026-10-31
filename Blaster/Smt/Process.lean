import Lean
import Std.Sync.Mutex

namespace Blaster.Smt

abbrev SolverProcess := IO.Process.Child ⟨.piped, .piped, .piped⟩
private abbrev TrackedProcess := IO.Process.Child ⟨.null, .piped, .piped⟩

private structure Processes where
  enabled : Bool := false
  cancelled : Bool := false
  children : Array TrackedProcess := #[]
  forceKill : UInt32 → IO Unit := fun _ => pure ()

private initialize processes : IO.Ref (Option (Std.Mutex Processes)) ← do
  IO.mkRef (some (← Std.Mutex.new {}))

private def processLock : IO (Std.Mutex Processes) := do
  let some lock ← processes.get | throw <| IO.userError "The solver supervisor wasn't initialized"
  return lock

/-- Only the standalone CLI enables supervision. The library retains its normal lifecycle. -/
def superviseSolvers (forceKill : UInt32 → IO Unit) : IO Unit := do
  (← processLock).atomically <| set ({ enabled := true, forceKill } : Processes)

def spawnSolver (args : IO.Process.SpawnArgs) : IO SolverProcess := do
  (← processLock).atomically do
    let state ← get
    if state.cancelled then throw <| IO.userError "I stopped this check"
    let child ← IO.Process.spawn { args with
      stdin := .piped, stdout := .piped, stderr := .piped
      setsid := state.enabled || args.setsid }
    if state.enabled then
      -- The registry must not keep stdin alive after a caller closes it.
      let (_, tracked) ← child.takeStdin
      set { state with children := state.children.push tracked }
    return child

/-- Serialize reaping with cancellation so a saved PID can never refer to a reused process. -/
partial def waitSolver {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO UInt32 := do
  let lock ← processLock
  unless ← lock.atomically (return (← get).enabled) do return ← child.wait
  let result ← lock.atomically do
    let state ← get
    if let some code ← child.tryWait then
      set { state with children := state.children.filter (·.pid != child.pid) }
      return some code
    return none
  if let some code := result then return code
  IO.sleep 10
  waitSolver child

private partial def readOutput (handle : IO.FS.Handle) (emit : String → IO Unit)
    (output : String := "") : IO String := do
  let line ← handle.getLine
  if line.isEmpty then return output
  emit line
  readOutput handle emit (output ++ line)

def commandOutput (args : IO.Process.SpawnArgs)
    (onStderr : String → IO Unit := fun _ => pure ()) : IO IO.Process.Output := do
  let child ← spawnSolver args
  let (_, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readToEnd
  let stderr ← IO.asTask <| readOutput child.stderr onStderr
  -- Keep the leader unreaped until inherited pipes close. A cancelled wrapper may
  -- already have exited while its descendants are still alive in the group.
  let stdout ← IO.ofExcept stdout.get
  let stderr ← IO.ofExcept stderr.get
  let code ← waitSolver child
  return { exitCode := code, stdout, stderr }

/-- Version probes are supervised too, so a broken executable cannot survive cancellation. -/
def solverOutput (path : String) (args : Array String) : IO IO.Process.Output :=
  commandOutput { cmd := path, args }

/-- Freeze new spawns, kill every live solver, and reap it before returning an interrupted report. -/
def stopSolvers : IO Unit := do
  (← processLock).atomically do
    let state ← get
    set { state with cancelled := true, children := #[] }
    for child in state.children do
      -- Kill the group before reaping its leader; its PID is still reserved here.
      try state.forceKill child.pid catch _ => try child.kill catch _ => pure ()
      discard <| child.wait

end Blaster.Smt
