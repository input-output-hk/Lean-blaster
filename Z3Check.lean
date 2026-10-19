/- Verify the solver capability required by Blaster, not just its version label.
   Run `lake exe z3check` with the intended solver directory first in PATH. -/
import Lean

def main : IO UInt32 := do
  try
    let version ← IO.Process.output { cmd := "z3", args := #["--version"] }
    unless version.exitCode == 0 do
      IO.eprintln s!"Failed to run z3: {version.stderr}"
      return 1
    let child ← IO.Process.spawn {
      cmd := "z3", args := #["-in"], stdin := .piped, stdout := .piped, stderr := .piped }
    child.stdin.putStr "(set-simplifier recfun-finder)\n(check-sat)\n(exit)\n"
    child.stdin.flush
    let output ← child.stdout.readToEnd
    let errors ← child.stderr.readToEnd
    let status ← child.wait
    unless status == 0 && output.trim == "sat" && errors.trim.isEmpty do
      IO.eprintln s!"Z3 lacks the required recfun-finder capability.\n{output}{errors}"
      return 1
    IO.println s!"{version.stdout.trim}: recfun-finder available"
    return 0
  catch error =>
    IO.eprintln s!"Solver setup failed: {error}"
    return 1
