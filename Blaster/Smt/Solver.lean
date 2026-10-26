import Blaster.Smt.Process

namespace Blaster.Smt

structure SolverInfo where
  path : String
  source : String
  version : String
  deriving Lean.ToJson

/-- Resolve launch symlinks before looking up resources in an installation. -/
def installationBin : IO System.FilePath := do
  return (← IO.FS.realPath (← IO.appPath)).parent.getD "."

/-- An explicit selection never falls back silently to a different solver. -/
def probeSolver (path source : String) : IO SolverInfo := do
  let out ← solverOutput path #["-version"]
  unless out.exitCode == 0 do
    throw <| IO.userError s!"I couldn't run Z3 at '{path}': {out.stderr.trim}"
  unless out.stdout.startsWith "Z3 version " do
    throw <| IO.userError s!"'{path}' didn't identify itself as Z3"
  return { path, source, version := out.stdout.trim }

/-- Release bundles put Z3 under libexec; a sibling binary also supports portable layouts. -/
def resolveSolver (explicit : Option String := none) : IO SolverInfo := do
  if let some path := explicit then return ← probeSolver path "explicit"
  if let some path ← IO.getEnv "BLASTER_SOLVER" then
    unless path.isEmpty do return ← probeSolver path "environment"
  let bin ← installationBin
  let name := if System.Platform.isWindows then "z3.exe" else "z3"
  for candidate in #[bin / ".." / "libexec" / "lean-blaster" / name, bin / name] do
    if ← candidate.pathExists then
      -- A broken bundled solver is an installation error, not a reason to change versions.
      return ← probeSolver candidate.toString "bundled"
  try
    probeSolver "z3" "PATH"
  catch _ =>
    throw <| IO.userError "I couldn't find Z3 in this installation or on PATH.\n\n  Select an installed solver with '--solver /path/to/z3', or run 'lean-blaster doctor'."

end Blaster.Smt
