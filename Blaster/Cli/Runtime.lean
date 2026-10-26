import Blaster.Cli.Types
import Blaster.Smt.Solver

open Lean

namespace Blaster.Cli

private partial def findProject (directory : System.FilePath) : IO (Option System.FilePath) := do
  if (← (directory / "lakefile.lean").pathExists) ||
      (← (directory / "lakefile.toml").pathExists) then
    return some directory
  let some parent := directory.parent | return none
  if parent == directory then return none
  findProject parent

private def projectFor (file : Option String) : IO (Option System.FilePath) := do
  let cwd ← IO.currentDir
  if let some file := file then
    let path : System.FilePath := file
    let path := if path.isAbsolute then path else cwd / path
    if let some project ← findProject (path.parent.getD cwd) then return some project
  findProject cwd

/-- Installed commands use their recorded toolchain, independent of the caller's shell. -/
private def runtimeSysroot (bin : System.FilePath) : IO System.FilePath := do
  let metadata := bin / ".." / "libexec" / "lean-blaster" / "runtime.json"
  let sysroot ← if ← metadata.pathExists then do
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile metadata)
    let version ← IO.ofExcept <| json.getObjValAs? String "leanVersion"
    unless version == Lean.versionString do
      throw <| IO.userError "My installed libraries use a different Lean version. Reinstall lean-blaster."
    pure <| System.FilePath.mk (← IO.ofExcept <| json.getObjValAs? String "leanSysroot")
  else
    findSysroot
  unless ← (sysroot / "lib" / "lean" / "Init.olean").pathExists do
    throw <| IO.userError s!"I couldn't find my Lean {Lean.versionString} libraries at '{sysroot}'. Reinstall lean-blaster after restoring that toolchain."
  return sysroot

/-- Ask Lake for dependency paths internally; never expose its environment in CLI output. -/
private def projectPaths (cfg : Config) (sysroot : System.FilePath) : IO SearchPath := do
  if cfg.command != "check" then return []
  let some project ← projectFor cfg.file | return []
  let toolchain := project / "lean-toolchain"
  if ← toolchain.pathExists then
    let requested := (← IO.FS.readFile toolchain).trim
    if requested.startsWith "leanprover/lean4:" && requested != s!"leanprover/lean4:v{Lean.versionString}" then
      throw <| IO.userError s!"This project uses '{requested}', but I was built with Lean {Lean.versionString}. Use a matching lean-blaster installation."
  let lake := sysroot / "bin" / (if System.Platform.isWindows then "lake.exe" else "lake")
  let output ← IO.Process.output {
    cmd := lake.toString
    args := #["env"]
    cwd := some project
    env := #[("LEAN_SYSROOT", some sysroot.toString)] }
  unless output.exitCode == 0 do
    throw <| IO.userError s!"I couldn't load this project's dependencies.\n{output.stderr.trim}"
  for line in output.stdout.splitOn "\n" do
    if line.startsWith "LEAN_PATH=" then
      return (System.SearchPath.parse (line.drop 10)).map fun path =>
        if path.isAbsolute then path else project / path
  throw <| IO.userError "Lake didn't provide this project's dependency paths. Run 'lean-blaster doctor' to check the installation."

def initLibraries (cfg : Config) : IO Unit := do
  let bin ← Smt.installationBin
  let ownLib := bin / ".." / "lib" / "lean"
  let sysroot ← runtimeSysroot bin
  let project ← projectPaths cfg sysroot
  initSearchPath sysroot (ownLib :: project)

end Blaster.Cli
