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

/-- Find source imports belonging to the caller's project, without building them. -/
def localSourceFor (cfg : Config) (moduleName : Name) : IO (Option System.FilePath) := do
  let name := moduleName.toString
  if name == "Blaster" || name.startsWith "Blaster." then return none
  let some project ← projectFor cfg.file | return none
  let source := project / s!"{name.replace "." "/"}.lean"
  if ← source.pathExists then return some source
  return none

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
  let output ← Smt.commandOutput {
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

/-- Lake prepares imports and native dependencies without elaborating the selected file. -/
def prepareImports (cfg : Config) (header : ModuleHeader)
    (onStage onOutput : String → IO Unit) : IO (Option ModuleSetup) := do
  if cfg.noBuild then return none
  let some project ← projectFor cfg.file | return none
  let file : System.FilePath := cfg.file.getD ""
  let cwd ← IO.currentDir
  let file := if file.isAbsolute then file else cwd / file
  let sysroot ← runtimeSysroot (← Smt.installationBin)
  let lake := sysroot / "bin" / (if System.Platform.isWindows then "lake.exe" else "lake")
  -- Blaster itself comes from this executable's matching installation, including in projects
  -- which do not declare Blaster as a Lake dependency. Other imports are prepared by Lake.
  let header := { header with imports := header.imports.filter fun imp =>
    let name := imp.module.toString
    name != "Blaster" && !name.startsWith "Blaster." }
  let mut buildEnv := #[("LEAN_SYSROOT", some sysroot.toString)]
  if let some selected := cfg.solver then
    let path : System.FilePath := selected
    let selected := if !path.isAbsolute && (selected.contains '/' || selected.contains '\\') then
      (cwd / path).toString else selected
    buildEnv := buildEnv.push ("BLASTER_SOLVER", some selected)
  else if (← IO.getEnv "BLASTER_SOLVER").getD "" |>.isEmpty then
    let bin ← Smt.installationBin
    let solver := bin / ".." / "libexec" / "lean-blaster" /
      (if System.Platform.isWindows then "z3.exe" else "z3")
    if ← solver.pathExists then buildEnv := buildEnv.push ("BLASTER_SOLVER", some solver.toString)
  onStage "I'm compiling imported Lean modules"
  let output ← Smt.commandOutput {
    cmd := lake.toString
    -- Lake still reports failing jobs, while successful proof logs stay out of
    -- the CLI report and no longer flood the terminal before the selected check.
    args := #["--quiet", "--no-ansi", "setup-file", file.toString, (toJson header).compress]
    cwd := some project
    env := buildEnv } onOutput
  unless output.exitCode == 0 do
    throw <| IO.userError s!"I couldn't prepare this file's imports.\n{output.stderr.trim}\nFix the dependency build errors and try again. Use '--no-build' to manage builds yourself."
  -- Configurations may print their own messages; only the final setup JSON is protocol data.
  let lines := output.stdout.trim.splitOn "\n"
  let setupText := lines.getLast?.getD ""
  for line in lines.dropLast do onOutput (line ++ "\n")
  let setup ← IO.ofExcept <| Json.parse setupText >>= fromJson? (α := ModuleSetup)
  onStage "I'm elaborating the Lean file"
  return some setup

def initLibraries (cfg : Config) : IO Unit := do
  let bin ← Smt.installationBin
  let ownLib := bin / ".." / "lib" / "lean"
  let sysroot ← runtimeSysroot bin
  let project ← projectPaths cfg sysroot
  initSearchPath sysroot (ownLib :: project)

/-- Discovery only needs the executable's own parser, not project builds or solver setup. -/
def initDiscoveryLibraries : IO Unit := do
  let bin ← Smt.installationBin
  let ownLib := bin / ".." / "lib" / "lean"
  let sysroot ← runtimeSysroot bin
  initSearchPath sysroot [ownLib]

end Blaster.Cli
