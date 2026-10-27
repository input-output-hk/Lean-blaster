import Blaster.Cli.Types
import Blaster.Smt.Solver

open Lean

namespace Blaster.Cli

/-- Enumerate each physical Lean source once, in a stable order. Directory links are
    not traversed, so a linked tree cannot take an invocation outside its root. -/
private partial def collectSourceFiles (directory : System.FilePath)
    (seen : IO.Ref (Array System.FilePath)) : IO Unit := do
  let entries ← directory.readDir
  for entry in entries do
    let path := entry.path
    unless [".lake", ".git", "lakefile.lean"].contains entry.fileName do
      let metadata ← path.symlinkMetadata
      if metadata.type == .dir then
        collectSourceFiles path seen
      else if path.extension == some "lean" &&
          (metadata.type == .file || (metadata.type == .symlink && !(← path.isDir))) then
        let canonical ← Lean.realPathNormalized path
        unless (← seen.get).contains canonical do
          seen.modify (·.push canonical)

def sourceFiles (directory : System.FilePath) : IO (Array System.FilePath) := do
  let seen ← IO.mkRef (#[] : Array System.FilePath)
  collectSourceFiles directory seen
  return ((← seen.get).toList.mergeSort (fun a b => a.toString ≤ b.toString)).toArray

def sourceLabel (canonicalDirectory source : System.FilePath) : String := Id.run do
  let pathPrefix := canonicalDirectory.toString ++ "/"
  return if source.toString.startsWith pathPrefix then
    source.toString.drop pathPrefix.length else source.toString

private partial def findProject (directory : System.FilePath) : IO (Option System.FilePath) := do
  if (← (directory / "lakefile.lean").pathExists) ||
      (← (directory / "lakefile.toml").pathExists) then
    return some directory
  let some parent := directory.parent | return none
  if parent == directory then return none
  findProject parent

def projectFor (file : Option String) : IO (Option System.FilePath) := do
  let cwd ← IO.currentDir
  if let some file := file then
    let path : System.FilePath := file
    let path := if path.isAbsolute then path else cwd / path
    let searchFrom ← if ← path.isDir then pure path else pure (path.parent.getD cwd)
    if let some project ← findProject searchFrom then return some project
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
    -- Buffer Lake's stderr so warnings from successful dependency builds do not
    -- appear as results for the selected file. Expose it with --debug.
    args := #["--quiet", "--no-ansi", "setup-file", file.toString, (toJson header).compress]
    cwd := some project
    env := buildEnv } (if cfg.debug then onOutput else fun _ => pure ())
  unless output.exitCode == 0 do
    let details := "\n".intercalate <|
      [output.stderr.trim, output.stdout.trim].filter (!·.isEmpty)
    throw <| IO.userError s!"I couldn't prepare this file's imports.\n{details}\nFix the dependency build errors and try again. Use '--no-build' to manage builds yourself."
  -- Configurations may print their own messages; only the final setup JSON is protocol data.
  let lines := output.stdout.trim.splitOn "\n"
  let setupText := lines.getLast?.getD ""
  if cfg.debug then
    for line in lines.dropLast do onOutput (line ++ "\n")
  let setup ← IO.ofExcept <| Json.parse setupText >>= fromJson? (α := ModuleSetup)
  onStage "I'm elaborating the Lean file"
  return some setup

/-- Lake may ask us to load the project's Blaster plugin even though this executable
    already contains Blaster. Only reuse the executable's native code when every
    imported Blaster module is byte-for-byte the same as its installed artifact. -/
def reconcileBlasterPlugin (setup : ModuleSetup) : IO ModuleSetup := do
  let isBlasterPlugin (path : System.FilePath) : Bool :=
    ["libBlaster.dylib", "libBlaster.so", "Blaster.dll"].contains (path.fileName.getD "")
  unless setup.plugins.any isBlasterPlugin do return setup
  let bin ← Smt.installationBin
  let ownLib := bin / ".." / "lib" / "lean"
  let mut found := false
  for (name, arts) in setup.importArts.toList do
    let moduleName := name.toString
    if moduleName == "Blaster" || moduleName.startsWith "Blaster." then
      found := true
      let projectOlean ← match arts.olean? with
        | some path => pure path
        | none => throw (IO.userError s!"I couldn't identify the compiled artifact for {moduleName} in this project's Blaster dependency.")
      let ownOlean := ownLib / s!"{moduleName.replace "." "/"}.olean"
      let identical ← if ← ownOlean.pathExists then do
        pure ((← IO.FS.readBinFile ownOlean) == (← IO.FS.readBinFile projectOlean))
      else pure false
      unless identical do
        throw <| IO.userError s!"This project uses a different Blaster build ({projectOlean}). I can't load it alongside my own Blaster code. Point the project's Blaster dependency at the revision used to install lean-blaster, rebuild its dependencies, and try again."
  unless found do
    throw <| IO.userError "Lake selected a Blaster plugin without matching module artifacts. I can't safely load it alongside my own Blaster code."
  return { setup with plugins := setup.plugins.filter (!isBlasterPlugin ·) }

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
