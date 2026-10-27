import Blaster.Cli.Args
import Blaster.Cli.Check
import Blaster.Cli.Discover
import Blaster.Cli.Llm
import Blaster.Smt.Solver
import Blaster.Cli.Runtime

open Lean

namespace Blaster.Cli

private def doctorData (cfg : Config) : IO (Array Diagnostic × Option Smt.SolverInfo) := do
  let mut diagnostics : Array Diagnostic := #[]
  let mut solver : Option Smt.SolverInfo := none
  try
    discard <| findOLean `Blaster
  catch ex =>
    diagnostics := diagnostics.push {
      severity := "error"
      message := s!"I couldn't find my compiled libraries. Reinstall lean-blaster.\n{ex}" }
  try
    solver := some (← Smt.resolveSolver cfg.solver)
  catch ex =>
    diagnostics := diagnostics.push { severity := "error", message := ex.toString }
  return (diagnostics, solver)

private def renderDoctor (cfg : Config) (renderer : Renderer)
    (diagnostics : Array Diagnostic) (solver : Option Smt.SolverInfo) : IO UInt32 := do
  let code : UInt32 := if diagnostics.isEmpty then 0 else 4
  if cfg.jsonReport then
    renderer.out.putStrLn <| Json.compress <| Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)), ("command", toJson "doctor"),
      ("leanVersion", toJson Lean.versionString), ("solver", toJson solver),
      ("diagnostics", toJson diagnostics), ("exitCode", toJson code.toNat)]
  else if cfg.json then
    renderer.emitJsonLine <| Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)), ("event", toJson "doctor"),
      ("leanVersion", toJson Lean.versionString), ("solver", toJson solver)]
    renderer.finish { diagnostics := diagnostics }
  else
    renderer.out.putStrLn s!"\n  {renderer.tintOut "identity" "blaster"} · setup\n\n  Lean {Lean.versionString}"
    if let some selectedSolver := solver then
      renderer.out.putStrLn s!"  {selectedSolver.version}\n  Solver: {selectedSolver.path} ({selectedSolver.source})"
    for diagnostic in diagnostics do renderer.err.putStrLn s!"\n  error: {diagnostic.message}"
    if code == 0 then renderer.out.putStrLn "\n  I can find Blaster's compiled libraries and run Z3. We're ready to check properties."
  return code

/-- Signals are polled outside elaboration, including during blocking source IO and solver probes. -/
private partial def awaitTask (renderer : Renderer) (task : Task (Except IO.Error α)) : IO (Except Report α) := do
  if ← IO.hasFinished task then return .ok (← IO.ofExcept task.get)
  let signal ← renderer.platform.signal
  if signal != 0 then
    renderer.stop.set true
    let mut report ← interruptCapture signal.toNat
    -- New solver spawns are excluded while this set is killed and reaped.
    try Smt.stopSolvers catch ex =>
      report := { report with diagnostics := report.diagnostics.push {
        severity := "error", message := s!"I couldn't finish stopping a supervised process: {ex}" } }
    return .error report
  IO.sleep 20
  awaitTask renderer task

private def finishReport (renderer : Renderer) (report : Report) : IO UInt32 := do
  renderer.finish report
  -- Source IO may not cooperate with Lean cancellation. Solvers are already reaped;
  -- exiting here prevents abandoned worker threads from delaying an interrupted command.
  if report.interrupted then IO.Process.exit report.exitCode.toUInt8
  return report.exitCode

private def finishCheckReport (cfg : Config) (renderer : Renderer) (report : Report) : IO UInt32 := do
  let mut report := report
  let mut written := false
  if cfg.llmReport.isSome then
    try
      writeLlmReport cfg report
      written := true
    catch ex =>
      report := { report with diagnostics := report.diagnostics.push {
        severity := "error", message := s!"I couldn't write the agent report: {ex}" } }
  let code ← finishReport renderer report
  if written && !cfg.machineOutput then
    renderer.out.putStrLn s!"  I wrote the agent report to {cfg.llmReport.getD ""}"
  return code

private def runDiscover (cfg : Config) (renderer : Renderer) : IO UInt32 := do
  let depth ← IO.mkRef 0
  let found ← IO.mkRef (#[] : Array DiscoveryItem)
  unless cfg.machineOutput do
    renderer.out.putStrLn s!"\n  {renderer.tintOut "identity" "blaster"} · discover {cfg.file.getD ""}\n"
  let onModuleStart := fun (label : String) => do
    if cfg.json then
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "moduleStart"),
        ("module", toJson label)]
    else unless cfg.jsonReport do
      let indent := String.join (List.replicate (← depth.get) "  ")
      renderer.out.putStrLn s!"  {indent}{renderer.tintOut "action" label}"
    depth.modify (· + 1)
  let onItem := fun (item : DiscoveryItem) => do
    found.modify (·.push item)
    if cfg.json then
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "discovery"),
        ("item", toJson item)]
    else unless cfg.jsonReport do
      let indent := String.join (List.replicate (← depth.get) "  ")
      let label := item.name.getD (if item.kind == "command" then "#blaster" else "<anonymous proof>")
      let pos := item.invocationRange.start
      renderer.out.putStrLn s!"  {indent}{renderer.tintOut "action" label} · {pos.file}:{pos.line}:{pos.column}"
      for line in item.body.splitOn "\n" do
        renderer.out.putStrLn s!"    {indent}{line}"
  let onModuleComplete := fun (label : String) (count : Nat) => do
    depth.modify (· - 1)
    if cfg.json then
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "moduleComplete"),
        ("module", toJson label), ("discoveryCount", toJson count)]
    else unless cfg.jsonReport do
      let indent := String.join (List.replicate (← depth.get) "  ")
      renderer.out.putStrLn s!"  {indent}{count} discovered\n"
  let diagnostics ← try
    let path : System.FilePath := cfg.file.getD ""
    let (_, issues) ← if ← path.isDir then
      discoverDirectory cfg onModuleStart onItem onModuleComplete
    else
      discoverFile cfg onModuleStart onItem onModuleComplete
    pure issues
  catch ex =>
    pure #[{ severity := "error", message := s!"I couldn't discover Blaster sites: {ex}" }]
  let items ← found.get
  let code : UInt32 := if diagnostics.any (·.severity == "error") then 4 else 0
  if cfg.json then
    for diagnostic in diagnostics do
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "diagnostic"),
        ("diagnostic", toJson diagnostic)]
    renderer.emitJsonLine <| Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)), ("event", toJson "complete"),
      ("exitCode", toJson code.toNat), ("discoveryCount", toJson items.size),
      ("diagnosticCount", toJson diagnostics.size),
      ("elapsedMs", toJson ((← IO.monoMsNow) - renderer.started))]
  else if cfg.jsonReport then
    renderer.out.putStrLn <| Json.compress <| Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)), ("command", toJson "discover"),
      ("discoveries", toJson items), ("diagnostics", toJson diagnostics),
      ("exitCode", toJson code.toNat)]
  else
    for diagnostic in diagnostics do
      renderer.err.putStrLn s!"\n  {diagnostic.severity}: {diagnostic.message}"
    renderer.out.putStrLn s!"\n  I found {items.size} Blaster sites."
  return code

def run (args : List String) (platform : Platform := {}) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
    let options := args.takeWhile (· != "--")
    let cfg : Config := { json := options.contains "--json", jsonReport := options.contains "--json-report" }
    let renderer ← Renderer.create cfg platform
    if cfg.json then
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "start"),
        ("command", toJson "parse")]
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "diagnostic"),
        ("diagnostic", toJson ({ severity := "error", message := message } : Diagnostic))]
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "complete"),
        ("exitCode", toJson (2 : Nat)), ("counts", Json.mkObj [
          ("valid", toJson (0 : Nat)), ("falsified", toJson (0 : Nat)),
          ("undetermined", toJson (0 : Nat)), ("error", toJson (0 : Nat)),
          ("skipped", toJson (0 : Nat))]),
        ("diagnosticCount", toJson (1 : Nat)), ("interrupted", toJson false),
        ("discoveryCount", toJson (0 : Nat)),
        ("signal", toJson (none : Option Nat)),
        ("elapsedMs", toJson ((← IO.monoMsNow) - renderer.started)),
        ("trust", toJson ({} : Report).trust)]
    else if cfg.jsonReport then
      if options.contains "discover" then
        renderer.out.putStrLn <| Json.compress <| Json.mkObj [
          ("schemaVersion", toJson (1 : Nat)), ("command", toJson "discover"),
          ("discoveries", toJson (#[] : Array DiscoveryItem)),
          ("diagnostics", toJson #[{ severity := "error", message : Diagnostic }]),
          ("exitCode", toJson (2 : Nat))]
      else
        renderer.out.putStrLn <| Json.compress <| Json.mkObj [
          ("schemaVersion", toJson (1 : Nat)), ("results", toJson (#[] : Array CheckResult)),
          ("diagnostics", toJson #[{ severity := "error", message : Diagnostic }]),
          ("exitCode", toJson (2 : Nat))]
    else renderer.err.putStrLn s!"\n  error: {message}\n"
    return 2
  | .ok cfg =>
    let renderer ← Renderer.create cfg platform
    if cfg.version then
      renderer.out.putStrLn s!"lean-blaster (development) · Lean {Lean.versionString}"
      return 0
    if cfg.help || cfg.command == "help" then
      renderer.out.putStr (helpText cfg.command)
      return 0
    let target : System.FilePath := cfg.file.getD ""
    if cfg.json then
      renderer.emitJsonLine <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("event", toJson "start"),
        ("command", toJson cfg.command), ("file", toJson cfg.file)]
    try
      if cfg.command == "discover" then
        return ← runDiscover cfg renderer
      if cfg.command == "check" && (← target.isDir) && !cfg.declarations.isEmpty then
        let report : Report := { diagnostics := #[{
          severity := "error",
          message := "'--decl' selects declarations in one file. Pass a .lean file when using it." }] }
        return ← finishCheckReport cfg renderer report
      Smt.superviseSolvers platform.forceKill
      resetCapture {
        config := cfg
        onStage := renderer.setStage, onResult := renderer.result }
      if cfg.command == "doctor" then
        let task ← IO.asTask do
          initLibraries cfg
          doctorData cfg
        match ← awaitTask renderer task with
        | .ok (diagnostics, solver) => return ← renderDoctor cfg renderer diagnostics solver
        | .error report => return ← finishReport renderer report
      unless cfg.machineOutput do
        renderer.out.putStrLn s!"\n  {renderer.tintOut "identity" "blaster"} · {cfg.file.getD ""}\n\n  I'm checking your properties.\n"
        renderer.out.flush
      let animation ← if renderer.live then
        some <$> IO.asTask renderer.animate else pure none
      let report ← try
        let task ← IO.asTask do
          initLibraries cfg
          -- The executable also redirects OS stdout, covering inherited subprocess output.
          IO.withStdout renderer.err <|
            if ← target.isDir then checkDirectory cfg renderer else checkFile cfg renderer
        match ← awaitTask renderer task with
        | .ok report => pure report
        | .error report => pure report
      catch ex =>
        let capturedReport := (← readCapture).report
        let failure : Diagnostic := { severity := "error", message := s!"I couldn't complete the check: {ex}" }
        pure { capturedReport with diagnostics := capturedReport.diagnostics.push failure }
      finally
        renderer.stop.set true
        if let some task := animation then discard <| IO.ofExcept task.get
        renderer.clear
      finishCheckReport cfg renderer report
    catch ex =>
      let report : Report := {
        diagnostics := #[{ severity := "error", message := s!"I couldn't initialize Blaster: {ex}" }] }
      return ← finishCheckReport cfg renderer report

end Blaster.Cli
