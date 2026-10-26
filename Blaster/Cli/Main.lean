import Blaster.Cli.Args
import Blaster.Cli.Check
import Blaster.Smt.Solver
import Blaster.Cli.Runtime

open Lean

namespace Blaster.Cli

private def doctor (cfg : Config) (renderer : Renderer) : IO UInt32 := do
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
  let code : UInt32 := if diagnostics.isEmpty then 0 else 4
  if cfg.json then
    renderer.out.putStrLn <| Json.compress <| Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)), ("command", toJson "doctor"),
      ("leanVersion", toJson Lean.versionString), ("solver", toJson solver),
      ("diagnostics", toJson diagnostics), ("exitCode", toJson code.toNat)]
  else
    renderer.out.putStrLn s!"\n  {styled renderer.colorOut "35" "blaster"} · setup\n\n  Lean {Lean.versionString}"
    if let some selectedSolver := solver then
      renderer.out.putStrLn s!"  {selectedSolver.version}\n  Solver: {selectedSolver.path} ({selectedSolver.source})"
    for diagnostic in diagnostics do renderer.err.putStrLn s!"\n  error: {diagnostic.message}"
    if code == 0 then renderer.out.putStrLn "\n  I can find Blaster's compiled libraries and run Z3. We're ready to check properties."
  return code

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
    let cfg : Config := { json := args.contains "--json" }
    let renderer ← Renderer.create cfg
    if cfg.json then
      renderer.out.putStrLn <| Json.compress <| Json.mkObj [
        ("schemaVersion", toJson (1 : Nat)), ("results", toJson (#[] : Array CheckResult)),
        ("diagnostics", toJson #[{ severity := "error", message : Diagnostic }]),
        ("exitCode", toJson (2 : Nat))]
    else renderer.err.putStrLn s!"\n  error: {message}\n"
    return 2
  | .ok cfg =>
    let renderer ← Renderer.create cfg
    if cfg.version then
      renderer.out.putStrLn s!"lean-blaster (development) · Lean {Lean.versionString}"
      return 0
    if cfg.help || cfg.command == "help" then
      renderer.out.putStr (helpText cfg.command)
      return 0
    try
      initLibraries cfg
      if cfg.command == "doctor" then return ← doctor cfg renderer
      unless cfg.json do
        renderer.out.putStrLn s!"\n  {styled renderer.colorOut "35" "blaster"} · {cfg.file.getD ""}\n\n  I'm checking your properties.\n"
        renderer.out.flush
      let animation ← if renderer.live then
        some <$> IO.asTask renderer.animate else pure none
      let report ← try
        -- Source commands (#eval, verbose library output, etc.) cannot pollute JSON stdout.
        IO.withStdout renderer.err <| checkFile cfg renderer
      catch ex =>
        let capturedReport := (← captureSession.get).report
        let failure : Diagnostic := { severity := "error", message := s!"I couldn't complete the check: {ex}" }
        pure { capturedReport with diagnostics := capturedReport.diagnostics.push failure }
      finally
        renderer.stop.set true
        if let some task := animation then discard <| IO.ofExcept task.get
        renderer.clear
      renderer.finish report
      return report.exitCode
    catch ex =>
      let report : Report := {
        diagnostics := #[{ severity := "error", message := s!"I couldn't initialize Blaster: {ex}" }] }
      renderer.finish report
      return 4

end Blaster.Cli
