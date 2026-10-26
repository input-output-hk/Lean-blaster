import Blaster.Command
import Blaster.Cli.Render
import Lean.Elab.Frontend

open Lean Elab Meta

namespace Blaster.Cli

private def selectDeclaration (name file : String) : Command.CommandElabM Unit := do
  Command.runTermElabM fun _ => do
    let n := name.toName
    let some info := (← getEnv).find? n |
      throwError "I couldn't find declaration '{name}'. Use its fully qualified name."
    let e := mkConst n (info.levelParams.map Level.param)
    let property ← if ← isProp info.type then pure info.type else pure e
    unless ← isProp property do
      throwError "'{name}' isn't a proposition or a declaration with a propositional type"
    let location := (← findDeclarationRanges? n).map fun ranges =>
      { file, line := ranges.selectionRange.pos.line,
        column := ranges.selectionRange.pos.column + 1 : Location }
    discard <| runCaptured property {} name "declaration" (locationOverride := location)

private def collectDiagnostics (messages : MessageLog) : IO (Array Diagnostic) := do
  let mut result := #[]
  for msg in messages.toList do
    let verificationFailure := msg.data.hasTag (· == `Blaster.Cli.falsified)
    let severity := if verificationFailure then "verification" else match msg.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "info"
    result := result.push {
      severity := severity, message := ← msg.data.toString
      location := some { file := msg.fileName, line := msg.pos.line, column := msg.pos.column + 1 } }
  return result

def checkFile (cfg : Config) (renderer : Renderer) : IO Report := do
  let file := cfg.file.getD ""
  captureSession.set {
    config := cfg
    onStage := renderer.setStage, onResult := renderer.result }
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let opts := ({} : Lean.Options)
    |>.setBool `blaster.cli.capture true
    |>.setBool `Elab.async false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
    (mainModule := `BlasterCliInput)
  if messages.hasErrors then
    return { diagnostics := ← collectDiagnostics messages }
  let state ← Lean.Elab.IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  let mut diagnostics ← collectDiagnostics state.commandState.messages
  -- Tactics have already run during ordinary elaboration. Reuse their records;
  -- explicitly selected declarations without a captured call are checked once here.
  unless state.commandState.messages.hasErrors do
    let action : Frontend.FrontendM Unit := do
      for name in cfg.declarations do
        unless (← captureSession.get).report.results.any (·.property == name) do
          try
            Frontend.runCommandElabM <| selectDeclaration name file
          catch ex =>
            captureSession.modify fun s => { s with
              report.diagnostics := s.report.diagnostics.push
                { severity := "error", message := ex.toString } }
    let (_, finalState) ← (action.run { inputCtx }).run state
    diagnostics := diagnostics ++ (← collectDiagnostics finalState.commandState.messages).filter
      (fun d => !diagnostics.any (fun old => old.message == d.message && old.severity == d.severity))
  let report := (← captureSession.get).report
  let report := { report with diagnostics := report.diagnostics ++ diagnostics }
  if report.results.isEmpty && !report.diagnostics.any (·.severity == "error") then
    return { report with diagnostics := report.diagnostics.push {
      severity := "error",
      message := "I didn't find any checks. Add '#blaster [property]', use 'by blaster', or select a property with '--decl NAME'." } }
  return report

end Blaster.Cli
