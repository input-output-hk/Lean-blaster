import Blaster.Command
import Blaster.Cli.Render
import Blaster.Cli.Runtime
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
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let moduleHeader := HeaderSyntax.toModuleHeader header
  -- An import-only umbrella has no direct checks to report. Avoid compiling its
  -- entire import graph merely to discover that fact after the build.
  if !messages.hasErrors && !moduleHeader.imports.isEmpty && cfg.declarations.isEmpty &&
      (input.extract parserState.pos input.endPos).trim.isEmpty then
    return { diagnostics := #[{ severity := "error", message :=
      "I found only imports in this file, so I have no direct checks to report.\n\n  Check a leaf file with '#blaster' or 'by blaster'.\n  To run the imported test suite, use 'lake test'." }] }
  let setup : Option ModuleSetup ← if messages.hasErrors then pure none else
    prepareImports cfg moduleHeader renderer.setStage renderer.buildOutput
  if let some setup := setup then setup.dynlibs.forM Lean.loadDynlib
  let opts := (setup.map (fun setup => setup.options.toOptions) |>.getD ({} : Lean.Options))
    |>.setBool `blaster.cli.capture true
    |>.setBool `Elab.async false
  let isModule := HeaderSyntax.isModule header || (setup.map (·.isModule) |>.getD false)
  let (env, messages) ← processHeaderCore (HeaderSyntax.startPos header) (HeaderSyntax.imports header) isModule
    opts messages inputCtx (mainModule := setup.map (·.name) |>.getD `BlasterCliInput)
    (arts := setup.map (·.importArts) |>.getD {})
    (plugins := setup.map (·.plugins) |>.getD #[])
  if messages.hasErrors then
    let mut diagnostics ← collectDiagnostics messages
    if cfg.noBuild then
      diagnostics := diagnostics.push { severity := "info", message :=
        "Automatic dependency builds are disabled. Run again without '--no-build' to prepare missing imports." }
    return { diagnostics }
  let state ← Lean.Elab.IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  let mut diagnostics ← collectDiagnostics state.commandState.messages
  -- Tactics have already run during ordinary elaboration. Reuse their records;
  -- explicitly selected declarations without a captured call are checked once here.
  unless state.commandState.messages.hasErrors do
    let action : Frontend.FrontendM Unit := do
      for name in cfg.declarations do
        unless (← readCapture).report.results.any (·.property == name) do
          try
            Frontend.runCommandElabM <| selectDeclaration name file
          catch ex =>
            modifyCapture fun s => { s with
              report.diagnostics := s.report.diagnostics.push
                { severity := "error", message := ex.toString } }
    let (_, finalState) ← (action.run { inputCtx }).run state
    diagnostics := diagnostics ++ (← collectDiagnostics finalState.commandState.messages).filter
      (fun d => !diagnostics.any (fun old => old.message == d.message && old.severity == d.severity))
  let report := (← readCapture).report
  let mut report := { report with diagnostics := report.diagnostics ++ diagnostics }
  -- A rejected tactic is still an elaboration error, even when classified as falsification.
  -- Never solve new declarations in that environment: Lean may have inserted recovery sorries.
  -- Instead, validate names and explicitly account for every remaining request.
  if state.commandState.messages.hasErrors then
    for name in cfg.declarations do
      unless report.results.any (·.property == name) do
        if (state.commandState.env.find? name.toName).isNone then
          report := { report with diagnostics := report.diagnostics.push {
            severity := "error", message := s!"I couldn't find declaration '{name}'. Use its fully qualified name." } }
        let record : CheckResult := {
          property := name, invocation := "declaration", status := "skipped", origin := "elaboration"
          location := { file, line := 1, column := 1 }, elapsedMs := 0, solverTimeoutSeconds := none
          reason := some "I couldn't check this selection because the file didn't elaborate successfully. Fix the earlier errors and run the check again." }
        report := { report with results := report.results.push record }
        renderer.result record
  if report.results.isEmpty && !report.diagnostics.any (·.severity == "error") then
    return { report with diagnostics := report.diagnostics.push {
      severity := "error",
      message := "I didn't find checks in this file. Imported modules are loaded from compiled libraries; their Blaster commands and tactic proofs aren't rerun here. Check a file containing '#blaster' or 'by blaster', select a property with '--decl NAME', or run 'lake test' for the project's test suite." } }
  return report

end Blaster.Cli
