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
      location := some { file := msg.fileName, line := msg.pos.line, column := msg.pos.column + 1 }
      code := if msg.data.isUnusedVariableWarning then some "lean.unusedVariables" else none }
  return result

private partial def checkSource (cfg : Config) (renderer : Renderer)
    (seen : IO.Ref (Array Name)) (partOfUmbrella : Bool)
    (followImports : Bool := true) : IO Report := do
  let firstResult := (← readCapture).report.results.size
  let file := cfg.file.getD ""
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let moduleHeader := HeaderSyntax.toModuleHeader header
  let explicitImports := HeaderSyntax.imports header false
  let emptyEnv ← mkEmptyEnvironment
  let (nextCommand, _, trailingMessages) :=
    Parser.parseCommand inputCtx { env := emptyEnv, options := {} } parserState messages
  if !followImports && !trailingMessages.hasErrors && !explicitImports.isEmpty &&
      Parser.isTerminalCommand nextCommand then
    return (← readCapture).report
  -- Check local sources named by an import-only umbrella directly. Building the
  -- umbrella first would execute their checks once during compilation and then
  -- require another elaboration to capture a structured CLI report.
  if followImports && !trailingMessages.hasErrors && !explicitImports.isEmpty && cfg.declarations.isEmpty &&
      Parser.isTerminalCommand nextCommand then
    let mut missingSources : Array String := #[]
    for imp in explicitImports do
      if let some source ← localSourceFor cfg imp.module then
        unless (← seen.get).contains imp.module do
          seen.modify (·.push imp.module)
          renderer.setStage s!"I'm checking imported module {imp.module}"
          let before := (← readCapture).report.results.size
          let started ← IO.monoMsNow
          let label := s!"{imp.module.toString.replace "." "/"}.lean"
          let parent ← renderer.beginImported label
          let report ← checkSource { cfg with file := some source.toString } renderer seen true followImports
          renderer.endImported label parent report before started
          if report.exitCode == 4 then return report
      else
        let name := imp.module.toString
        unless name == "Blaster" || name.startsWith "Blaster." ||
            name == "Init" || name.startsWith "Init." ||
            name == "Lean" || name.startsWith "Lean." ||
            name == "Lake" || name.startsWith "Lake." do
          missingSources := missingSources.push name
    let mut report := (← readCapture).report
    if !missingSources.isEmpty then
      let names := ", ".intercalate missingSources.toList
      report := { report with diagnostics := report.diagnostics.push {
        severity := "warning", message :=
          s!"I couldn't find local source for {names}; I didn't check those imports." } }
    if !partOfUmbrella && report.results.size == firstResult &&
        !report.diagnostics.any (·.severity == "error") then
      report := { report with diagnostics := report.diagnostics.push {
        severity := "error", message :=
          "I found no checks in the local source imports of this file. Check a source module directly or run 'lake test' for the project's test suite." } }
    modifyCapture fun s => { s with report }
    return report
  let setup : Option ModuleSetup ← if messages.hasErrors then pure none else
    prepareImports cfg moduleHeader renderer.setStage renderer.buildOutput
  let setup ← setup.mapM reconcileBlasterPlugin
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
    let prior := (← readCapture).report
    let report := { prior with diagnostics := prior.diagnostics ++ diagnostics }
    modifyCapture fun s => { s with report }
    return report
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
  if report.results.size == firstResult && !partOfUmbrella &&
      !report.diagnostics.any (·.severity == "error") then
    report := { report with diagnostics := report.diagnostics.push {
      severity := "error",
      message := "I didn't find checks in this file. Check a file containing '#blaster' or 'by blaster', select a property with '--decl NAME', or run 'lake test' for the project's test suite." } }
  modifyCapture fun s => { s with report }
  return report

def checkFile (cfg : Config) (renderer : Renderer) : IO Report := do
  let seen ← IO.mkRef (#[] : Array Name)
  checkSource cfg renderer seen false

/-- Each source in the directory inventory is selected once. Import-only umbrellas
    never schedule their children; the inventory already includes those files. -/
def checkDirectory (cfg : Config) (renderer : Renderer) : IO Report := do
  let files ← sourceFiles (cfg.file.getD "")
  let root ← Lean.realPathNormalized (cfg.file.getD "")
  let seen ← IO.mkRef (#[] : Array Name)
  for source in files do
    let label := sourceLabel root source
    let firstResult := (← readCapture).report.results.size
    let started ← IO.monoMsNow
    let parent ← renderer.beginImported label
    let report ← try
      checkSource { cfg with file := some source.toString } renderer seen true false
    catch ex =>
      let report := (← readCapture).report
      let report := { report with diagnostics := report.diagnostics.push {
        severity := "error", message := s!"I couldn't check '{label}': {ex}" } }
      modifyCapture fun s => { s with report }
      pure report
    renderer.endImported label parent report firstResult started
  let mut report := (← readCapture).report
  if report.results.isEmpty && !report.diagnostics.any (·.severity == "error") then
    report := { report with diagnostics := report.diagnostics.push {
      severity := "error", message := "I found no Blaster checks in this directory." } }
    modifyCapture fun s => { s with report }
  return report

end Blaster.Cli
