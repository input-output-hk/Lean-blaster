import Blaster.Command
import Blaster.Cli.Runtime
import Lean.Elab.Frontend
import Lean.Elab.Import

open Lean Elab

namespace Blaster.Cli

private def sourceRange (input : Parser.InputContext) (file : String)
    (stx : Syntax) : Option SourceRange := do
  let range ← stx.getRange?
  let start := input.fileMap.toPosition range.start
  let stop := input.fileMap.toPosition range.stop
  return {
    start := { file, line := start.line, column := start.column + 1 }
    stop := { file, line := stop.line, column := stop.column + 1 } }

private def sourceText (input : Parser.InputContext) (stx : Syntax) : Option String := do
  let range ← stx.getRange?
  return input.inputString.extract range.start range.stop

private def qualifiedName (scope : Array (Option String)) (name : String) : String :=
  if name.startsWith "_root_." then name.drop 7
  else
    let parts := scope.toList.filterMap id
    if parts.isEmpty then name else ".".intercalate (parts ++ [name])

private def declarationName? (stx : Syntax) (scope : Array (Option String)) : Option String := do
  if !stx.isOfKind ``Lean.Parser.Command.declaration then none
  else
    let decl := stx[1]
    if ![``Lean.Parser.Command.theorem, ``Lean.Parser.Command.definition,
        ``Lean.Parser.Command.abbrev, ``Lean.Parser.Command.opaque].contains decl.getKind then none
    else
      let ident := decl[1][0]
      if ident.isIdent then some (qualifiedName scope ident.getId.toString) else none

private def site (input : Parser.InputContext) (file kind : String)
    (stx bodyStx : Syntax) (name : Option String) : Option DiscoveryItem := do
  return {
    kind
    name
    body := ← sourceText input bodyStx
    invocationRange := ← sourceRange input file stx
    bodyRange := ← sourceRange input file bodyStx }

/-- Traverse parsed syntax, preserving the declaration containing each tactic. -/
private partial def collectSites (input : Parser.InputContext) (file : String)
    (scope : Array (Option String)) (stx : Syntax)
    (owner : Option (Option String × Syntax) := none) : Array DiscoveryItem := Id.run do
  let owner := if stx.isOfKind ``Lean.Parser.Command.declaration then
    some (declarationName? stx scope, stx)
    else owner
  let mut items := #[]
  if stx.isOfKind ``Blaster.Syntax.solve then
    if let some item := site input file "command" stx stx none then
      items := items.push item
  else if stx.isOfKind ``Blaster.Tactic.blasterTactic then
    let (name, bodyStx) := owner.getD (none, stx)
    if let some item := site input file "tactic" stx bodyStx name then
      items := items.push item
  if let .node _ kind args := stx then
    let args := if kind == choiceKind then args.extract 0 1 else args
    for arg in args do
      items := items ++ collectSites input file scope arg owner
  return items

private def parseDiagnostics (messages : MessageLog) : IO (Array Diagnostic) := do
  let mut diagnostics := #[]
  for msg in messages.toList do
    if msg.severity == .error then
      let detail ← msg.data.toString
      let location : Location := {
        file := msg.fileName, line := msg.pos.line, column := msg.pos.column + 1 }
      diagnostics := diagnostics.push {
        severity := "error"
        code := some "discovery.parse"
        message := s!"I couldn't fully parse this source without elaboration: {detail}"
        location := some location }
  return diagnostics

/-- Parser extensions live in imported oleans. Reuse environments for identical
    import headers while scanning a directory; no source is elaborated here. -/
private def parserEnvFor (baseEnv : Environment)
    (cache : IO.Ref (Array (Array Import × Environment)))
    (imports : Array Import) : IO (Environment × Option String) := do
  if imports.isEmpty then return (baseEnv, none)
  if let some (_, cached) := (← cache.get).find? (fun entry => entry.1 == imports) then
    return (cached, none)
  try
    let env ← importModules (#[{ module := `Blaster.Command }] ++ imports) {}
      (loadExts := true)
    cache.modify (·.push (imports, env))
    return (env, none)
  catch ex =>
    return (baseEnv, some ex.toString)

private partial def discoverSource (cfg : Config) (baseEnv : Environment)
    (cache : IO.Ref (Array (Array Import × Environment))) (seen : IO.Ref (Array Name))
    (onModuleStart : String → IO Unit) (onItem : DiscoveryItem → IO Unit)
    (onModuleComplete : String → Nat → IO Unit) (followImports : Bool := true) :
    IO (Array DiscoveryItem × Array Diagnostic) := do
  let file := cfg.file.getD ""
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := HeaderSyntax.imports header false
  let (first, firstState, firstMessages) :=
    Parser.parseCommand inputCtx { env := baseEnv, options := {} } parserState messages
  if followImports && !firstMessages.hasErrors && !imports.isEmpty && Parser.isTerminalCommand first then
    let mut items := #[]
    let mut diagnostics := #[]
    for imp in imports do
      if let some source ← localSourceFor cfg imp.module then
        unless (← seen.get).contains imp.module do
          seen.modify (·.push imp.module)
          let label := s!"{imp.module.toString.replace "." "/"}.lean"
          onModuleStart label
          let (found, issues) ← discoverSource { cfg with file := some source.toString }
            baseEnv cache seen onModuleStart onItem onModuleComplete followImports
          items := items ++ found
          diagnostics := diagnostics ++ issues
          onModuleComplete label found.size
    return (items, diagnostics)
  let (env, importIssue) ← parserEnvFor baseEnv cache imports
  let (first, firstState, firstMessages) :=
    Parser.parseCommand inputCtx { env, options := {} } parserState messages
  let mut state := firstState
  let mut messages := firstMessages
  let mut command := first
  let mut scope : Array (Option String) := #[]
  let mut items := #[]
  repeat
    if command.isOfKind ``Lean.Parser.Command.eoi then break
    if command.isOfKind ``Lean.Parser.Command.namespace then
      scope := scope.push (some command[1].getId.toString)
    else if command.isOfKind ``Lean.Parser.Command.section then
      scope := scope.push none
    else if command.isOfKind ``Lean.Parser.Command.end then
      if !scope.isEmpty then scope := scope.pop
    else
      let found := collectSites inputCtx file scope command
      for item in found do onItem item
      items := items ++ found
    let (next, nextState, nextMessages) :=
      Parser.parseCommand inputCtx { env, options := {} } state messages
    command := next
    state := nextState
    messages := nextMessages
  let mut diagnostics ← parseDiagnostics messages
  if let some issue := importIssue then
    diagnostics := diagnostics.push {
      severity := "warning", code := some "discovery.importSyntax",
      message := s!"I couldn't load syntax from this file's compiled imports; discovery may be incomplete. {issue}" }
  return (items, diagnostics)

/-- Discover direct Blaster syntax without elaboration, dependency builds, or solver work. -/
def discoverFile (cfg : Config) (onModuleStart : String → IO Unit)
    (onItem : DiscoveryItem → IO Unit) (onModuleComplete : String → Nat → IO Unit) :
    IO (Array DiscoveryItem × Array Diagnostic) := do
  initDiscoveryLibraries cfg
  let env ← importModules #[{ module := `Blaster.Command }] {} (loadExts := true)
  let cache ← IO.mkRef (#[] : Array (Array Import × Environment))
  let seen ← IO.mkRef (#[] : Array Name)
  discoverSource cfg env cache seen onModuleStart onItem onModuleComplete

/-- A directory is an inventory of source files, not an import graph. An umbrella
    contributes no sites; its leaves are visited directly, once each. -/
def discoverDirectory (cfg : Config) (onModuleStart : String → IO Unit)
    (onItem : DiscoveryItem → IO Unit) (onModuleComplete : String → Nat → IO Unit) :
    IO (Array DiscoveryItem × Array Diagnostic) := do
  initDiscoveryLibraries cfg
  let env ← importModules #[{ module := `Blaster.Command }] {} (loadExts := true)
  let cache ← IO.mkRef (#[] : Array (Array Import × Environment))
  let seen ← IO.mkRef (#[] : Array Name)
  let mut items := #[]
  let mut diagnostics := #[]
  let root ← Lean.realPathNormalized (cfg.file.getD "")
  for source in (← sourceFiles (cfg.file.getD "")) do
    let label := sourceLabel root source
    onModuleStart label
    try
      let (found, issues) ← discoverSource { cfg with file := some source.toString }
        env cache seen onModuleStart onItem onModuleComplete false
      items := items ++ found
      diagnostics := diagnostics ++ issues
      onModuleComplete label found.size
    catch ex =>
      diagnostics := diagnostics.push {
        severity := "error", message := s!"I couldn't inspect '{label}': {ex}" }
      onModuleComplete label 0
  return (items, diagnostics)

end Blaster.Cli
