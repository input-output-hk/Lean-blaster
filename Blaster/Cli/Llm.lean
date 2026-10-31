import Blaster.Cli.Runtime
import Std.Time

open Lean

namespace Blaster.Cli

private def quoted (value : String) : String := (toJson value).compress

private def displayPath (root : System.FilePath) (file : String) : IO String := do
  let path : System.FilePath := file
  let cwd ← IO.currentDir
  let path := if path.isAbsolute then path else cwd / path
  let path ← try Lean.realPathNormalized path catch _ => pure path.normalize
  return sourceLabel root path

private def indented (value : String) : String :=
  "\n".intercalate <| value.splitOn "\n" |>.map ("    " ++ ·)

private def sourceExcerpt (location : Location) : IO String := do
  let path : System.FilePath := location.file
  let input ← try IO.FS.readFile path catch _ => return "    Source is unavailable."
  let lines := (input.splitOn "\n").toArray
  let first := max 1 (location.line - 3)
  let last := min lines.size (location.line + 3)
  let mut excerpt := ""
  for line in [first:last + 1] do
    let marker := if line == location.line then ">" else " "
    excerpt := excerpt ++ s!"    {marker} {line} | {lines[line - 1]!}\n"
  return if excerpt.isEmpty then excerpt else excerpt.dropRight 1

private def sameLocation (a b : Location) : Bool :=
  a.file == b.file && a.line == b.line && a.column == b.column

private def linkedDiagnostic (report : Report) (diagnostic : Diagnostic) : Bool :=
  diagnostic.severity == "verification" &&
    diagnostic.location.any fun location =>
      report.results.any fun result =>
        result.status == "falsified" && sameLocation location result.location

private def resultDetail (root : System.FilePath) (report : Report)
    (index : Nat) (result : CheckResult) : IO String := do
  let location := result.location
  let file ← displayPath root location.file
  let expected := result.expectedStatus.map (fun status => s!" (expected {status})") |>.getD ""
  let siteKey := s!"{file}:{location.line}:{location.column}:{result.invocation}"
  let mut lines := s!"### R{index + 1}: {result.status}{expected} — {file}:{location.line}:{location.column}\n\n"
  lines := lines ++ s!"- Property: {quoted result.property}\n"
  lines := lines ++ s!"- Invocation: {quoted result.invocation}; origin: {quoted result.origin}; elapsed: {result.elapsedMs} ms\n"
  lines := lines ++ s!"- Site key: {quoted siteKey}\n"
  if let some timeout := result.solverTimeoutSeconds then
    lines := lines ++ s!"- Per-query solver timeout: {timeout} s\n"
  lines := lines ++ "\nSource excerpt:\n\n" ++ (← sourceExcerpt location) ++ "\n"
  if let some goal := result.goal then
    lines := lines ++ "\nElaborated goal:\n\n" ++ indented goal ++ "\n"
  if let some reason := result.reason then
    lines := lines ++ "\nReported reason:\n\n" ++ indented reason ++ "\n"
  if result.status == "falsified" then
    if result.counterexample.isEmpty then
      lines := lines ++ "\nCounterexample values: unavailable in this result.\n"
    else
      lines := lines ++ "\nRaw solver counterexample values (types and source mapping are not available here):\n\n"
      for value in result.counterexample do
        lines := lines ++ indented value.trim ++ "\n"
  let related := report.diagnostics.filter fun diagnostic =>
    diagnostic.location.any (sameLocation location) &&
      diagnostic.code != some "lean.unusedVariables"
  if !related.isEmpty then
    lines := lines ++ "\nLean diagnostics at this site:\n\n"
    for diagnostic in related do
      lines := lines ++ s!"- {diagnostic.severity}: {quoted diagnostic.message}\n"
  return lines ++ "\n"

private def gitOutput (root : System.FilePath) (args : Array String) : IO (Option String) := do
  try
    let output ← IO.Process.output { cmd := "git", args, cwd := some root }
    if output.exitCode == 0 then return some output.stdout.trim
  catch _ => pure ()
  return none

private def solverLabel (cfg : Config) : IO String := do
  try
    let solver ← Blaster.Smt.resolveSolver cfg.solver
    return s!"{solver.version} ({solver.source}: {solver.path})"
  catch _ => return "Unavailable"

private def timeoutLabel (cfg : Config) : String :=
  match cfg.timeout with
  | none => "Source or default setting"
  | some none => "Unlimited"
  | some (some seconds) => s!"{seconds} s per query"

/-- Produce one complete evidence snapshot; the JSON event protocol is unchanged. -/
def llmReportText (cfg : Config) (report : Report) : IO String := do
  let cwd ← IO.currentDir
  let root ← Lean.realPathNormalized ((← projectFor cfg.file).getD cwd)
  let timestamp := toString <| Std.Time.PlainDateTime.ofTimestampAssumingUTC (← Std.Time.Timestamp.now)
  let revision := (← gitOutput root #["rev-parse", "--verify", "HEAD"]).getD "Unavailable"
  let dirty := match ← gitOutput root #["status", "--porcelain"] with
    | none => "Unavailable"
    | some value => if value.isEmpty then "Clean" else "Dirty"
  let solver ← solverLabel cfg
  let count (status : String) := report.results.filter (·.status == status) |>.size
  let diagnosticCount (severity : String) :=
    report.diagnostics.filter (·.severity == severity) |>.size
  let lintCount := report.diagnostics.filter (·.code == some "lean.unusedVariables") |>.size
  let resultFiles := report.results.foldl (fun files result =>
    if files.contains result.location.file then files else files.push result.location.file) (#[] : Array String)
  let mut content := "# Blaster check report\n\n"
  content := content ++ "This is a snapshot of observed Blaster invocations. It is not a Lean proof certificate.\n\n"
  content := content ++ "## Run\n\n"
  content := content ++ s!"- Generated (UTC): {timestamp}Z\n"
  content := content ++ s!"- Project root: {quoted root.toString}\n"
  content := content ++ s!"- Requested target: {quoted (cfg.file.getD "")}\n"
  content := content ++ s!"- Git revision: {revision}\n- Working tree: {dirty}\n"
  content := content ++ s!"- Lean: {Lean.versionString}\n- Solver: {solver}\n"
  content := content ++ s!"- Solver timeout override: {timeoutLabel cfg}\n"
  content := content ++ s!"- Solver seed override: {cfg.seed.map toString |>.getD "none"}\n"
  content := content ++ s!"- Counterexample retrieval: {if cfg.counterexamples then "enabled" else "disabled"}\n"
  content := content ++ s!"- Dependency builds: {if cfg.noBuild then "disabled" else "enabled"}\n"
  if !cfg.declarations.isEmpty then
    content := content ++ s!"- Selected declarations: {", ".intercalate cfg.declarations.toList}\n"
  content := content ++ s!"- Exit code: {report.exitCode}\n"
  if report.interrupted then
    content := content ++ s!"- Interrupted by signal: {report.signal.map toString |>.getD "unknown"}\n"
  content := content ++ "\n## Coverage and trust\n\n"
  content := content ++ s!"- Selected source files: {report.selectedSources.size}\n"
  content := content ++ s!"- Source files with recorded calls: {resultFiles.size}\n"
  content := content ++ s!"- Recorded calls: {report.results.size}; {count "valid"} valid, {count "falsified"} falsified, {count "undetermined"} undetermined, {count "error"} errors, {count "skipped"} skipped.\n"
  content := content ++ s!"- Lean diagnostics: {diagnosticCount "error"} errors, {diagnosticCount "verification"} verification messages, {diagnosticCount "warning"} warnings.\n"
  content := content ++ "- Syntactic sites discovered: not measured by this check run. Use lean-blaster discover for that inventory.\n"
  content := content ++ "- Import-only umbrellas do not schedule their children again. Lake may still compile imported sources on a cold build; those dependency executions are not captured as CLI results.\n"
  content := content ++ s!"- Trust: {report.trust}\n"
  if lintCount > 0 then
    content := content ++ s!"- Routine unused-variable warnings omitted from detail: {lintCount}\n"
  content := content ++ "\n## Result index\n\n"
  if report.results.isEmpty then content := content ++ "No Blaster invocation was recorded.\n"
  for index in [:report.results.size] do
    let some result := report.results[index]? | continue
    let file ← displayPath root result.location.file
    let expected := result.expectedStatus.map (fun status => s!" (expected {status})") |>.getD ""
    content := content ++ s!"- R{index + 1}: {result.status}{expected} — {quoted result.property} — {file}:{result.location.line}:{result.location.column} ({result.invocation})\n"
  content := content ++ "\n## Non-valid results\n\n"
  content := content ++ "Expected falsified or undetermined outcomes are included for evidence; they are not necessarily regressions.\n\n"
  let mut detailed := false
  for index in [:report.results.size] do
    let some result := report.results[index]? | continue
    if result.status != "valid" then
      detailed := true
      content := content ++ (← resultDetail root report index result)
  if !detailed then content := content ++ "No non-valid Blaster results were recorded.\n\n"
  content := content ++ "## Other Lean diagnostics\n\n"
  let mut other := false
  for diagnostic in report.diagnostics do
    unless diagnostic.code == some "lean.unusedVariables" || linkedDiagnostic report diagnostic do
      other := true
      let location ← match diagnostic.location with
        | some location => do
          let file ← displayPath root location.file
          pure s!" at {file}:{location.line}:{location.column}"
        | none => pure ""
      content := content ++ s!"- {diagnostic.severity}{location}: {quoted diagnostic.message}\n"
  if !other then content := content ++ "None.\n"
  return content

/-- Replace a report only after the complete new version has been written. -/
def writeLlmReport (cfg : Config) (report : Report) : IO Unit := do
  let some output := cfg.llmReport | return
  let cwd ← IO.currentDir
  let target : System.FilePath := output
  let target := if target.isAbsolute then target else cwd / target
  if target.extension == some "lean" then
    throw <| IO.userError "The agent report is Markdown; choose a path other than a .lean source file."
  if ← target.pathExists then
    let existing ← Lean.realPathNormalized target
    if report.selectedSources.contains existing.toString then
      throw <| IO.userError "The agent report path points to a checked source file. Choose another path."
  let content ← llmReportText cfg report
  let parent := target.parent.getD cwd
  IO.FS.createDirAll parent
  let temporary := parent / s!".{target.fileName.getD "blaster-report"}.{← IO.Process.getPID}.{← IO.monoMsNow}.tmp"
  try
    IO.FS.writeFile temporary content
    IO.FS.rename temporary target
  catch ex =>
    try IO.FS.removeFile temporary catch _ => pure ()
    throw ex

end Blaster.Cli
