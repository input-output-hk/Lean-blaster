import Pigment
import Blaster.BlastResults

open Pigment.Basic
open Blaster.BlastResults

-- ── Output mode ───────────────────────────────────────────────────────────────

private inductive OutputMode where
  | compact  -- one-liner for all results
  | normal   -- cards for failures only (default)
  | verbose  -- cards for all results

-- ── Merged result record ──────────────────────────────────────────────────────

private structure ResultRecord where
  name       : String   -- raw key (theorem name or "Line N")
  label      : String   -- display label (formula for #blaster, name for by blaster)
  decl       : String
  moduleName : String
  line       : Nat
  status     : String
  time_ms    : Nat
  cex        : List String

-- ── Formatting helpers ────────────────────────────────────────────────────────

private def dashes (n : Nat) : String := String.ofList (List.replicate n '-')

private def moduleToFilePath (moduleName : String) : String :=
  moduleName.replace "." "/" ++ ".lean"

private def formatMs (ms : Nat) : String :=
  let centis := (ms + 5) / 10
  let secs   := centis / 100
  let frac   := centis % 100
  let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
  s!"{secs}.{fracStr}s"

private def headerWidth : Nat := 60

private def paddedHeader (label : String) (right : String) : String :=
  let core := "-- " ++ label ++ " "
  let sep := if right.isEmpty then "" else " "
  let available := headerWidth - core.length - sep.length - right.length
  let fill := if available > 0 then dashes available else ""
  core ++ fill ++ sep ++ right

private def mkLabel (r : StartRecord) : String :=
  if r.name == r.desc then
    let d := r.decl
    if d.startsWith "#blaster [" && d.endsWith "]" then d.drop 10 |>.dropRight 1
    else r.name
  else s!"{r.name}  {r.desc}"

-- ── Compact one-liner ─────────────────────────────────────────────────────────

private def nameColWidth : Nat := 50

private def renderCompact (r : ResultRecord) : ReaderT Config IO Unit := do
  let pad := String.ofList (List.replicate (nameColWidth - min nameColWidth r.label.length) ' ')
  let time := formatMs r.time_ms
  match r.status with
  | "proved"    => println (s!"  ✓  {r.label}{pad}{time}".style |> green  |> bold)
  | "falsified" => println (s!"  ✗  {r.label}{pad}{time}".style |> red    |> bold)
  | _           => println (s!"  ?  {r.label}{pad}{time}".style |> yellow |> bold)

-- ── Card body (used inside labelled sections) ────────────────────────────────

private def renderCardBody (r : ResultRecord) : ReaderT Config IO Unit := do
  let filePart := s!"{moduleToFilePath r.moduleName}:{r.line}"
  let timePart := formatMs r.time_ms
  let formula :=
    if r.decl.startsWith "#blaster [" && r.decl.endsWith "]" then
      r.decl.drop 10 |>.dropRight 1
    else r.decl
  println ("".style)
  let fileInfo := s!"  {filePart}  {timePart}".style
  println (match r.status with | "falsified" => fileInfo |> red | _ => fileInfo |> yellow)
  println ("".style)
  println (s!"    {formula}".style)
  println ("".style)
  match r.status with
  | "falsified" =>
    if r.cex.isEmpty then
      println ("  I found the theorem to be trivially false during optimization.".style)
      println ("".style)
    else
      println ("  I found a counterexample:".style)
      println ("".style)
      for cexLine in r.cex do
        println (s!"      {cexLine}".style)
      println ("".style)
  | _ =>
    println ("  I ran out of time before reaching a verdict.".style)
    println ("".style)

/-- Red bold header when lake build itself failed -/
private def renderBuildFailed (moduleName : String) : ReaderT Config IO Unit := do
  println ((paddedHeader "BUILD FAILED" "").style |> red |> bold)
  println ("".style)
  println (s!"I could not compile {moduleName}. Run lake build {moduleName} to see why.".style)
  println ("".style)

-- ── Render all results after build ───────────────────────────────────────────

-- Sort results by source line so output matches file order.
private def byLine (results : Array ResultRecord) : Array ResultRecord :=
  results.qsort (fun a b => decide (a.line < b.line))

-- For named theorems show the name; for #blaster calls show file:line.
private def validLabel (r : ResultRecord) : String :=
  if r.name.startsWith "Line " then s!"{moduleToFilePath r.moduleName}:{r.line}"
  else r.name

private def renderValidSection (proved : Array ResultRecord) : ReaderT Config IO Unit := do
  println ((dashes headerWidth).style |> dim)
  println ("-- VALID".style |> green |> bold)
  println ("".style)
  let maxLabelLen := proved.foldl (fun n r => max n (validLabel r).length) 1
  for r in proved do
    let lbl := validLabel r
    let pad := String.ofList (List.replicate (maxLabelLen - lbl.length) ' ')
    let entry := s!"  {lbl}{pad}   {formatMs r.time_ms}"
    println (entry.style |> green)
  println ("".style)

private def renderAll (results : Array ResultRecord) (mode : OutputMode) :
    ReaderT Config IO Unit := do
  let proved       := byLine (results.filter (fun r => r.status == "proved"))
  let falsified    := byLine (results.filter (fun r => r.status == "falsified"))
  let undetermined := byLine (results.filter (fun r => r.status != "proved" && r.status != "falsified"))
  match mode with
  | .compact =>
    -- one-liner for everything, failures first
    for r in falsified    do renderCompact r
    for r in undetermined do renderCompact r
    for r in proved       do renderCompact r
  | .normal | .verbose =>
    if !proved.isEmpty then
      renderValidSection proved
    if !falsified.isEmpty then
      println ((dashes headerWidth).style |> dim)
      println ("-- FALSIFIED".style |> red |> bold)
      for r in falsified do renderCardBody r
    if !undetermined.isEmpty then
      println ((dashes headerWidth).style |> dim)
      println ("-- UNDETERMINED".style |> yellow |> bold)
      for r in undetermined do renderCardBody r

-- ── Summary footer ────────────────────────────────────────────────────────────

private def renderSummary (results : Array ResultRecord) (totalMs : Nat) :
    ReaderT Config IO Unit := do
  println ((dashes headerWidth).style |> dim)
  let falsified    := results.filter (fun r => r.status == "falsified")
  let undetermined := results.filter (fun r => r.status != "proved" && r.status != "falsified")
  let proved       := results.filter (fun r => r.status == "proved")
  let provedText    := s!"  {proved.size} proved".style            |> green  |> bold
  let falsifiedText := s!"  {falsified.size} falsified".style      |> red    |> bold
  let undeterText   := s!"  {undetermined.size} undetermined".style |> yellow |> bold
  let timeText      := s!"  ({formatMs totalMs} total)".style      |> dim
  printLine [provedText, falsifiedText, undeterText, timeText]

-- ── Polling state ─────────────────────────────────────────────────────────────

private abbrev StartMap := Std.HashMap String StartRecord

private structure RunState where
  lineCount     : Nat := 0
  pendingStarts : StartMap := {}
  results       : Array ResultRecord := #[]
  totalMs       : Nat := 0

-- Pure accumulation — no rendering here; all output happens after the build.
private def processLine (line : String) (state : RunState) : RunState :=
  match parseRecord line with
  | .start r =>
    -- Drop any previous result for this name: the tactic is re-running (snapshot re-elab),
    -- so we want only the freshest result.
    let results := state.results.filter (fun x => x.name != r.name)
    { state with pendingStarts := state.pendingStarts.insert r.name r, results }
  | .end_ e =>
    let newStarts := state.pendingStarts.erase e.name
    match state.pendingStarts.get? e.name with
    | none   => { state with pendingStarts := newStarts }
    | some s =>
      let r : ResultRecord := {
        name       := s.name
        label      := mkLabel s
        decl       := s.decl
        moduleName := s.moduleName
        line       := s.line
        status     := e.status
        time_ms    := e.time_ms
        cex        := e.cex
      }
      { state with
        pendingStarts := newStarts
        results       := state.results.push r
        totalMs       := state.totalMs + e.time_ms }
  | .unknown => state

private def drainFile (moduleName : String) (state : RunState) : IO RunState := do
  let (newLines, newCount) ← readNewLines moduleName state.lineCount
  let mut st := { state with lineCount := newCount }
  for line in newLines do
    st := processLine line st
  return st

-- ── Main ──────────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  -- Parse leading flags
  let mut mode     : OutputMode  := .normal
  let mut restArgs : List String := args
  let mut cont     := true
  while cont do
    match restArgs with
    | "--compact" :: rest => mode := .compact; restArgs := rest
    | "--verbose" :: rest => mode := .verbose; restArgs := rest
    | _                   => cont := false

  let moduleName ←
    match restArgs.head? with
    | none =>
      IO.eprintln "Usage: blast_check [--compact|--verbose] <ModuleName|path/to/File.lean>"
      return 1
    | some m =>
      -- Accept both dot-separated module names and file paths with tab-completion
      let m := if m.startsWith "./" then m.drop 2 else m
      pure (if m.endsWith ".lean" then m.dropRight 5 |>.replace "/" "." else m)

  -- If the results file is missing or empty, the olean is stale (e.g. file was deleted
  -- externally). Remove it so lake is forced to recompile and write fresh results.
  let existingLines ← readAllLines moduleName
  if existingLines.isEmpty then
    let oleanPath := ".lake/build/lib/lean/" ++ moduleName.replace "." "/" ++ ".olean"
    try IO.FS.removeFile oleanPath catch _ => pure ()

  -- Snapshot the current line count so we only read records from this run.
  -- If the module is rebuilt, writeStart truncates the file and we start from 0.
  -- If the module is cached (no recompile), new lines = 0 and we fall back to
  -- the existing file which holds the correct results from the last build.
  let preRunLines := existingLines.size

  -- Spawn `lake build <moduleName>` with BLAST_CHECK=1, suppressing output.
  -- Child inherits the full parent environment; BLAST_CHECK is added on top.
  let proc ← IO.Process.spawn {
    cmd    := "lake"
    args   := #["build", moduleName]
    env    := #[("BLAST_CHECK", "1")]
    stdout := .null
    stderr := .null
  }

  -- Run proc.wait in a background task so we can poll without blocking
  let waitTask ← IO.asTask proc.wait

  -- Detect terminal colours once for the entire run
  let cfg ← defaultConfig

  -- Live build progress: print a status line, update it with result count as proofs finish
  let stdout ← IO.getStdout
  let printStatus : String → IO Unit := fun s => do
    stdout.putStr s!"\r  ⟳  {s}"
    stdout.flush

  printStatus s!"building {moduleName}..."

  -- Polling loop: drain results file every 200ms until build finishes.
  -- Start reading from preRunLines so that a cache hit (no recompile, no new records)
  -- leaves state.results empty — handled below by the fallback.
  let mut state : RunState := { lineCount := preRunLines }
  let mut buildDone := false
  while !buildDone do
    state ← drainFile moduleName state
    let n := state.results.size
    printStatus s!"building {moduleName}...{if n > 0 then s!"  ({n} done)" else ""}"
    if ← IO.hasFinished waitTask then
      buildDone := true
    else
      IO.sleep 200

  -- Final drain after build has finished
  state ← drainFile moduleName state

  -- Clear the status line before rendering
  stdout.putStr s!"\r{String.ofList (List.replicate 80 ' ')}\r"
  stdout.flush

  -- Retrieve the build exit code (waitTask is finished, so .get is safe)
  let buildResult := waitTask.get
  let buildExitCode : UInt32 :=
    match buildResult with
    | .ok code => code
    | .error _ => 1

  -- Cache-hit fallback: if the build succeeded but wrote no new records, the module
  -- was served from cache. Read the full existing file so old results are still shown.
  if state.results.isEmpty && buildExitCode == 0 then
    let allLines ← readAllLines moduleName
    let mut s : RunState := {}
    for line in allLines do
      s := processLine line s
    state := s

  -- If build failed with no records, show build-failed banner and exit 1.
  -- If build failed but some records were written (partial run), fall through
  -- to the summary so partial results are still shown, but exit 1.
  if buildExitCode != 0 && state.lineCount == 0 then
    (renderBuildFailed moduleName).run cfg
    return 1

  -- Render all results, then the summary footer
  (renderAll state.results mode).run cfg
  (renderSummary state.results state.totalMs).run cfg

  -- Exit 1 if any falsified or if the build itself failed
  if state.results.any (fun r => r.status == "falsified") || buildExitCode != 0 then return 1
  return 0
