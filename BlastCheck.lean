import Pigment
import Blaster.BlastResults

open Pigment.Basic
open Blaster.BlastResults

-- ── Formatting helpers ────────────────────────────────────────────────────────

private def dashes (n : Nat) : String := String.ofList (List.replicate n '-')

private def moduleToFilePath (moduleName : String) : String :=
  moduleName.replace "." "/" ++ ".lean"

private def formatMs (ms : Nat) : String :=
  -- Format as X.XXs with exactly 2 decimal places
  let centis := (ms + 5) / 10  -- round to nearest centisecond
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

-- ── Per-record renderers ──────────────────────────────────────────────────────

/-- Gray/dim line showing that a check is running -/
private def renderStart (r : StartRecord) : ReaderT Config IO Unit := do
  let label :=
    if r.name == r.desc then
      s!"  ⟳  {r.name}"
    else
      s!"  ⟳  {r.name}  {r.desc}"
  println (label.style |> dim)

/-- Green bold header + indented declaration -/
private def renderProved (start : StartRecord) (e : EndRecord) : ReaderT Config IO Unit := do
  let filePart := s!"{moduleToFilePath start.moduleName}:{start.line}"
  let timePart := formatMs e.time_ms
  let hdr := paddedHeader "PROVED" s!"{filePart}  {timePart}"
  println (hdr.style |> green |> bold)
  println ("".style)
  println (s!"    {start.decl}".style)
  println ("".style)

/-- Red bold header + counterexample lines -/
private def renderFalsified (start : StartRecord) (e : EndRecord) : ReaderT Config IO Unit := do
  let filePart := s!"{moduleToFilePath start.moduleName}:{start.line}"
  let timePart := formatMs e.time_ms
  let hdr := paddedHeader "FALSIFIED" s!"{filePart}  {timePart}"
  println (hdr.style |> red |> bold)
  println ("".style)
  println (s!"    {start.decl}".style)
  println ("".style)
  println ("I found a counterexample:".style)
  println ("".style)
  for cexLine in e.cex do
    println (s!"    {cexLine}".style)
  println ("".style)

/-- Yellow bold header + timeout message -/
private def renderUndetermined (start : StartRecord) (e : EndRecord) : ReaderT Config IO Unit := do
  let filePart := s!"{moduleToFilePath start.moduleName}:{start.line}"
  let timePart := formatMs e.time_ms
  let hdr := paddedHeader "UNDETERMINED" s!"{filePart}  {timePart}"
  println (hdr.style |> yellow |> bold)
  println ("".style)
  println (s!"    {start.decl}".style)
  println ("".style)
  println ("I ran out of time before reaching a verdict.".style)
  println ("".style)

/-- Red bold header when lake build itself failed -/
private def renderBuildFailed (moduleName : String) : ReaderT Config IO Unit := do
  let hdr := paddedHeader "BUILD FAILED" ""
  println (hdr.style |> red |> bold)
  println ("".style)
  println (s!"I could not compile {moduleName}. Run lake build {moduleName} to see why.".style)
  println ("".style)

/-- Summary footer -/
private def renderSummary
    (proved falsified undetermined totalMs : Nat) : ReaderT Config IO Unit := do
  println ((dashes headerWidth).style |> dim)
  let provedText    := s!"  {proved} proved".style |> green |> bold
  let falsifiedText := s!"  {falsified} falsified".style |> red |> bold
  let undeterText   := s!"  {undetermined} undetermined".style |> yellow |> bold
  let timeText      := s!"  ({formatMs totalMs} total)".style |> dim
  printLine [provedText, falsifiedText, undeterText, timeText]

-- ── Polling state ─────────────────────────────────────────────────────────────

private structure RunState where
  lineCount    : Nat := 0
  pendingStart : Option StartRecord := none
  proved       : Nat := 0
  falsified    : Nat := 0
  undetermined : Nat := 0
  totalMs      : Nat := 0

private def processLine
    (line : String) (state : RunState) : ReaderT Config IO RunState := do
  match parseRecord line with
  | .start r =>
    renderStart r
    return { state with pendingStart := some r }
  | .end_ e =>
    -- Render based on the pending start
    match state.pendingStart with
    | some s =>
      match e.status with
      | "proved"    => renderProved s e
      | "falsified" => renderFalsified s e
      | _           => renderUndetermined s e
    | none => pure ()
    -- Update counters
    let newState : RunState :=
      match e.status with
      | "proved"    => { state with proved       := state.proved       + 1,
                                    totalMs      := state.totalMs      + e.time_ms,
                                    pendingStart := none }
      | "falsified" => { state with falsified    := state.falsified    + 1,
                                    totalMs      := state.totalMs      + e.time_ms,
                                    pendingStart := none }
      | _           => { state with undetermined := state.undetermined + 1,
                                    totalMs      := state.totalMs      + e.time_ms,
                                    pendingStart := none }
    return newState
  | .unknown =>
    return state

private def drainFile
    (moduleName : String) (state : RunState) : ReaderT Config IO RunState := do
  let (newLines, newCount) ← readNewLines moduleName state.lineCount
  let mut st := { state with lineCount := newCount }
  for line in newLines do
    st ← processLine line st
  return st

-- ── Main ──────────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  let moduleName ←
    match args.head? with
    | none =>
      IO.eprintln "Usage: blast_check <ModuleName>"
      return 1
    | some m => pure m

  -- Collect current PATH so the child process can find tools
  let pathVal := (← IO.getEnv "PATH").getD ""

  -- Spawn `lake build <moduleName>` with BLAST_CHECK=1, suppressing output
  let proc ← IO.Process.spawn {
    cmd    := "lake"
    args   := #["build", moduleName]
    env    := #[("BLAST_CHECK", "1"), ("PATH", pathVal)]
    stdout := .null
    stderr := .null
  }

  -- Run proc.wait in a background task so we can poll without blocking
  let waitTask ← IO.asTask proc.wait

  -- Detect terminal colours once for the entire run
  let cfg ← defaultConfig

  -- Polling loop: drain results file every 200ms until build finishes
  let mut state : RunState := {}
  let mut buildDone := false
  while !buildDone do
    state ← (drainFile moduleName state).run cfg
    if ← IO.hasFinished waitTask then
      buildDone := true
    else
      IO.sleep 200

  -- Final drain after build has finished
  state ← (drainFile moduleName state).run cfg

  -- Retrieve the build exit code (waitTask is finished, so .get is safe)
  let buildResult := waitTask.get
  let buildExitCode : UInt32 :=
    match buildResult with
    | .ok code => code
    | .error _ => 1

  -- If build failed and no records were written, show build-failed banner and exit 1
  if buildExitCode != 0 && state.lineCount == 0 then
    (renderBuildFailed moduleName).run cfg
    return 1

  -- Print summary
  (renderSummary state.proved state.falsified state.undetermined state.totalMs).run cfg

  -- Exit 1 if any falsified, otherwise 0
  if state.falsified > 0 then return 1
  return 0
