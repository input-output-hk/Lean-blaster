import Blaster.Cli.Types
import Blaster.Cli.Platform
import Std.Sync.Mutex

namespace Blaster.Cli

structure Renderer where
  config : Config
  out : IO.FS.Stream
  err : IO.FS.Stream
  colorOut : Bool
  colorErr : Bool
  live : Bool
  stage : IO.Ref String
  started : Nat
  stop : IO.Ref Bool
  emittedResults : IO.Ref Nat
  groupPrefix : IO.Ref (Option String)
  platform : Platform
  palette : String
  outputLock : Std.Mutex Unit

private def canColor (cfg : Config) (stream : IO.FS.Stream) : IO Bool := do
  if cfg.machineOutput || cfg.color == "never" then return false
  if cfg.color == "always" then return true
  if (← IO.getEnv "TERM") == some "dumb" then return false
  if let some value ← IO.getEnv "NO_COLOR" then
    unless value.isEmpty do return false
  return ← stream.isTty

private def paletteFor (cfg : Config) : IO String := do
  if cfg.theme != "auto" then return cfg.theme
  let colorTerm := (← IO.getEnv "COLORTERM").getD ""
  unless ["truecolor", "24bit"].contains colorTerm do return "ansi"
  let some background := ((← IO.getEnv "COLORFGBG").getD "").splitOn ";" |>.getLast? | return "ansi"
  let some value := background.toNat? | return "ansi"
  -- Other ANSI colors and indexed backgrounds do not identify brightness reliably.
  if value == 0 || value == 8 then return "dark"
  if value == 7 || value == 15 then return "light"
  return "ansi"

def Renderer.create (cfg : Config) (platform : Platform := {}) : IO Renderer := do
  let out ← match platform.output with | some output => pure output | none => IO.getStdout
  let err ← IO.getStderr
  return {
    config := cfg
    out := out
    err := err
    colorOut := ← canColor cfg out
    colorErr := ← canColor cfg err
    platform := platform
    palette := ← paletteFor cfg
    outputLock := ← Std.Mutex.new ()
    live := !cfg.machineOutput && !cfg.noProgress && (← err.isTty) && (← IO.getEnv "TERM") != some "dumb"
    stage := ← IO.mkRef "I'm elaborating the Lean file"
    started := ← IO.monoMsNow
    stop := ← IO.mkRef false
    emittedResults := ← IO.mkRef 0
    groupPrefix := ← IO.mkRef none }

/-- ANSI roles inherit the user's terminal palette and remain readable on light backgrounds. -/
def styled (enabled : Bool) (role text : String) : String :=
  if enabled then s!"\x1b[{role}m{text}\x1b[0m" else text

private def roleStyle (palette role : String) : String :=
  match palette, role with
  | "dark", "identity" => "38;2;196;181;253"
  | "light", "identity" => "38;2;109;40;217"
  | "dark", "action" => "38;2;103;232;249"
  | "light", "action" => "38;2;14;116;144"
  | "dark", "valid" => "38;2;134;239;172"
  | "light", "valid" => "38;2;22;101;52"
  | "dark", "error" => "38;2;253;164;175"
  | "light", "error" => "38;2;190;18;60"
  | "dark", "warning" => "38;2;252;211;77"
  | "light", "warning" => "38;2;146;64;14"
  | "dark", "muted" => "38;2;161;161;170"
  | "light", "muted" => "38;2;82;82;91"
  | _, "identity" => "35"
  | _, "action" => "36"
  | _, "valid" => "32"
  | _, "error" => "31"
  | _, "warning" => "33"
  | _, _ => "90"

def Renderer.tintOut (r : Renderer) (role text : String) : String :=
  styled r.colorOut (roleStyle r.palette role) text

def Renderer.tintErr (r : Renderer) (role text : String) : String :=
  styled r.colorErr (roleStyle r.palette role) text

private def symbol (cfg : Config) (status : String) : String :=
  match status with
  | "valid" => if cfg.ascii then "+" else "✓"
  | "falsified" | "error" => if cfg.ascii then "x" else "×"
  | _ => "?"

private def statusRole (status : String) : String :=
  match status with
  | "valid" => "valid"
  | "falsified" | "error" => "error"
  | _ => "warning"

private def elapsed (milliseconds : Nat) : String :=
  if milliseconds < 1000 then s!"{milliseconds}ms"
  else s!"{milliseconds / 1000}.{(milliseconds % 1000) / 100}s"

private def clearLine (r : Renderer) : IO Unit := do
  if r.live then r.err.putStr "\r\x1b[2K"

def Renderer.clear (r : Renderer) : IO Unit :=
  r.outputLock.atomically <| clearLine r

def Renderer.setStage (r : Renderer) (stage : String) : IO Unit := do
  r.stage.set stage
  if r.config.verbose && !r.live && !r.config.machineOutput then
    r.outputLock.atomically <| r.err.putStrLn s!"  {stage} · {(← IO.monoMsNow) - r.started}ms elapsed"

def Renderer.buildOutput (r : Renderer) (text : String) : IO Unit :=
  r.outputLock.atomically do
    clearLine r
    r.err.putStr text
    r.err.flush

partial def Renderer.animate (r : Renderer) : IO Unit := do
  unless ← r.stop.get do
    let stage ← r.stage.get
    -- Query each frame so resizing works even when the shell does not export COLUMNS.
    let actual ← r.platform.columns
    let fallback := ((← IO.getEnv "COLUMNS").bind String.toNat?).getD 80
    let width := if actual > 0 then actual else max 1 fallback
    let elapsed := s!" · {((← IO.monoMsNow) - r.started) / 1000}s"
    let line := s!"  {if r.config.ascii then "." else "◌"} {stage}{elapsed}"
    let line ← r.platform.clip line (width - 1)
    r.outputLock.atomically do
      unless ← r.stop.get do
        r.err.putStr s!"\r\x1b[2K{r.tintErr "identity" line}"
        r.err.flush
    IO.sleep 100
    r.animate

/-- Write one complete JSON record and flush it for streaming consumers. -/
private def writeJsonLine (r : Renderer) (value : Lean.Json) : IO Unit := do
  r.out.putStrLn value.compress
  r.out.flush

def Renderer.emitJsonLine (r : Renderer) (value : Lean.Json) : IO Unit :=
  r.outputLock.atomically <| writeJsonLine r value

/-- Open a source section. The returned guide restores its parent after nested imports. -/
def Renderer.beginImported (r : Renderer) (label : String) : IO (Option String) := do
  let parent ← r.groupPrefix.get
  let guide := parent.getD "  "
  let branch := if r.config.ascii then "+-- " else "╭─ "
  r.outputLock.atomically do
    clearLine r
    if r.config.json && !(← r.stop.get) then
      writeJsonLine r <| Lean.Json.mkObj [
        ("schemaVersion", Lean.toJson (1 : Nat)), ("event", Lean.toJson "moduleStart"),
        ("module", Lean.toJson label)]
    else unless r.config.machineOutput || (← r.stop.get) do
      r.out.putStrLn s!"{guide}{r.tintOut "muted" branch}{r.tintOut "action" label}"
      r.out.flush
  r.groupPrefix.set (some <| guide ++ if r.config.ascii then "|  " else "│  ")
  return parent

/-- Close a source section with counts from checks captured since it opened. -/
def Renderer.endImported (r : Renderer) (label : String) (parent : Option String)
    (report : Report) (firstResult started : Nat) : IO Unit := do
  let guide := parent.getD "  "
  let results := report.results.toList.drop firstResult
  let count (status : String) := (results.filter (·.status == status)).length
  let expected (status : String) :=
    (results.filter (fun result => result.status == status && result.expectedStatus == some status)).length
  let total := results.length
  let mut parts := #[s!"{total} {if total == 1 then "call" else "calls"}"]
  if count "valid" > 0 then
    parts := parts.push <| r.tintOut "valid" s!"{count "valid"} valid"
  if expected "falsified" > 0 then
    parts := parts.push <| r.tintOut "muted" s!"{expected "falsified"} expected falsified"
  if count "falsified" > expected "falsified" then
    parts := parts.push <| r.tintOut "error" s!"{count "falsified" - expected "falsified"} falsified"
  if expected "undetermined" > 0 then
    parts := parts.push <| r.tintOut "muted" s!"{expected "undetermined"} expected undetermined"
  if count "undetermined" > expected "undetermined" then
    parts := parts.push <| r.tintOut "warning" s!"{count "undetermined" - expected "undetermined"} undetermined"
  if count "error" > 0 then
    parts := parts.push <| r.tintOut "error" s!"{count "error"} errors"
  if count "skipped" > 0 then
    parts := parts.push <| r.tintOut "warning" s!"{count "skipped"} not checked"
  let elapsedMs := (← IO.monoMsNow) - started
  let duration := elapsed elapsedMs
  let branch := if r.config.ascii then "+-- " else "╰─ "
  r.outputLock.atomically do
    clearLine r
    if r.config.json && !(← r.stop.get) then
      writeJsonLine r <| Lean.Json.mkObj [
        ("schemaVersion", Lean.toJson (1 : Nat)), ("event", Lean.toJson "moduleComplete"),
        ("module", Lean.toJson label), ("elapsedMs", Lean.toJson elapsedMs),
        ("counts", Lean.Json.mkObj [
          ("valid", Lean.toJson (count "valid")),
          ("falsified", Lean.toJson (count "falsified")),
          ("undetermined", Lean.toJson (count "undetermined")),
          ("error", Lean.toJson (count "error")),
          ("skipped", Lean.toJson (count "skipped"))])]
    else unless r.config.machineOutput || (← r.stop.get) do
      r.out.putStrLn s!"{guide}{r.tintOut "muted" branch}{" · ".intercalate parts.toList} {r.tintOut "muted" s!"· {duration}"}"
      r.out.flush
  r.groupPrefix.set parent

def Renderer.result (r : Renderer) (result : CheckResult) : IO Unit := do
  if r.config.json then
    r.outputLock.atomically do
      unless ← r.stop.get do
        writeJsonLine r <| Lean.Json.mkObj [
          ("schemaVersion", Lean.toJson (1 : Nat)), ("event", Lean.toJson "result"),
          ("result", Lean.toJson result)]
        r.emittedResults.modify (· + 1)
    return
  if r.config.jsonReport || (← r.stop.get) then return
  if let some guide ← r.groupPrefix.get then
    r.outputLock.atomically do
      clearLine r
      let label := match result.status with
        | "valid" => "Valid"
        | "falsified" => "Falsified"
        | "undetermined" => "Undetermined"
        | "skipped" => "Not checked"
        | _ => "Could not check"
      let property := if result.invocation == "command" && result.property.startsWith "#blaster" then
        "#blaster" else result.property
      let expectation := if result.expectedStatus == some result.status then " (expected)"
        else result.expectedStatus.map (fun status => s!" (expected {status})") |>.getD ""
      let status := r.tintOut (statusRole result.status) s!"{symbol r.config result.status} {label}{expectation}"
      r.out.putStrLn s!"{guide}{status} · {property} at {result.location.line}:{result.location.column} {r.tintOut "muted" s!"· {elapsed result.elapsedMs}"}"
      if result.invocation == "tactic" && result.status != "valid" then
        if let some goal := result.goal then r.out.putStrLn s!"{guide}  Goal: {goal}"
      if r.config.debug then
        let limit := result.solverTimeoutSeconds.map (fun n => s!"{n}s") |>.getD "unlimited"
        r.err.putStrLn s!"{guide}  debug: per-query solver limit {limit}; result captured directly from {result.invocation}"
      match result.status with
      | "falsified" =>
        let subject := if result.invocation == "tactic" then "goal" else "property"
        if result.counterexample.isEmpty then
          unless result.expectedStatus == some "falsified" do
            r.out.putStrLn s!"{guide}  I found this {subject} false; no counterexample values are available"
        else
          r.out.putStrLn s!"{guide}  I found a counterexample (raw solver values):"
          for value in result.counterexample do
            for line in value.trim.splitOn "\n" do
              r.out.putStrLn s!"{guide}    {line}"
      | "undetermined" | "error" | "skipped" =>
        if let some reason := result.reason then r.out.putStrLn s!"{guide}  {reason}"
      | _ => pure ()
      r.out.flush
    return
  r.outputLock.atomically do
    clearLine r
    let label := match result.status with
      | "valid" => "Valid"
      | "falsified" => "Falsified"
      | "undetermined" => "Undetermined"
      | "skipped" => "Not checked"
      | _ => "Could not check"
    let label := if result.invocation == "tactic" then label ++ " goal" else label
    let label := if result.expectedStatus == some result.status then label ++ " (expected)"
      else label ++ (result.expectedStatus.map (fun status => s!" (expected {status})") |>.getD "")
    let subject := if result.invocation == "tactic" then "goal" else "property"
    let plain := s!"{symbol r.config result.status} {label}"
    let padding := String.mk (List.replicate (20 - plain.length) ' ')
    let status := r.tintOut (statusRole result.status) plain
    r.out.putStrLn s!"  {status}{padding}{result.property}  {r.tintOut "muted" s!"· {elapsed result.elapsedMs}"}"
    let location := r.tintOut "action" s!"{result.location.file}:{result.location.line}:{result.location.column}"
    r.out.putStrLn s!"    {location} {r.tintOut "muted" s!"· {result.invocation} · {result.origin}"}"
    if result.invocation == "tactic" && result.status != "valid" then
      if let some goal := result.goal then r.out.putStrLn s!"    Goal: {goal}"
    if r.config.debug then
      let limit := result.solverTimeoutSeconds.map (fun n => s!"{n}s") |>.getD "unlimited"
      r.err.putStrLn s!"    debug: per-query solver limit {limit}; result captured directly from {result.invocation}"
    match result.status with
    | "falsified" =>
      if result.counterexample.isEmpty then
        r.out.putStrLn s!"    I found this {subject} false; no counterexample values are available"
      else
        r.out.putStrLn "    I found a counterexample (raw solver values):"
        for value in result.counterexample do
          for line in value.trim.splitOn "\n" do
            r.out.putStrLn s!"      {line}"
    | "undetermined" | "error" | "skipped" =>
      if let some reason := result.reason then r.out.putStrLn s!"    {reason}"
    | _ =>
      if r.config.verbose then r.out.putStrLn <|
        if result.origin == "smt" then "    Z3 reports this goal as valid"
        else "    I resolved this goal during optimization"
    r.out.flush

def Renderer.finish (r : Renderer) (report : Report) : IO Unit := do
  r.outputLock.atomically do
   clearLine r
   if r.config.jsonReport then
    r.out.putStrLn <| Lean.Json.compress <| Lean.Json.mkObj [
      ("schemaVersion", Lean.toJson report.schemaVersion),
      ("results", Lean.toJson report.results),
      ("diagnostics", Lean.toJson report.diagnostics),
      ("trust", Lean.toJson report.trust),
      ("interrupted", Lean.toJson report.interrupted),
      ("signal", Lean.toJson report.signal),
      ("exitCode", Lean.toJson report.exitCode.toNat)]
   else if r.config.json then
    -- An interrupted worker can append a result before its callback sees the signal.
    -- Emit those captured results before the terminal completion record.
    let emitted ← r.emittedResults.get
    for result in report.results.toList.drop emitted do
      writeJsonLine r <| Lean.Json.mkObj [
        ("schemaVersion", Lean.toJson report.schemaVersion), ("event", Lean.toJson "result"),
        ("result", Lean.toJson result)]
    for diagnostic in report.diagnostics do
      writeJsonLine r <| Lean.Json.mkObj [
        ("schemaVersion", Lean.toJson report.schemaVersion), ("event", Lean.toJson "diagnostic"),
        ("diagnostic", Lean.toJson diagnostic)]
    let count (status : String) := report.results.filter (·.status == status) |>.size
    writeJsonLine r <| Lean.Json.mkObj [
      ("schemaVersion", Lean.toJson report.schemaVersion), ("event", Lean.toJson "complete"),
      ("exitCode", Lean.toJson report.exitCode.toNat),
      ("counts", Lean.Json.mkObj [
        ("valid", Lean.toJson (count "valid")),
        ("falsified", Lean.toJson (count "falsified")),
        ("undetermined", Lean.toJson (count "undetermined")),
        ("error", Lean.toJson (count "error")),
        ("skipped", Lean.toJson (count "skipped"))]),
      ("diagnosticCount", Lean.toJson report.diagnostics.size),
      ("elapsedMs", Lean.toJson ((← IO.monoMsNow) - r.started)),
      ("interrupted", Lean.toJson report.interrupted),
      ("signal", Lean.toJson report.signal), ("trust", Lean.toJson report.trust)]
   else
    for diag in report.diagnostics do
      unless diag.code == some "lean.unusedVariables" && !r.config.verbose do
        let role := if diag.severity == "error" then "error" else "warning"
        let label := r.tintErr role diag.severity
        r.err.putStrLn s!"\n  {label}: {diag.message}"
        if let some location := diag.location then
          r.err.putStrLn s!"    {location.file}:{location.line}:{location.column}"
    let count (status : String) := report.results.filter (·.status == status) |>.size
    let expected (status : String) :=
      report.results.filter (fun result => result.status == status && result.expectedStatus == some status) |>.size
    let errors := count "error" + (report.diagnostics.filter (·.severity == "error")).size
    let errorWord := if errors == 1 then "error" else "errors"
    let completion := if report.interrupted then "I stopped" else "We're done"
    let skipped := if count "skipped" == 0 then "" else s!", {count "skipped"} not checked"
    let expectedFalse := if expected "falsified" == 0 then "" else s!" ({expected "falsified"} expected)"
    let expectedUnknown := if expected "undetermined" == 0 then "" else s!" ({expected "undetermined"} expected)"
    r.out.putStrLn s!"\n  {completion}: {report.results.size} calls · {count "valid"} valid, {count "falsified"} falsified{expectedFalse}, {count "undetermined"} undetermined{expectedUnknown}, {errors} {errorWord}{skipped}"
    if count "valid" > 0 then
      r.out.putStrLn s!"  {r.tintOut "warning" "warning"}: {report.trust}"
   r.out.flush

end Blaster.Cli
