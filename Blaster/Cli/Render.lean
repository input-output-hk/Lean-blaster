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
  platform : Platform
  palette : String
  outputLock : Std.Mutex Unit

private def canColor (cfg : Config) (stream : IO.FS.Stream) : IO Bool := do
  if cfg.json || cfg.color == "never" then return false
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
    live := !cfg.json && !cfg.noProgress && (← err.isTty) && (← IO.getEnv "TERM") != some "dumb"
    stage := ← IO.mkRef "I'm elaborating the Lean file"
    started := ← IO.monoMsNow
    stop := ← IO.mkRef false }

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
  if r.config.verbose && !r.live && !r.config.json then
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

def Renderer.result (r : Renderer) (result : CheckResult) : IO Unit := do
  unless r.config.json || (← r.stop.get) do r.outputLock.atomically do
    clearLine r
    let label := match result.status with
      | "valid" => "Valid"
      | "falsified" => "Falsified"
      | "undetermined" => "Undetermined"
      | "skipped" => "Not checked"
      | _ => "Could not check"
    let label := if result.invocation == "tactic" then label ++ " goal" else label
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
   if r.config.json then
    r.out.putStrLn <| Lean.Json.compress <| Lean.Json.mkObj [
      ("schemaVersion", Lean.toJson report.schemaVersion),
      ("results", Lean.toJson report.results),
      ("diagnostics", Lean.toJson report.diagnostics),
      ("trust", Lean.toJson report.trust),
      ("interrupted", Lean.toJson report.interrupted),
      ("signal", Lean.toJson report.signal),
      ("exitCode", Lean.toJson report.exitCode.toNat)]
   else
    for diag in report.diagnostics do
      let role := if diag.severity == "error" then "error" else "warning"
      let label := r.tintErr role diag.severity
      r.err.putStrLn s!"\n  {label}: {diag.message}"
      if let some location := diag.location then
        r.err.putStrLn s!"    {location.file}:{location.line}:{location.column}"
    let count (status : String) := report.results.filter (·.status == status) |>.size
    let errors := count "error" + (report.diagnostics.filter (·.severity == "error")).size
    let completion := if report.interrupted then "I stopped" else "We're done"
    let skipped := if count "skipped" == 0 then "" else s!", {count "skipped"} not checked"
    r.out.putStrLn s!"\n  {completion}: {count "valid"} valid, {count "falsified"} falsified, {count "undetermined"} undetermined, {errors} errors{skipped}"
    if count "valid" > 0 then
      r.out.putStrLn s!"  {r.tintOut "warning" "warning"}: {report.trust}"
   r.out.flush

end Blaster.Cli
