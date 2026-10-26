import Blaster.Cli.Types

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

private def canColor (cfg : Config) (stream : IO.FS.Stream) : IO Bool := do
  if cfg.json || cfg.color == "never" then return false
  if cfg.color == "always" then return true
  if (← IO.getEnv "TERM") == some "dumb" then return false
  if let some value ← IO.getEnv "NO_COLOR" then
    unless value.isEmpty do return false
  return ← stream.isTty

def Renderer.create (cfg : Config) : IO Renderer := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  return {
    config := cfg
    out := out
    err := err
    colorOut := ← canColor cfg out
    colorErr := ← canColor cfg err
    live := !cfg.json && !cfg.noProgress && (← err.isTty) && (← IO.getEnv "TERM") != some "dumb"
    stage := ← IO.mkRef "I'm elaborating the Lean file"
    started := ← IO.monoMsNow
    stop := ← IO.mkRef false }

/-- ANSI roles inherit the user's terminal palette and remain readable on light backgrounds. -/
def styled (enabled : Bool) (role text : String) : String :=
  if enabled then s!"\x1b[{role}m{text}\x1b[0m" else text

private def symbol (cfg : Config) (status : String) : String :=
  match status with
  | "valid" => if cfg.ascii then "+" else "✓"
  | "falsified" | "error" => if cfg.ascii then "x" else "×"
  | _ => "?"

private def statusStyle (status : String) : String :=
  match status with
  | "valid" => "32"
  | "falsified" | "error" => "31"
  | _ => "33"

private def elapsed (milliseconds : Nat) : String :=
  if milliseconds < 1000 then s!"{milliseconds}ms"
  else s!"{milliseconds / 1000}.{(milliseconds % 1000) / 100}s"

def Renderer.clear (r : Renderer) : IO Unit := do
  if r.live then r.err.putStr "\r\x1b[2K"

def Renderer.setStage (r : Renderer) (stage : String) : IO Unit := do
  r.stage.set stage
  if r.config.verbose && !r.live && !r.config.json then
    r.err.putStrLn s!"  {stage} · {(← IO.monoMsNow) - r.started}ms elapsed"

partial def Renderer.animate (r : Renderer) : IO Unit := do
  unless ← r.stop.get do
    let stage ← r.stage.get
    -- Stay within narrow terminals; full paths and declarations appear in permanent output.
    let width := ((← IO.getEnv "COLUMNS").bind String.toNat?).getD 80
    let elapsed := s!" · {((← IO.monoMsNow) - r.started) / 1000}s"
    let line := s!"  {if r.config.ascii then "." else "◌"} {stage}{elapsed}"
    r.err.putStr s!"\r\x1b[2K{String.mk (line.toList.take (width - 1))}"
    r.err.flush
    IO.sleep 100
    r.animate

def Renderer.result (r : Renderer) (result : CheckResult) : IO Unit := do
  unless r.config.json do
    r.clear
    let label := match result.status with
      | "valid" => "Valid"
      | "falsified" => "Falsified"
      | "undetermined" => "Undetermined"
      | _ => "Could not check"
    let label := if result.invocation == "tactic" then label ++ " goal" else label
    let subject := if result.invocation == "tactic" then "goal" else "property"
    let status := styled r.colorOut (statusStyle result.status) s!"{symbol r.config result.status} {label}"
    r.out.putStrLn s!"  {status}  {result.property}  · {elapsed result.elapsedMs}"
    r.out.putStrLn s!"    {result.location.file}:{result.location.line}:{result.location.column} · {result.invocation} · {result.origin}"
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
    | "undetermined" | "error" =>
      if let some reason := result.reason then r.out.putStrLn s!"    {reason}"
    | _ =>
      if r.config.verbose then r.out.putStrLn <|
        if result.origin == "smt" then "    Z3 reports this goal as valid"
        else "    I resolved this goal during optimization"
    r.out.flush

def Renderer.finish (r : Renderer) (report : Report) : IO Unit := do
  r.clear
  if r.config.json then
    r.out.putStrLn <| Lean.Json.compress <| Lean.Json.mkObj [
      ("schemaVersion", Lean.toJson report.schemaVersion),
      ("results", Lean.toJson report.results),
      ("diagnostics", Lean.toJson report.diagnostics),
      ("trust", Lean.toJson report.trust),
      ("exitCode", Lean.toJson report.exitCode.toNat)]
  else
    for diag in report.diagnostics do
      let color := if diag.severity == "error" then "31" else "33"
      let label := styled r.colorErr color diag.severity
      r.err.putStrLn s!"\n  {label}: {diag.message}"
      if let some location := diag.location then
        r.err.putStrLn s!"    {location.file}:{location.line}:{location.column}"
    let count (status : String) := report.results.filter (·.status == status) |>.size
    let errors := count "error" + (report.diagnostics.filter (·.severity == "error")).size
    r.out.putStrLn s!"\n  We're done: {count "valid"} valid, {count "falsified"} falsified, {count "undetermined"} undetermined, {errors} errors"
    if count "valid" > 0 then
      r.out.putStrLn s!"  {styled r.colorOut "33" "warning"}: {report.trust}"
  r.out.flush

end Blaster.Cli
