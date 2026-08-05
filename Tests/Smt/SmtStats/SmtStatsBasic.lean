import Tests.Utils

/-! # Tests for the optimizer growth telemetry (stats-file / stats-interval)

Covers:
 - JSONL structure: start/sample/end events, parseable lines, monotone steps
 - default-off behavior (statsFile defaults to none)
 - open-failure resilience (bad path → warning, optimization still succeeds)
 - end-to-end option syntax smoke test through #blaster
-/

open Lean Elab Command Term Meta Blaster.Options Tests

namespace Test.SmtStatsBasic

private def statsPath : String := ".lake/smtstats_basic_test.jsonl"

private def getEv (j : Json) : String :=
  ((j.getObjVal? "ev").bind Json.getStr?).toOption.getD "<none>"

private def getNatField (j : Json) (k : String) : Nat :=
  ((j.getObjVal? k).bind Json.getNat?).toOption.getD 0

/-- Run optimization with telemetry enabled and validate the JSONL output. -/
elab "#testStatsJsonl" : command => do
  runTermElabM fun _ => do
    let sOpts : BlasterOptions :=
      { statsFile := some statsPath, statsInterval := 10, onlyOptimize := true }
    let stx ← `(∀ (x y : List UInt8), (if x < y then y.length else x.length) > 0)
    discard <| callOptimize sOpts stx
    let content ← IO.FS.readFile statsPath
    IO.FS.removeFile statsPath
    let lines := (content.splitOn "\n").filter (· ≠ "")
    -- every line parses as JSON
    let mut events : Array Json := #[]
    for l in lines do
      match Json.parse l with
      | .ok j => events := events.push j
      | .error err => logError s!"SmtStats ❌ unparseable JSONL line: {l} ({err})"
    -- exactly one start (first) and one end (last), ≥1 sample between
    if events.size < 3 then
      logError s!"SmtStats ❌ expected ≥3 events (start/sample.../end), got {events.size}"
    if getEv events[0]! ≠ "start" then
      logError s!"SmtStats ❌ first event is not start: {events[0]!.compress}"
    if getEv events[events.size - 1]! ≠ "end" then
      logError s!"SmtStats ❌ last event is not end: {events[events.size - 1]!.compress}"
    let samples := events.filter (fun j => getEv j == "sample")
    if samples.isEmpty then
      logError "SmtStats ❌ no sample events (interval 10 should have fired)"
    -- steps strictly monotone across samples; sample carries known cache fields
    let mut prev := 0
    for s in samples do
      let steps := getNatField s "steps"
      if steps ≤ prev then
        logError s!"SmtStats ❌ non-monotone steps: {steps} after {prev}"
      prev := steps
      if (s.getObjVal? "globalRewrite").toOption.isNone then
        logError s!"SmtStats ❌ sample missing globalRewrite field: {s.compress}"
      if (s.getObjVal? "localDecls").toOption.isNone then
        logError s!"SmtStats ❌ sample missing localDecls field: {s.compress}"
    -- end totals are consistent
    let endEv := events[events.size - 1]!
    if getNatField endEv "steps" < prev then
      logError "SmtStats ❌ end.steps below last sample steps"
    let endSamples := getNatField endEv "samples"
    if endSamples ≠ samples.size then
      logError s!"SmtStats ❌ end.samples={endSamples} but counted {samples.size}"
    logInfo "SmtStats JSONL ✅"

#testStatsJsonl

-- Default options leave telemetry off.
#guard (default : BlasterOptions).statsFile.isNone
#guard (default : BlasterOptions).statsInterval == 100000

/-- A bad path must warn but never fail the run. -/
elab "#testStatsBadPath" : command => do
  runTermElabM fun _ => do
    let sOpts : BlasterOptions :=
      { statsFile := some "/nonexistent-dir-smtstats-test/out.jsonl", onlyOptimize := true }
    let stx ← `(∀ (x y : List UInt8), (if x < y then y.length else x.length) > 0)
    -- must not throw; the warning is logged by initStats
    discard <| callOptimize sOpts stx
    logInfo "SmtStats bad-path ✅"

#testStatsBadPath

-- End-to-end surface smoke test: options parse and the command completes.
-- (No file-content assertions here: #blaster elaborates asynchronously.)
#blaster (stats-file: ".lake/smtstats_syntax_test.jsonl") (stats-interval: 1000) (only-optimize: 1) (solve-result: 2) [ ∀ (x y : List UInt8), (if x < y then y.length else x.length) > 0 ]

end Test.SmtStatsBasic
