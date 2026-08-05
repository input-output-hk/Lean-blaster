import Lean
import Blaster.Optimize.Env

open Lean

namespace Blaster.Optimize

/-! # Optimizer growth telemetry (issue #138)

Opt-in JSONL recording of optimizer cache sizes over stack steps, enabled by
the `stats-file` solve option. Design:
docs/superpowers/specs/2026-08-05-optimizer-stats-design.md

Events (one JSON object per line, flushed per line so killed runs stay analyzable):
 - `{"ev":"start", "schema":1, "unfoldDepth":…, "maxDepth":…, "interval":…}`
 - `{"ev":"sample", "steps":…, "ms":…, "mcDepth":…, "<cache>":<size>, …}`
 - `{"ev":"end", "steps":…, "ms":…, "samples":…}`
Fields within an event are emitted in alphabetical order (Json.mkObj sorts keys).
-/

/-- Sizes of all tracked optimizer caches. All reads are O(1).
    `Name`-keyed memoization caches are bounded by program size and reported
    as one aggregate (`memNamed`); `Expr`-keyed ones are reported individually. -/
def cacheSizes (env : TranslateEnv) : List (String × Nat) :=
  let o := env.optEnv
  let m := o.memCache
  [ ("globalRewrite",  o.globalRewriteCache.size),
    ("localRewrite",   o.localRewriteCache.size),
    ("synthInstance",  o.synthInstanceCache.size),
    ("whnf",           o.whnfCache.size),
    ("match",          o.matchCache.size),
    ("recFunInst",     o.recFunInstCache.size),
    ("recFun",         o.recFunCache.size),
    ("recFunMap",      o.recFunMap.size),
    ("hypMap",         o.hypothesisContext.hypothesisMap.size),
    ("eqMap",          o.hypothesisContext.equalityMap.size),
    ("matchInCtx",     o.matchInContext.size),
    ("localDecls",     o.ctx.ctx.decls.size),
    ("inferType",      m.inferTypeCache.size),
    ("isProp",         m.isPropCache.size),
    ("getFunBody",     m.getFunBodyCache.size),
    ("isResolvable",   m.isResolvableCache.size),
    ("isType",         m.isTypeCache.size),
    ("isNotFun",       m.isNotFunCache.size),
    ("isCstMatchProp", m.isCstMatchPropCache.size),
    ("getFunEnvInfo",  m.getFunEnvInfoCache.size),
    ("memNamed",       m.isRecFunCache.size + m.isInstanceCache.size
                       + m.isClassCache.size + m.isInductiveCache.size
                       + m.getMatcherCache.size + m.getConstInfoCache.size
                       + m.isMatcherCache.size + m.isPartialCache.size
                       + m.isMatchToIte.size) ]

private def writeEvent (h : IO.FS.Handle) (fields : List (String × Json)) : IO Unit := do
  h.putStr ((Json.mkObj fields).compress ++ "\n")
  h.flush

/-- Emit one `sample` event. A write failure disables telemetry silently
    (no error spam at sample cadence). -/
def sampleStats : TranslateEnvT Unit := do
  let env ← get
  let some h := env.stats.handle | return ()
  let now ← IO.monoMsNow
  let fields :=
    [ ("ev", Json.str "sample"),
      ("steps", toJson env.stats.steps),
      ("ms", toJson (now - env.stats.startMs)),
      ("mcDepth", toJson env.optEnv.options.mcDepth) ]
    ++ (cacheSizes env).map (fun (n, v) => (n, toJson v))
  try
    writeEvent h fields
    modify fun e => { e with stats.samples := e.stats.samples + 1 }
  catch _ =>
    modify fun e => { e with stats.handle := none }

/-- Count one optimizer stack step; emit a sample every `interval` steps.
    Disabled path (the default): one state-ref read plus an Option tag test; no allocation, no state write. -/
@[always_inline, inline]
def bumpStatsAndMaybeSample : TranslateEnvT Unit := do
  let s := (← get).stats
  if s.handle.isSome then
    let steps := s.steps + 1
    if steps ≥ s.nextSampleAt then
      modify fun e => { e with stats.steps := steps, stats.nextSampleAt := steps + s.interval }
      sampleStats
    else
      modify fun e => { e with stats.steps := steps }

/-- Open the stats file and write the `start` event when `stats-file` is set.
    Open failure logs a warning and leaves telemetry disabled — it never
    fails the solve. Opening truncates the file. Use one stats file per command:
    concurrent commands sharing a path will clobber each other. -/
def initStats : TranslateEnvT Unit := do
  if (← get).stats.handle.isSome then return ()
  let sOpts := (← get).optEnv.options.solverOptions
  let some path := sOpts.statsFile | return ()
  let interval := max 1 sOpts.statsInterval
  try
    let h ← IO.FS.Handle.mk path .write
    writeEvent h
      [ ("ev", Json.str "start"),
        ("schema", toJson (1 : Nat)),
        ("unfoldDepth", toJson sOpts.unfoldDepth),
        ("maxDepth", toJson sOpts.maxDepth),
        ("interval", toJson interval) ]
    let now ← IO.monoMsNow
    modify fun e =>
      { e with stats := { handle := some h, interval, steps := 0,
                          nextSampleAt := interval, startMs := now, samples := 0 } }
  catch ex =>
    logWarning m!"stats-file: could not initialize '{path}' ({ex.toMessageData}); telemetry disabled"

/-- Emit the `end` event and drop the handle. At `verbose ≥ 1`, log a human
    summary (total steps, elapsed, top-8 caches by final size). -/
def finalizeStats : TranslateEnvT Unit := do
  let env ← get
  let some h := env.stats.handle | return ()
  let now ← IO.monoMsNow
  try
    writeEvent h
      [ ("ev", Json.str "end"),
        ("steps", toJson env.stats.steps),
        ("ms", toJson (now - env.stats.startMs)),
        ("samples", toJson env.stats.samples) ]
  catch _ => pure ()
  -- Dropping the last reference closes the file (Lean handles close on RC release; there is no Handle.close).
  modify fun e => { e with stats.handle := none }
  if env.optEnv.options.solverOptions.verbose ≥ 1 then
    let top := ((cacheSizes env).toArray.qsort (fun a b => a.2 > b.2)).extract 0 8
    let lines := top.toList.map (fun (n, v) => s!"  {n}: {v}")
    logInfo m!"optimizer stats: {env.stats.steps} steps, {now - env.stats.startMs} ms\n{String.intercalate "\n" lines}"

/-- Run `act` with telemetry initialized before and finalized after (when the
    `stats-file` option is set; otherwise both hooks are no-ops). -/
def withOptimizeStats (act : TranslateEnvT α) : TranslateEnvT α := do
  initStats
  try act finally finalizeStats

end Blaster.Optimize
