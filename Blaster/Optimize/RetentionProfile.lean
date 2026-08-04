import Lean
import Blaster.Optimize.Env.Types

/-!
# Retention profiling (opt-in, off by default)

Diagnostic instrumentation for the optimizer's memory blowup: every `N`
driver iterations, append one CSV line with the live entry count of every
collection reachable from `TranslateEnv`, the driver stack depth and the
process RSS.

Entirely gated on the environment variable `BLASTER_RETENTION_PROFILE`
(the output path). When it is unset the only cost is one `IO.Ref` read per
driver iteration (`Retention.due` short-circuits on the `0` sentinel) and
nothing is ever written. `BLASTER_RETENTION_EVERY` overrides `N`
(default 20000).

A sample walks every table (the nested ones are `O(capacity)`), which costs
~40 ms on a large environment, so samples are additionally rate limited to
one per `BLASTER_RETENTION_MIN_MS` milliseconds (default 2000) — that keeps
the overhead near 2% of wall clock whatever `N` is, while the iteration
counter still advances by `N` on every period.

Every line is flushed: the profiled process is expected to die by OOM, so
buffered data is lost data.
-/

open Lean Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize.Retention

/-- Iterations remaining until the next sample. `0` = profiling disabled. -/
initialize countdownRef : IO.Ref Nat ← IO.mkRef 0
/-- Sampling period `N` (iterations between samples). -/
initialize periodRef : IO.Ref Nat ← IO.mkRef 20000
/-- Total driver iterations observed (period × samples). -/
initialize itersRef : IO.Ref Nat ← IO.mkRef 0
/-- Output handle, when profiling is enabled. -/
initialize handleRef : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none
/-- `IO.monoMsNow` at profiling start. -/
initialize startMsRef : IO.Ref Nat ← IO.mkRef 0
/-- `IO.monoMsNow` of the last emitted sample. -/
initialize lastMsRef : IO.Ref Nat ← IO.mkRef 0
/-- Minimum milliseconds between two emitted samples. -/
initialize minMsRef : IO.Ref Nat ← IO.mkRef 2000

private def header : String :=
  "phase,elapsed_s,iters,rss_kb,stack_depth," ++
  "hashCons,rewrite_ctxs,rewrite_entries,synthInstance,matchCache,recFunInst,recFunSet,recFunMap," ++
  "hypMap_keys,hypMap_entries,eqMap_keys,eqMap_entries,matchInCtx_keys,matchInCtx_entries,matchInCtx_pats," ++
  "isRecFun,isInstance,isClass,getMatcher,getConstInfo,inferType,isMatcher,isPartial,funEnvInfo,funBody," ++
  "isProp,matchToIte,isNotFun,matchAlts,betaLambda,forallMeta,genericMatch,ctxReuse_keys,ctxReuse_entries,isCtorMatchProp," ++
  "curCtx,nextCtxId,activeCtxs,lctx_decls,localInsts,mAssignments,mvarCounter\n"

/-- Read `VmRSS` (kB) from `/proc/self/status`; `0` if unavailable. -/
def rssKb : IO Nat := do
  match ← (IO.FS.lines "/proc/self/status").toBaseIO with
  | .error _ => return 0
  | .ok ls =>
    for l in ls do
      if l.startsWith "VmRSS:" then
        -- "VmRSS:\t   2869096 kB"
        return ((l.drop 6).trim.takeWhile Char.isDigit).toNat?.getD 0
    return 0

/-- Enable profiling if `BLASTER_RETENTION_PROFILE` is set. Idempotent:
    a second call (the driver is re-entered once per `#solve`/`#prep_uplc`
    invocation in a module) keeps the first handle and clock. -/
def init : IO Unit := do
  if (← handleRef.get).isSome then return ()
  match ← IO.getEnv "BLASTER_RETENTION_PROFILE" with
  | none => return ()
  | some path =>
    let period := ((← IO.getEnv "BLASTER_RETENTION_EVERY").bind String.toNat?).getD 20000
    let period := if period == 0 then 20000 else period
    let minMs := ((← IO.getEnv "BLASTER_RETENTION_MIN_MS").bind String.toNat?).getD 2000
    let h ← IO.FS.Handle.mk path IO.FS.Mode.write
    h.putStr header
    h.flush
    handleRef.set (some h)
    periodRef.set period
    countdownRef.set period
    minMsRef.set minMs
    itersRef.set 0
    let now ← IO.monoMsNow
    startMsRef.set now
    lastMsRef.set now

/-- One driver iteration; `true` when this iteration should be sampled.
    Disabled fast path: a single `IO.Ref` read. Every `N`-th iteration the
    iteration counter advances and the rate limiter decides whether a sample
    is actually emitted. -/
@[inline] def due : IO Bool := do
  let c ← countdownRef.get
  if c == 0 then
    return false
  else if c == 1 then
    let period ← periodRef.get
    countdownRef.set period
    itersRef.modify (· + period)
    let now ← IO.monoMsNow
    if now - (← lastMsRef.get) ≥ (← minMsRef.get) then
      lastMsRef.set now
      return true
    else
      return false
  else
    countdownRef.set (c - 1)
    return false

private def sumRefMapSizes {α β γ} [Inhabited α] [BEq α] [Hashable α] [BEq γ] [Hashable γ]
    (m : HashMap α (IO.Ref (HashMap γ β))) : IO Nat := do
  let mut n := 0
  for r in m.vals do
    n := n + (← r.get).size
  return n

private def sumCtxMapEntries {α} (m : ContextMap α) : IO Nat := do
  let mut n := 0
  for r in m.vals do
    n := n + (← r.get).length
  return n

/-- Live pattern count inside `matchInContext` (a `ContextMap` whose values
    are refs to `HashSet PtrExpr`). -/
private def sumMatchInPatterns (m : MatchNotEqPatternMap) : IO Nat := do
  let mut n := 0
  for r in m.vals do
    for (_, s) in (← r.get) do
      n := n + (← s.get).size
  return n

/-- Append one CSV sample. `phase` is `tick` for periodic samples and
    `final` for the completion sample. -/
def sample (phase : String) (stackDepth : Nat) : TranslateEnvT Unit := do
  match ← handleRef.get with
  | none => return ()
  | some h =>
    let iters ← itersRef.get
    let elapsed := ((← IO.monoMsNow) - (← startMsRef.get)).toFloat / 1000.0
    let rss ← rssKb
    let env ← get
    let o := env.optEnv
    let m := o.memCache
    let mctx ← getMCtx
    let rewriteEntries ← sumRefMapSizes o.rewriteCache
    let hypEntries ← sumCtxMapEntries o.hypothesisContext.hypothesisMap
    let eqEntries ← sumCtxMapEntries o.hypothesisContext.equalityMap
    let matchInEntries ← sumCtxMapEntries o.matchInContext
    let matchInPats ← sumMatchInPatterns o.matchInContext
    let ctxReuseEntries ← sumRefMapSizes m.contextReuseCache
    let cols : List Nat :=
      [ rss, stackDepth,
        o.hashConsCache.size, o.rewriteCache.size, rewriteEntries,
        o.synthInstanceCache.size, o.matchCache.size, o.recFunInstCache.size,
        o.recFunCache.size, o.recFunMap.size,
        o.hypothesisContext.hypothesisMap.size, hypEntries,
        o.hypothesisContext.equalityMap.size, eqEntries,
        o.matchInContext.size, matchInEntries, matchInPats,
        m.isRecFunCache.size, m.isInstanceCache.size, m.isClassCache.size,
        m.getMatcherCache.size, m.getConstInfoCache.size, m.inferTypeCache.size,
        m.isMatcherCache.size, m.isPartialCache.size, m.getFunEnvInfoCache.size,
        m.getFunBodyCache.size, m.isPropCache.size, m.isMatchToIte.size,
        m.isNotFunCache.size, m.matchAltsCache.size, m.betaLambdaCache.size,
        m.forallMetaCache.size, m.genericMatchCache.size,
        m.contextReuseCache.size, ctxReuseEntries, m.isCtorMatchPropCache.size,
        o.options.curCtx, o.options.nextCtxId, o.options.active.size,
        o.ctx.ctx.decls.size, o.ctx.localInsts.size,
        o.mAssignments.size, mctx.mvarCounter ]
    let line := s!"{phase},{elapsed},{iters}," ++ String.intercalate "," (cols.map toString) ++ "\n"
    h.putStr line
    h.flush

end Blaster.Optimize.Retention
