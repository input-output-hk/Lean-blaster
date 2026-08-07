import Lean

/-!
# Phase-0 diagnostic counters (opt-in, off by default)

Global counters for the four go/no-go questions of the optimization
campaign (see the consumer repo's PREP-MEMORY-CLIFF.md):

* **p0a** — on a local rewrite-cache miss, would the key have hit in the
  global (ctx 0) cache or in another *active* context's cache? Measures
  the redundant re-derivation caused by context-local caching
  (`isInOptimizeEnvCache`). Probing every active context is O(active),
  so it is sampled 1-in-64 misses; `p0a_localMiss` counts all misses,
  `p0a_sampled` the probed subset.
* **p0b** — how often does `iteSimp?`'s then-simplification path free a
  live reusable else-branch context (forcing a from-scratch re-descent),
  versus propagating it (`toImpliesExpr`)?
* **p0c** — firings and fan-out of the case-of-case pull-outs
  (`constMatchPropagation?.isMatchArg` / `isDiteArg`), the unbounded
  term-duplication rule.
* **hypq** — how many hash-cons interns are *query junk*: nodes built by
  the hypothesis-map probe predicates (`inHypMap`, `*InHyps`, …) solely
  to be looked up, permanently retained by the hash-cons table.

All counters are inert unless `BLASTER_RETENTION_PROFILE` enabled
profiling (`enabledRef`); the disabled cost is one `IO.Ref` read at each
instrumented site. This module deliberately imports only `Lean` so that
`Env/Types.lean` (and everything above it) can import it without cycles.
-/

namespace Blaster.Optimize.Retention

/-- Master switch, set by `Retention.init` when `BLASTER_RETENTION_PROFILE` is present. -/
initialize enabledRef : IO.Ref Bool ← IO.mkRef false

/-- Ancestor-walk memoization (see `findAncestorCache`): OFF by default —
    measured A/B (2026-08-05): memo-on LOSES at both quick rungs
    (1600: 39.7 s vs 36.9 s; 1700: 92.1 s vs 87.2 s; oleans identical) —
    the insert traffic costs more than the walk it saves. Kept behind
    `BLASTER_MEMO_DEPTH=<n>0` for re-testing at deeper budgets only. -/
initialize walkMemoRef : IO.Ref Bool ← do
  let v := (← IO.getEnv "BLASTER_MEMO_DEPTH").bind String.toNat?
  IO.mkRef (v.getD 0 != 0)

/-- Hash-cons GC v1 (clear-based): when the intern table's entry count
    reaches this threshold, `maybeGCHashCons` clears it together with every
    derived memo cache — mandatorily including the two bare-pointer
    `InstKey`-keyed caches (`betaLambdaCache`, `contextReuseCache`), which
    would otherwise hold recyclable addresses of objects the cleared table
    may have been the last retainer of. `0` (default) = disabled.
    Set via `BLASTER_HASHCONS_GC=<entry count>`. -/
initialize gcIntervalRef : IO.Ref Nat ← do
  IO.mkRef (((← IO.getEnv "BLASTER_HASHCONS_GC").bind String.toNat?).getD 0)

/-- Number of GC clears performed (diagnostic, reported in the CSV). -/
initialize gcRunsRef : IO.Ref Nat ← IO.mkRef 0

/-- Bisection mask for the v1 clear (diagnosing the 1600 hang):
    bit 0 (1) = clear `hashConsCache`;
    bit 1 (2) = clear the PtrExpr-keyed memo caches;
    bit 2 (4) = clear the InstKey-keyed caches (betaLambda, contextReuse).
    v1 behavior = 7. Set via `BLASTER_GC_MASK`, default 7. -/
initialize gcMaskRef : IO.Ref Nat ← do
  IO.mkRef (((← IO.getEnv "BLASTER_GC_MASK").bind String.toNat?).getD 7)

/-- Rearm point for the GC trigger: fire when the intern table's size
    reaches this value; after firing, set to (post-clear size + interval).
    Without this, a mask that does not clear the table itself would leave
    `size ≥ interval` true forever and fire on EVERY iteration (the
    bisection-sabotage bug of 2026-08-05). `0` = not yet armed. -/
initialize gcNextFireRef : IO.Ref Nat ← IO.mkRef 0

/-- Live intern-table entries surviving the most recent v2 mark-and-rebuild. -/
initialize gcLiveRef : IO.Ref Nat ← IO.mkRef 0

/-- Cumulative milliseconds spent inside v2 GC pauses. -/
initialize gcPauseMsRef : IO.Ref Nat ← IO.mkRef 0

/-- Per-phase v2 pause breakdown (cumulative ms): root collection,
    mark traversal, rebuild/filter sweeps. -/
initialize gcRootsMsRef : IO.Ref Nat ← IO.mkRef 0
/-- Sub-slice of `gcRootsMsRef`: the context-reachability step alone. -/
initialize gcLiveCtxMsRef : IO.Ref Nat ← IO.mkRef 0
initialize gcMarkMsRef : IO.Ref Nat ← IO.mkRef 0
initialize gcRebuildMsRef : IO.Ref Nat ← IO.mkRef 0

@[inline] def enabledIO : IO Bool := enabledRef.get

/-- Bump `r` by `n` iff profiling is enabled. -/
@[inline] def bump (r : IO.Ref Nat) (n : Nat := 1) : IO Unit := do
  if ← enabledRef.get then r.modify (· + n)

-- p0a: would-have-hit probe (local rewrite-cache misses)
initialize p0aLocalMiss : IO.Ref Nat ← IO.mkRef 0
initialize p0aSampled : IO.Ref Nat ← IO.mkRef 0
initialize p0aGlobalHit : IO.Ref Nat ← IO.mkRef 0
initialize p0aActiveHit : IO.Ref Nat ← IO.mkRef 0
/-- Countdown for the 1-in-64 sampling of the (comparatively expensive) probe. -/
initialize p0aCountdown : IO.Ref Nat ← IO.mkRef 64

-- p0b: iteSimp? else-context destruction vs propagation
initialize p0bPropagated : IO.Ref Nat ← IO.mkRef 0
initialize p0bFreed : IO.Ref Nat ← IO.mkRef 0
initialize p0bFreedLive : IO.Ref Nat ← IO.mkRef 0

-- p0c: case-of-case pull-out duplication
initialize p0cMatchPull : IO.Ref Nat ← IO.mkRef 0
initialize p0cDitePull : IO.Ref Nat ← IO.mkRef 0
initialize p0cInnerAlts : IO.Ref Nat ← IO.mkRef 0
initialize p0cOuterAlts : IO.Ref Nat ← IO.mkRef 0

-- hypq: hypothesis-query junk interned into the hash-cons table
initialize hypqCalls : IO.Ref Nat ← IO.mkRef 0
initialize hypqInterned : IO.Ref Nat ← IO.mkRef 0
/-- Nonzero while inside a hypothesis-query predicate (`withHypQuery`).
    Read by `updateHashConsCache` to attribute interns. Always `0` when
    profiling is disabled. -/
initialize hypQueryDepth : IO.Ref Nat ← IO.mkRef 0

/-- Extra GC roots that live only in Lean-stack locals (invisible to the
    driver-stack/env sweeps): the hash-consed ORIGINAL term registered by
    `Optimize.mainAux`. The unroller re-constructs its subterms constantly;
    dropping their table entries mints equal-but-distinct twins whose
    identity loss cascades into Lean-side exponential re-checking. -/
initialize gcExtraRootsRef : IO.Ref (Array Lean.Expr) ← IO.mkRef #[]

/-- Breadcrumb channel for stall diagnosis: rate-limited (1/s) flushed
    one-line pass-entry markers to `$BLASTER_RETENTION_PROFILE.crumbs`.
    The last line before silence names the pass a hung run is stuck in.
    Inert unless profiling is enabled. -/
initialize crumbHandleRef : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none
initialize crumbMsRef : IO.Ref Nat ← IO.mkRef 0
initialize crumbTagRef : IO.Ref String ← IO.mkRef ""

def crumb (tag : String) : IO Unit := do
  if !(← enabledRef.get) then return ()
  let now ← IO.monoMsNow
  let dt := now - (← crumbMsRef.get)
  -- transition-aware: a TAG CHANGE logs after 50 ms (so the final pass
  -- entered before a stall is never suppressed by an unrelated crumb
  -- moments earlier); same-tag repeats log at most 1/s
  if dt < 1000 then
    if tag == (← crumbTagRef.get) || dt < 50 then return ()
  crumbMsRef.set now
  crumbTagRef.set tag
  let h ← do
    match ← crumbHandleRef.get with
    | some h => pure (some h)
    | none =>
      match ← IO.getEnv "BLASTER_RETENTION_PROFILE" with
      | some p =>
          let h ← IO.FS.Handle.mk (p ++ ".crumbs") IO.FS.Mode.write
          crumbHandleRef.set (some h)
          pure (some h)
      | none => pure none
  if let some h := h then
    h.putStr s!"{tag} {now}\n"
    h.flush

/-- Attribute hash-cons interns performed inside `k` to hypothesis-query
    construction. Flag-based (not a real depth): a nested call resets the
    flag on its own exit, slightly undercounting the tail of the outer
    query — acceptable for a diagnostic. -/
@[inline] def withHypQuery [Monad m] [MonadLiftT IO m] (k : m α) : m α := do
  if ← liftM (m := IO) enabledRef.get then
    liftM (m := IO) <| hypqCalls.modify (· + 1)
    liftM (m := IO) <| hypQueryDepth.set 1
    let r ← k
    liftM (m := IO) <| hypQueryDepth.set 0
    return r
  else k

end Blaster.Optimize.Retention
