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
