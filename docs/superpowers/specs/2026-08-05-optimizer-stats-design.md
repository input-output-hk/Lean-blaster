# Optimizer Growth Telemetry (`stats-file`) — Design

**Date:** 2026-08-05
**Issue:** [#138](https://github.com/input-output-hk/Lean-blaster/issues/138) — `#prep_uplc` scales poorly on large UPLC validators
**Status:** Approved

## Problem

Issue #138 has a mature external diagnosis (colll78's budget-ladder data): the prepared
residual grows ×1.84 per +100 CEK budget steps, wall time ×2.83, peak RSS ×1.68 — an
exponential answer, not a leak. What is missing is *in-tool attribution*: Blaster has no
instrumentation, so every investigation (angerman's counters, colll78's RSS traces) rebuilds
ad-hoc tooling outside the repo. Killed/OOM runs — the interesting ones — lose everything a
post-hoc report would say.

## Goal

An opt-in, crash-surviving record of *which optimizer state grows, when*, cheap enough to
leave in production code, exposed to downstream consumers (`#prep_uplc`) through the
existing options plumbing.

Non-goals (deferred; schema has room): per-symbol/rule-fire attribution, RSS sampling,
any change to optimizer behavior.

## Surface

Two new solve options in the existing `(key: value)` grammar (`Blaster/Command/Syntax.lean`),
carried by `BlasterOptions` (`Blaster/Command/Options.lean`), hence available to `#blaster`,
`#solve`, `#kind`, and downstream commands that thread `BlasterOptions`:

- `(stats-file: "prep_growth.jsonl")` — enables telemetry, names the sink file.
  Default `none`: zero behavior change, one `Option` check per optimizer step.
- `(stats-interval: 100000)` — stack steps between samples. Default 100,000
  (≈156 samples for the 15.6M-step budget-501 run quoted in the issue).

If PlutusCoreBlaster whitelists option keywords for `#prep_uplc`, exposing these two there
is a one-line downstream follow-up (out of scope here).

## Architecture

In-band counter + inline sampler (chosen over an out-of-band watcher task — the optimizer
state lives in `StateT`, invisible to other threads — and over Lean trace machinery — trace
messages accumulate in elaborator memory, worsening the OOM regime, and die with the process).

New module `Blaster/Optimize/Stats.lean`:

- `OptimizeStats` — state record: `handle : Option IO.FS.Handle`, `interval : Nat`,
  `steps : Nat`, `nextSampleAt : Nat`, `startMs : Nat`. Lives in the translate-env state
  alongside `optEnv`.
- `initStats` — called once at optimize entry when `statsFile` is set: opens the file
  (truncate), writes the `start` event. Open failure → `logWarning` + stats disabled;
  the solve proceeds.
- `bumpStatsAndMaybeSample` — called at the top of `optimizeExprAux`
  (`Blaster/Optimize/Basic.lean`). Disabled path: single `Option` check. Enabled path:
  increment `steps`; when `steps ≥ nextSampleAt`, run `sampleStats`.
- `sampleStats` — reads `IO.monoMsNow` and the O(1) `.size` of each tracked cache, appends
  one JSON line, flushes (flush-per-line is what makes killed runs analyzable). A write
  failure disables stats silently (no error spam at sample cadence).
- `finalizeStats` — writes the `end` event, closes the handle; at `verbose ≥ 1` logs a human
  summary (total steps, elapsed ms, top-8 caches by final size). Gating the summary behind
  `verbose` keeps default command output stable for the golden-message test suite.

## Schema (JSONL)

One JSON object per line. Three event shapes:

```jsonl
{"ev":"start","schema":1,"unfoldDepth":100,"maxDepth":10,"interval":100000}
{"ev":"sample","steps":100000,"ms":812,"mcDepth":0,
 "globalRewrite":51234,"localRewrite":210,"whnf":20411,"synthInstance":12,
 "match":95,"recFunInst":40,"recFun":38,"recFunMap":38,
 "hypMap":45,"eqMap":12,"matchInCtx":312,"localDecls":58,
 "inferType":80211,"isProp":15002,"getFunBody":9110,"isResolvable":420,
 "isType":1200,"isNotFun":310,"isCstMatchProp":95,"getFunEnvInfo":2013,
 "memNamed":1650}
{"ev":"end","steps":15598844,"ms":171003,"samples":156}
```

Field map (all `Std.HashMap`/`HashSet` sizes, O(1)):

| field | source |
|---|---|
| `globalRewrite`, `localRewrite` | `OptimizeEnv.globalRewriteCache` / `.localRewriteCache` |
| `whnf`, `synthInstance`, `match` | `.whnfCache` / `.synthInstanceCache` / `.matchCache` |
| `recFunInst`, `recFun`, `recFunMap` | `.recFunInstCache` / `.recFunCache` / `.recFunMap` |
| `hypMap`, `eqMap` | `hypothesisContext.hypothesisMap` / `.equalityMap` |
| `matchInCtx` | `.matchInContext` (outer map size) |
| `localDecls` | `.ctx.ctx` local context size (only non-cache structure that grows) |
| `inferType` … `getFunEnvInfo` | the `Expr`-keyed maps of `MemoizeEnv`, individually |
| `memNamed` | sum of the `Name`-keyed `MemoizeEnv` maps (bounded by program size) |
| `mcDepth` | `OptimizeOptions.mcDepth` (correlates samples with BMC/k-induction depth) |

A run killed by OOM/timeout leaves a valid file ending after the last flushed sample —
that is the intended behavior, not an error.

## #138 workflow this enables

Re-run colll78's budget ladder with `stats-file` on. Plot per-cache curves against `steps`.
The cache whose curve tracks the ×1.84 residual growth identifies the structure holding the
exponential answer (candidate: `globalRewriteCache` keying distinct symbolic CEK states),
which is exactly the reconvergence structure a DAG-merge/streaming fix must target.
Complements PR #155 (hashconsing) rather than duplicating it.

## Testing

- `Tests/` addition: a small `#blaster (stats-file: "<scratch>.jsonl") (stats-interval: <small>)`
  run, followed by `#eval` assertions: every line parses as JSON; `steps` strictly monotone
  across samples; exactly one `start` and one `end` event; `end.steps > 0`.
- A default-options run asserting no file is created and command output is unchanged.
- Failure-path test: `stats-file` pointing into a nonexistent directory → warning, solve
  still succeeds.

## Performance guardrails

- Disabled: one `Option` check per `optimizeExprAux` iteration (same class as existing
  per-step flag checks).
- Enabled at default interval: ~25 O(1) size reads + one small JSON line + flush per
  100k steps — sub-permille of the 171 s / 15.6M-step reference run.
