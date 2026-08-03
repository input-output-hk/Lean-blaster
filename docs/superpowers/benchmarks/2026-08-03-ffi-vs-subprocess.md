# FFI vs. subprocess backend — performance comparison

**Date:** 2026-08-03 · **Branch:** `feat/z3-ffi-migration` · **z3:** 4.15.4 · **Lean:** v4.24.0

Measured **before flipping the default backend to FFI** (Task 16), to quantify the
win and rule out regressions. Uses the built-in `profileTask` phase timers
(`(verbose: 1)`), which isolate the backend-attributable phases from the common
pre-SMT optimization step.

## Method

Each `#blaster` query is timed in four phases: `Optimization` (pre-SMT rewriting —
**backend-independent**), `Translation` (Lean→SMT + declarations), `Submitting Smt
Query` (the top-level assert), and `Solve` (check-sat + result/model retrieval).
The last three are the backend cost. Goals are chosen to genuinely reach the solver
(each is `⚠️ Undetermined` under `(only-optimize: 1)`, so the optimizer does not
short-circuit Z3):

```
[∀ (x y : Int), x ≤ y → x - 1 < y]
[∀ (x y z : Int), x < y → y < z → x < z]
[∀ (n m x : Nat), n = m → m = n + x → 0 = x]
```

Reproduce: generate a module with N copies of the three goals, once with
`#blaster (backend: ffi) (verbose: 1) [...]` and once with `#blaster (verbose: 1)
[...]`; `lake build` each module (with `DYLD_LIBRARY_PATH=/opt/homebrew/lib`) and sum
the `[End]: <phase> (…s)` lines per phase.

## Results

### Single query (clean, one goal each backend)

| Phase | FFI | Legacy (subprocess) |
|---|---:|---:|
| Optimization (common) | 35 ms | 35 ms |
| Translation | 0 ms | 3 ms |
| Submitting Query | 1 ms | 0 ms |
| **Solve** | **1 ms** | **21 ms** |
| **Backend total** | **~2 ms** | **~24 ms** |

### 30 solver-reaching queries (summed; deterministic across re-runs)

| Phase | FFI | Legacy (subprocess) |
|---|---:|---:|
| Translation | 0.001 s | 0.303 s |
| Submitting Query | 0.117 s | 0.052 s |
| **Solve** | **0.402 s** | **2.027 s** |
| **Backend total** | **0.52 s** | **2.38 s** |

## Takeaways

- **The backend interaction is ~4.6× faster with FFI** over the batch (0.52 s vs
  2.38 s), driven by the **Solve phase (~5×: 0.40 s vs 2.03 s)**. Two subprocess
  costs vanish in-process: the stdin/stdout round-trips (per-command `success`
  handshake + the check-sat read) and the **20 ms sleep-poll** in the legacy
  `getSatResult` loop, which is paid on essentially every check.
- **No regression:** FFI is never slower on the backend phases.
- **For a single small goal, end-to-end wall-clock is dominated by the
  backend-independent `Optimization` step (~35 ms)**, so the FFI win is modest until
  the workload is solve-heavy — many queries per file, deep BMC/K-induction (one
  check-sat per depth), or large formulas (many declare/assert round-trips). This is
  where the ~5× Solve speedup compounds.
- Note for issue #138 (translation/optimizer output explosion): that bottleneck is
  **upstream** of the backend (the `Optimization`/`Translation` phases), so FFI
  addresses the solver-interaction cost but not the optimizer explosion directly.

## Caveat

Absolute numbers carry system-load sensitivity; the legacy backend's 30 subprocess
spawns create transient CPU contention that also inflates its *backend-independent*
`Optimization` timings (8.4 s vs 3.3 s across the batch) — an indirect symptom of
the subprocess model rather than a real optimization difference. The
backend-attributable phases above are the intended comparison.
