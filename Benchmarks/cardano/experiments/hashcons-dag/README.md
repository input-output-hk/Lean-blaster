# Hash-consing shared input graphs

Issue [249](https://github.com/input-output-hk/Lean-blaster/issues/249) isolates
exponential traversal of an expression DAG when canonicalizing children
changes their pointers. The global intern table stores canonical nodes; it
cannot always look up an original composite whose child pointers differ.
The reproduction needs no CEK code, eviction, garbage collection, or staging.

The per-walk source-pointer memo was already implemented in
[PR160](https://github.com/input-output-hk/Lean-blaster/pull/160), by
Anastasia-Labs at `9caca28412f96415487f743417a8d1d7a00e8f50`. This change ports
that idea onto PR248 without the larger retention/GC/cache-reuse work.
Keys keep source expressions alive for the duration of one traversal.

The regression `Tests/FixedIssues/Issue249.lean` builds a physically shared,
linear-sized Nat expression with two alpha-equivalent identity lambdas using
different binder names. It bounds allocation heartbeats for two walks of the
same original graph, checks stable canonical output and its type, and requires
`#testOptimize` to reduce the depth-20 expression to zero. It is imported by
the normal test suite. On unmodified PR248 (`2cc060ca`), the exact regression
fails at 47,186,118 allocation heartbeats; the original issue's slightly
different measurement harness recorded 39,846,173 at the same depth.
These are allocation counts, not wall-clock thresholds.

## Validated refinement

The final measured code is `d747cee2`. It keeps the usual canonical lookup
first, memoizes only original nodes whose pointers change, and avoids setting
up a traversal for an already-interned root. The regression passes with 537
and 326 allocation heartbeats. The full native suite passes (736 jobs), and
the 37 named CEK/recursive-search controls pass. An initial concurrent build
hit the existing `SmtNatMod.lean:35` solver timeout; that module passed alone
with unchanged settings, followed by a passing full-suite build. Relevant
output is retained in the validation excerpts.

Three new alternating serial pairs measured the final code against PR248:

| Case | PR248 prep | Refined fix prep | PR248 prep + proof checks | Refined fix total |
| --- | ---: | ---: | ---: | ---: |
| SellNFT, fuel 1800 | 19.823 s | 20.345 s | 57.288 s | 57.246 s |
| Governance, fuel 9000 | 22.603 s | 23.204 s | 26.998 s | 27.619 s |

The cells are medians of three measurements. Optimizer-only medians were
17.528 → 17.981 s and 20.734 → 21.266 s respectively. Ordinary preparation
still costs about 0.5–0.6 s more in this small sample; SellNFT's combined
total is effectively unchanged. The reason for this fix is eliminating
exponential traversal of shared inputs, not a claimed speedup on these two
ordinary runs. `refined-results.json` retains all 24 module measurements;
`summary.json` contains the medians. All paired inputs, dependency pins,
counters, artifact sizes and proof outcomes match.

## Direct port comparison

Commit `befd4757` first ported the memo directly, inserting every completed
composite and probing it before the canonical table. Its regression passes
with 467 and 304 allocation heartbeats for the two calls. The native test
suite passes (735 jobs), as do the 37 named CEK/recursive-search controls.

Three alternating serial paired runs found ordinary preparation overhead:

| Case | PR248 prep | Direct port prep | PR248 prep + proof checks | Direct port total |
| --- | ---: | ---: | ---: | ---: |
| SellNFT, fuel 1800 | 19.754 s | 20.891 s | 57.070 s | 58.293 s |
| Governance, fuel 9000 | 21.972 s | 23.696 s | 26.380 s | 28.122 s |

Each cell is the median of three measurements (totals are per-pair sums).
Optimizer-only medians were 17.624 → 18.865 s for SellNFT and
20.063 → 21.420 s for Governance. This version is not a contract-level
speedup. Its full results remain in `eager-port-results.json`.

The refinement probes the canonical table first, skips local entries for
unchanged nodes, and returns already-interned roots before allocating traversal
state. The current canonical table does not evict during a walk, so unchanged
nodes remain available there. If eviction is introduced later, this invariant
must be revisited rather than copying this optimization into a GC variant.

## Measurement method

Both workspaces use native Lake builds, Lean 4.24.0, the same named fused-CEK
overlay, and Z3 4.15.2 with a 30-second solver bound, on the existing Apple
M2 Max machine. Dependencies are warmed before measurement. Each preparation
run regenerates the same target module; its matching property module is then
checked immediately. There is no concurrent owned benchmark or dependency
build. CPU sampling is disabled; process-tree RSS is sampled to enforce a
12 GiB bound. Each module has a 120-second outer time bound.

SellNFT keeps the two previously certified recursive-search recognizers;
Governance uses the ordinary fused evaluator. Neither comparison enables the
experimental closed-body or constructor-shape block compiler. Source and
property-file hashes are pinned in `input-hashes.json`; each result includes
repository pins and patch hashes, generated-module hash, flags, timings,
counters, artifact sizes and verdicts.

All direct-port pairs have identical input modules, dependency pins, residual
sizes, hash-cons table sizes, context counts, beta-cache sizes and proof
outcomes. SellNFT retains two Valid results, one existing solver timeout,
and two Expected Falsified negative controls. Governance retains four Valid
results. SellNFT's total therefore includes an unresolved timeout; it is not
a successful proof time for all its properties. Neither sub-10-second target
has been met by this comparison.

To reproduce on two prepared workspaces:

```sh
python3 Benchmarks/cardano/experiments/hashcons-dag/run-pairs.py \
  --reference /path/to/reference-workspace \
  --candidate /path/to/candidate-workspace
```

The driver stops if preparation fails or an expected proof outcome changes.
The hash-consing regression is independent of these contracts and of any
particular Y/Z combinator encoding. Removing this traversal pathology supports
the broader compiler work; it does not establish arbitrary mainnet coverage.
