# Verified fused CEK preparation, 2026-09-09

## Changes under review

The opt-in `blaster_specialize N` attribute unfolds a labeled function using
its existing equation when a selected argument has a known outer constructor.
It demands that argument before normalizing unrelated dynamic payloads, then
falls back to ordinary optimization when control remains symbolic. Indices
are one based, including implicit parameters. Fully applied calls, opaque
function restrictions, and the existing recursive-unfolding option are respected.
The attribute introduces no assumed equations. Its scope can be local.

The companion [PlutusCore PR #44](https://github.com/input-output-hk/PlutusCoreBlaster/pull/44) exposes `eval` and `ret` separately instead
of building an intermediate CEK state for each transition. Both versions now cover every transition. The earlier named adapter retained
the original interpreter for constructor/case paths; that limitation was removed
after secondary benchmarks exposed the fallback cost. Each has a kernel proof of equality with `runSteps`
for all states, fuel, and builtin semantics variants. The proof uses only the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The executable `.exec` remains the reference interpreter. The certificate
covers replacing the interpreter before normalization; it does **not** certify
Blaster's complete normalizer or convert solver verdicts into kernel proofs.

## Correctness prerequisite

The prototype exposed beta-cache re-entry binding a parameter to an expression
that still refers to that parameter's previous value. A tiny identity application
could grow beyond 4 GiB in seconds. [Issue #242](https://github.com/input-output-hk/Lean-blaster/issues/242) was filed with a bounded cycle
reproducer before [PR #243](https://github.com/input-output-hk/Lean-blaster/pull/243), whose `Issue242.lean` also checks transitive aliases,
unassigned pattern variables, simultaneous swaps, over-application, restoration,
and passing `#testOptimize`/Blaster queries. No false `Valid` verdict was
established for this bug; the reproduced failure is cyclic substitution.

The fix snapshots old argument values before rebinding cached parameters.
This can increase allocation on ordinary preparation, so the primary comparison
uses that **same fixed optimizer** for both reference and fused arms. Earlier
pre-fix timings are contextual history, not the denominator of the new speedups.

## Measurement protocol

Native Lake builds on an Apple M2 Max, 12 logical CPUs, 64 GiB, Lean 4.24.0.
The solver is Z3 4.15.2 with a 30-second process cap and per-query timeout.
Dependencies are warm before timing. Reference and fused arms run serially,
with order reversed on alternate repetitions, identical inputs, fuel, and
solver limits. Every preparation is followed immediately by its proof phase.
Detailed normalization profiling is disabled in these timing runs.

The harness records optimizer time, module wall time, sampled process-tree RSS,
hash-cons entries, context IDs, beta-cache size, residual module size, source
hashes, committed revisions, and tracked patches. A fused preparation is counted
as successful only when the command reports `PREP_INTERPRETER staged=true`.
Three early global scouts had an unwired WSC option and measured the reference
path despite their labels; they are excluded from fused performance evidence.

## Initial paired results (three repetitions per arm)

These observations used the initial named adapter. Its full constructor/case
extension is measured separately below; the indexed global implementation is
unchanged.

| Workload / fuel | Reference prep | Fused prep | Prep speedup | Reference prep + proofs | Fused prep + proofs |
|---|---:|---:|---:|---:|---:|
| SellNFT / 1800 | 39.083 s | 24.046 s | 1.63× | 79.961 s | 66.268 s |
| Production global / 1600 | 58.454 s | 46.275 s | 1.26× | 63.366 s | 50.624 s |

All table values are medians. Preparation is the optimizer's interval; totals
are the median of each paired preparation/proof module wall-time sum. SellNFT
includes its unchanged 30-second timeout in every total. Proof time itself is
37.613 → 39.212 s on SellNFT and 1.659 → 1.651 s on global. The total gains are
therefore **1.21×** and **1.25×**, respectively. These are descriptive results
from three samples, not a statistical confidence claim.

Prep ranges: SellNFT reference 38.946–41.968 s, fused 22.838–25.445 s; global
reference 58.141–62.182 s, fused 46.271–50.297 s. No timed run was discarded.

| Workload | Reference nodes | Fused nodes | Contexts, both arms | Reference peak RSS | Fused peak RSS | Residual `.olean`, reference → fused |
|---|---:|---:|---:|---:|---:|---:|
| SellNFT | 15,574,522 | 8,271,045 | 29,063 | 3.027 GiB | 2.193 GiB | 831,312 → 826,280 bytes |
| Global | 15,668,782 | 8,316,039 | 103,138 | 3.195 GiB | 2.330 GiB | 634,096 → 634,096 bytes |

Node counts fall by about 47%, and sampled preparation memory by 27%. Context
counts do not change. The result isolates reduced interpreter work and allocation,
with no large residual-size inflation. Module size equality is not a semantic
certificate; the acceptance checks and interpreter equality proof are separate.

Raw observations are in
[`Benchmarks/cardano/results/fused-2026-09-09`](../../Benchmarks/cardano/results/fused-2026-09-09).
The measured Blaster commit is `40981aff` with an empty tracked patch in every
primary run. Later commits add only reports and the portable pairing driver.
The legacy named evaluator pin is `0c713ef6`; the indexed evaluator pin is
`09ca8995`, with the complete preparation wiring captured by tracked-patch hashes
and supplied reconstruction patches.

## Correctness gates

- The full native Blaster test suite passes on the specialization branch.
- Seventeen named and seventeen indexed CEK normalization checks pass, including
  capture, field/application order, missing bindings, invalid tags and case
  indices, terminal states, and exact exhaustion boundaries.
- The indexed interpreter's reference equality is kernel checked, as is the
  separate legacy named proof.
- Global acceptance validates four existing production goldens, exact input
  round-trips, terminal step counts 1453/2782/3441/2370, one step short, and ten
  times the required fuel. The three successful goldens must return Unit.
- At fuel 1600, Blaster checks symbolic `SeizeAct` rejection and both acceptance
  and exact Unit return for the nonmember golden against the measured residual.
- SellNFT has two valid properties, two expected counterexamples, and the
  existing multisatisfaction query that times out at 30 seconds. That timeout
  remains a failed proof phase; it is neither omitted nor counted as a pass.

## Reproduction

See `Benchmarks/cardano/README.md`. The supplied setup applies patches to the
exact original workload pins, including the two documented local investigation
commits, and copies the normalization fixtures. A fresh `--no-build` recreation
was checked byte-for-byte against all three interpreter source files in each
measured workspace. New files are marked intent-to-add so tracked-patch hashes
include their contents. The upstream PlutusCore PR instead targets public main
and validates against its pinned Blaster dependency.

## Remaining limits

Fusion reduces interpreter overhead and allocations. It does not merge dynamic
paths: compare context counts as well as elapsed time. Large accepting global
executions require substantially more fuel than the first accepting golden.
Further work should target repeated symbolic contexts while preserving the
acceptance gate, and reduce the conservative cache-snapshot cost without
reintroducing Issue #242. A general claim of unlocked large contracts requires
new completed preparations and proofs at those larger bounds.
