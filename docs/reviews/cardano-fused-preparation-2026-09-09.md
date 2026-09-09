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

## Final paired results (three repetitions per arm)

These results use the complete named and indexed evaluators, including
constructor and primitive case transitions. All preparations retain fully
symbolic inputs; their domains have not been narrowed.

| Workload / fuel | Reference prep | Fused prep | Prep speedup | Reference prep + proofs | Fused prep + proofs |
|---|---:|---:|---:|---:|---:|
| SellNFT / 1800 | 39.569 s | 23.336 s | 1.70× | 80.862 s | 65.089 s |
| Governance / 9000 | 35.410 s | 22.574 s | 1.57× | 42.352 s | 28.789 s |
| Production global / 1600 | 58.454 s | 46.275 s | 1.26× | 63.366 s | 50.624 s |

All table values are medians. Preparation is the optimizer's interval; totals
are the median of each paired preparation/proof module wall-time sum. SellNFT
includes its unchanged 30-second timeout in every total. Median proof module
time is 37.423 → 39.178 s on SellNFT, 4.404 → 4.409 s on Governance, and
1.659 → 1.651 s on global. Total gains are **1.24×**, **1.47×**, and **1.25×**,
respectively. The total is the median of paired sums, not the sum of phase
medians. These are descriptive results from three samples, not a statistical
confidence claim. The SellNFT proof phase becomes slightly slower, despite
the overall improvement.

Prep ranges: SellNFT reference 38.904–41.638 s, fused 22.277–24.252 s;
Governance reference 35.295–37.302 s, fused 20.960–23.991 s; global reference
58.141–62.182 s, fused 46.271–50.297 s. No run from these paired series was
discarded.

| Workload | Reference nodes | Fused nodes | Contexts, both arms | Reference peak RSS | Fused peak RSS | Residual `.olean`, reference → fused |
|---|---:|---:|---:|---:|---:|---:|
| SellNFT | 15,574,522 | 8,271,483 | 29,063 | 3.027 GiB | 2.193 GiB | 831,312 → 826,280 bytes |
| Governance | 10,889,149 | 5,070,510 | 17,761 | 2.082 GiB | 1.872 GiB | 2,216,312 → 2,216,312 bytes |
| Global | 15,668,782 | 8,316,039 | 103,138 | 3.195 GiB | 2.330 GiB | 634,096 → 634,096 bytes |

Node counts fall by 47% on SellNFT/global and 53% on Governance. Sampled
preparation memory falls by 28%, 10%, and 27%, respectively. Context counts
do not change. This is evidence of reduced interpreter work and allocation,
without large residual-size inflation. Module size equality is not a semantic
certificate; acceptance checks and the interpreter equality proof are separate.

Raw observations are in
[`Benchmarks/cardano/results/fused-2026-09-09`](../../Benchmarks/cardano/results/fused-2026-09-09).
The final named series uses Blaster `a07d55b4` and named evaluator `096c7a22`.
The global series uses Blaster `40981aff` and indexed evaluator `09ca8995`.
Blaster has an empty tracked patch in all these runs. No optimizer code changed
between those two Blaster revisions: later commits added reports, the pairing
driver, and the complete named benchmark adapter. The indexed implementation
and wiring are unchanged. Each arm uses the same fixed optimizer as its paired
reference. Interpreter preparation wiring and local dependency changes are
captured by tracked-patch hashes and supplied reconstruction patches.

`final-summary.json` summarizes `final-sellnft-1800-*`,
`final-governance-9000-*`, and `paired-global-*`. The archive also preserves
earlier observations explicitly as history; see its README for the mapping.

## Secondary checks and higher bound

One final reference/fused pair using the complete named adapter checks the two
smaller workloads. These are spot checks, not three-sample estimates:

| Workload / fuel | Reference prep | Fused prep | Reference prep + proofs | Fused prep + proofs | Proof outcomes, both arms |
|---|---:|---:|---:|---:|---|
| MintingPolicy / 1200 | 6.360 s | 3.774 s | 12.625 s | 9.882 s | 2 Valid, 1 expected counterexample |
| ParamFeed / 10000 | 0.140 s | 0.124 s | 3.307 s | 3.296 s | 1 Valid |

MintingPolicy prep is 1.69× faster in this pair; its node count falls from
3,275,325 to 1,968,184 with 7,575 contexts in both arms. ParamFeed's whole-module
time is essentially unchanged. These `complete-secondary-*` runs use
`a07d55b4` plus only the two final symbolic-fallback tests in the tracked patch;
the optimizer and interpreter implementations match the main named series.

The complete indexed evaluator at **global fuel 1800 still times out after
240.037 seconds**, with sampled peak RSS 5.13 GiB. Its raw result is
`fused-global1800.json`. Lean did not flush the activation or optimizer metrics
before termination; the requested source and its hash are recorded. This is
a censored experiment, not a completed fused preparation or a speedup sample.
There is no residual proof result at this bound. Fusion has **not** unlocked it.

The earlier partial named adapter improved SellNFT but left Governance's
constructor/case work in the reference interpreter: a secondary pair measured
35.526 → 37.605 s, with essentially unchanged node counts. Completing those
paths produced the final Governance improvement above. The initial SellNFT
series (39.083 → 24.046 s) and partial-adapter secondary observations remain
archived under `paired-sellnft-*` and `secondary-*`; they are not pooled into
the final named medians.

## Correctness gates

- The full native Blaster test suite passes on the specialization branch.
- Symbolic list-tail and surrounding-match fallback checks pass, including a
  kernel theorem for the explicit symbolic-tail residual.
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
- All four measured Governance properties remain Valid in every pair.
- The public PlutusCore PR builds and tests against its exact pinned Blaster
  dependency `c576289c`; its Linux build and CodeQL checks pass.

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
paths: context counts remain 103,138 for global at fuel 1600. That bound covers
only the first accepting golden; the other two require 2782 and 3441 transitions.
The 1800 timeout confirms that the next bottleneck remains unresolved.

The next experiment should attribute repeated normalization to the expression
and the hypotheses actually read, then evaluate reuse across contexts that agree
on those dependencies. A cache keyed only by an ancestor context is insufficient:
context-sensitive reductions must remain valid under the reused hypotheses.
Measure unique expressions versus expression/context pairs before implementing
reuse. Preserve exact fuel and accepting Unit-return checks, and require a
completed larger preparation plus its proofs before claiming a newly unlocked
bound. Separately, reducing the conservative beta-cache snapshot cost is useful
only if all Issue242 aliasing and restoration regressions remain passing.
