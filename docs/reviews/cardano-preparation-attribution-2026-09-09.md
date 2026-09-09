# Cardano preparation: attribution and accepting executions

This follow-up to PR #239 adds opt-in normalization profiling and an accepting
global-validator gate. It changes no normalization rule. The measurements select
the next specialization experiment; they are not an optimization speedup claim.

## Reproduction and validation

Implementation: `6575b13c`, followed by `4b0ddd06` (exception-cleanup tests, a
stronger prepared unit-return check, and excluding replayed preparation metrics
from proof-phase timings). Workloads and their exact revisions remain those in
`Benchmarks/cardano/pins.json`. The benchmark setup patches now also separate
application construction and declaration checking from normalization. Applying
them to fresh copies reproduced the measured dependency diffs byte for byte.

Machine: Apple M2 Max, 12 logical CPUs, Lean 4.24.0. Runs were native Lake builds,
serial after warming dependencies. Solver checks used Z3 4.15.2 with the existing
30-second cap. Per-run results and final profiles are in `Benchmarks/cardano/results/attribution/`;
commands and metric definitions are in `Benchmarks/cardano/README.md`.

The full `lake test` suite passes. Its first run hit the previously observed
`Tests/Smt/SmtNat/SmtNatMod.lean:37` solver timeout while tests were building;
the retry passed. Focused tests compare normalized expressions and hash-cons/
context counts with profiling on and off, check exact timing accounting, and
check cleanup after both success and an exception. A deliberately capped
six-second preparation retained a valid partial JSONL profile and was reported
as a timeout, not a completed preparation.

## Input conversion is cheap in isolation

Each row reports three runs normalizing the original input conversion function
with symbolic arguments, without applying the CEK interpreter.

| Conversion | Normalization milliseconds | Median | Hash-cons entries |
|---|---|---:|---:|
| Global | 116, 110, 117 | 116 ms | 41,460 |
| SellNFT | 58, 56, 58 | 58 ms | 7,317 |
| Governance | 80, 76, 80 | 80 ms | 15,652 |

These costs cannot simply be subtracted from full preparation. In the full
global-1600 profile, CardanoLedgerApi normalization heads account for 3.57 seconds,
including 2.25 seconds under an output-list conversion helper. Conversion-derived
expressions can be processed again in interpreter branch contexts.

With profiling disabled, full global-1600 normalization takes **57.017, 55.012,
and 55.859 seconds** (median **55.859 seconds**). Application construction takes
0–1 ms; final declaration checking/compilation takes 31–32 ms. Whole-module time
is 58.12–60.44 seconds. Every run retains the same 15,595,053 hash-cons entries,
103,138 allocated context IDs, and 633,904-byte output module as the earlier
baseline. The older baseline scout was 59.456 seconds; these are not paired
evidence of a speedup from the diagnostic hooks. A subsequent unprofiled run
after collecting profiles takes 55.779 seconds, with the same structural counts.

## The preparation cliff tracks propagation of the remaining computation

One diagnostic run per row. A normalization request is a rewrite-cache hit,
miss, or metavariable-containing expression for which lookup is bypassed.

| Metric | Global 1400 | Global 1600 | SellNFT 1800 |
|---|---:|---:|---:|
| Profiled normalization | 12.39 s | 64.75 s | 40.23 s |
| Normalization requests | 11,883,838 | 55,686,815 | 41,228,296 |
| Rewrite-cache hits | 7,106,208 | 33,262,159 | 25,383,164 |
| Rewrite-cache misses | 2,893,268 | 13,474,894 | 4,259,525 |
| Metavariable bypasses | 1,884,362 | 8,949,762 | 11,585,607 |
| Allocated context IDs | 22,056 | 103,138 | 29,063 |
| `runSteps` match propagation | 7,782 | 35,132 | 9,816 |
| `runSteps` conditional propagation | 1,540 | 8,994 | 2,859 |
| `List.cons` match propagation | 582 | 582 | 2 |

The global fuel increase is 14.3%; normalization requests grow **4.69×**, and
propagation of `runSteps` across choices grows **4.73×**. Direct list-constructor
match propagation stays at 582. These are optimizer events, not counts of
feasible program paths, but they identify where the additional work appears.

In global-1600, **19.5%** of profiled time is under `List.cons`, with 6.13 million
uncached normalization entries. Heads prefixed `PlutusCore.UPLC.CekMachine.`
account for **41.3%**; builtin dispatch and `runSteps` are prominent. The same
namespace accounts for **53.0%** in SellNFT, where `ifBoundOtherwiseError` and
its generated matcher together account for **14.3%**. This makes variable access
and environment handling an especially useful target in the smaller script.

These are exclusive wall times under syntactic normalization heads. Anonymous
expressions inherit their enclosing head, and the figures include diagnostic
overhead. A constructor's time may include work in its fields. A CEK head's time
does not establish that its work is statically removable. Global-1600 profiling
adds about **16%** relative to the three-run unprofiled median. All three complete
profiles have balanced frames and exactly partition their measured interval;
they preserve the earlier node/context counts and output-module sizes.

## A real accepting execution is now part of the benchmark

The fixture reuses the existing post-#112 global goldens and the exact
`programmableLogicGlobal1600.script` used by the preparation benchmark. It checks
the golden literals against their serialized data through the existing
`TermsCheck` module, successful typed decoding, and an exact round-trip through
`globalInputs1600`.

| Golden | First terminal transition | Required result |
|---|---:|---|
| transfer-nonmember-covering-node | 1,453 | Unit halt |
| transfer-member-single-policy | 2,782 | Unit halt |
| transfer-mixed-many-policies | 3,441 | Unit halt |
| transfer-containment-violation-REJECT | 2,370 | Genuine CEK error |

All four pass executable checks at their terminal budget, one step below it,
and at ten times that budget. The counting evaluator distinguishes unfinished
execution from a real error; `runSteps` intentionally maps fuel exhaustion to
`State.Error`. Accepting results must contain unit, not just any halting value.

At fuel 1600, Blaster also proves the nonmember golden accepts against the
**prepared `.prop`**, alongside the existing universal SeizeAct rejection
property. The final fixture additionally proves that the prepared result
returns unit. All three properties pass in three serial runs: 1.672, 1.668, and
1.674 seconds for the proof phase after preparation. Fuel 1400 is too low for this particular witness; fuel 1600 is
sufficient. Larger member and mixed-policy witnesses remain useful future
targets at 2782 and 3441.

The executable checks use `native_decide`, which trusts native compilation.
They are regression gates, not a kernel-reduced equivalence certificate between
`.prop` and `.exec`, and they do not establish every ledger validity condition.
The proposed staged compiler still needs a separate correctness argument.

## Selected first specialization experiment

Start with **SellNFT's fixed CEK control and variable access**, keeping dynamic
environments and the remaining computation shared. The global results motivate
sharing continuations across symbolic state choices; merely changing constructor
distribution has already failed the end-to-end gate in draft PR #240.

Keep the first experiment bounded: a small set of fixed-program blocks with
explicit dynamic operands, exact CEK fuel costs, and an interpreter fallback for
unsupported operations. Measure whether it actually reduces normalization
requests and `runSteps` distribution, then check preparation plus proofs and the
accepting golden. Neither the namespace percentages nor staging papers predict
the obtainable speedup.

[PlutusCoreBlaster PR #42](https://github.com/input-output-hk/PlutusCoreBlaster/pull/42),
checked at `dce72b54641fa5e0959a54cb5d22f2350f410576`, already proposes fuel-free
step iteration and composition lemmas. Reuse or adapt that work when proving
block simulation; do not duplicate it. It currently targets `main` and notes
overlap with PRs #34 and #40, so compatibility with the pinned CIP-153 interpreter
must be checked explicitly. See the updated staged-preparation design for the
remaining semantic and performance gates.
