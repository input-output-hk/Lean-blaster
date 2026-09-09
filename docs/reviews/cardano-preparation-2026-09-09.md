# Cardano preparation: measurements and experiments, 2026-09-09

## Scope and method

Preparation is the dominant measured phase. On the production CIP-153 global
validator at 1,600 CEK steps, preparation takes 63.08 s, of which 59.46 s is
inside `Optimize.main`. A subsequent symbolic rejection property takes 1.67 s.
That property covers the rejected SeizeAct arm only; it does not establish
acceptance coverage or the validator's other properties.

The baseline is the reviewed beta stack at `36c3a15a9fdc9f3237ad376f8d67665e3742d3f8`
(PR #235), not a new revision of the beta branch. Measurements use native Lake
builds on an Apple M2 Max, 12 cores, 64 GiB RAM, Lean 4.24.0. Dependencies were
built first. Timed cases ran serially, with no concurrent test/build jobs.
The runner samples aggregate descendant RSS every 0.5 s. This is not a process
high-water mark. No allocator tuning was applied.

The [reproduction guide](../../Benchmarks/cardano/README.md) and
[pins](../../Benchmarks/cardano/pins.json) identify all five repositories.
Two pins are local investigation commits unavailable on GitHub when checked;
reproduction requires local repositories containing those commits. The setup
helper copies committed source only. The WSC script uses the CIP-153-capable
PlutusCore revision; ordinary Cardano examples use upstream PlutusCore.

## Baseline

These are single scout observations, except SellNFT which was repeated for a
paired proof check. They identify bottlenecks; they are not confidence intervals.

| Case | CEK fuel | Preparation wall | Optimizer | Hash-cons entries | Context IDs |
| --- | ---: | ---: | ---: | ---: | ---: |
| SellNFT | 1,800 | 38.53 s | 35.62 s | 8,106,674 | 29,063 |
| MintingPolicy | 1,200 | 7.84 s | 5.98 s | 1,682,983 | 7,575 |
| ParamFeed | 10,000 | 1.70 s | 0.20 s | 52,254 | 154 |
| Governance | 9,000 | 37.51 s | 34.59 s | 7,293,990 | 17,761 |
| CIP-153 global | 1,400 | 12.81 s | 11.09 s | 3,131,631 | 22,056 |
| CIP-153 global | 1,600 | 63.08 s | 59.46 s | 15,595,053 | 103,138 |
| CIP-153 global | 1,800 | >240 s (timeout) | — | — | — |

The 1,800-step run reached a sampled 6.90 GiB before its time limit; it did not
hit the 16 GiB memory limit. The subsequent 2,000-step scout was deliberately
cancelled. Its partial time must not be used as a benchmark result.

Increasing global fuel by 14% (1,400 to 1,600) increased optimizer time by 5.4×
and retained hash-cons entries by 5.0×. Fuel bounds evaluation work, but the
symbolic preparation cost is highly nonlinear. Hash-cons entries count retained
optimizer nodes, not the final residual expression's live nodes.

A separate five-second CPU sample during global preparation showed expression
abstraction/substitution, hash-consing, context membership, allocation and
reference counting. It is a short diagnostic window, not a whole-run attribution.
The large retained expression/context counts make avoiding repeated expansion a
higher-priority experiment than changing the SMT solver.

## Experiments that failed their gates

- **Ancestor rewrite reuse, adapted from existing PR #160.** A small port reduced
  global 1,600 optimizer time from 59.46 to 35.34 s and retained nodes from 15.60 M
  to 9.83 M. However, returning an ancestor normal form directly skipped
  simplifications enabled by a child's hypotheses. The full test suite reported
  normalization regressions. This port was removed; its speedup is not a ready
  optimization. PR #160 also contains GC/retention and allocator work which this
  experiment did not port.
- **Bounded memoization of pure substitution/abstraction.** It produced roughly
  1.89 M hits on global 1,600, but optimizer time was 60.10 s and the retained
  hash-cons count was unchanged. A high cache hit rate did not translate into a
  useful speedup. This prototype was removed.
- **Retain every constructor's field choices.** SellNFT optimizer time fell to
  1.62 s and Governance to 1.65 s. Global 1,600 instead regressed to 105.85 s;
  ParamFeed regressed from 0.20 to 1.63 s. The paired SellNFT proof phase grew
  from 37.45 to 157.27 s. Both versions proved the same two positive properties,
  found the same two counterexamples, and hit the 30 s solver cap on the
  multi-satisfaction check. The preparation-only gain therefore moved substantial
  work into proving. Some retained-choice preparations also introduced existing
  `sorry`-fallback warnings in hypothesis proof reconstruction. This mode is not
  a general recommendation.
- **Retain choices only for List, Prod and Plutus Data.** This preserved the
  ordinary examples' preparation cost, but global still took 107.12 s inside the
  optimizer. Naming selected types did not resolve the production regression.
- **Unfold functions before normalizing their arguments.** Small unused-argument
  and projection tests passed, but global 1,600 exceeded 120 s, and SellNFT hit
  the 16 GiB memory cap after about 51 s. Governance was cancelled when this
  approach was rejected. This prototype was removed.

The constructor experiment exposed an independently reproducible scaling issue:
[issue #238](https://github.com/input-output-hk/Lean-blaster/issues/238). A list
of 12 independent conditional elements creates 16,379 contexts with unconditional
constructor hoisting, versus 47 when those field choices remain inside their
constructors. The corresponding retained node counts are 117,084 and 2,817.
The issue was filed before the proposed regression test `Issue238.lean`.

## Proof coverage and fuel

Each candidate must be checked against the same properties and solver cap after
preparation. A small `.olean` or a fast rejecting property is insufficient:
CEK fuel exhaustion produces `State.Error`, so under-fuelled preparation can
make rejection vacuous. Larger fuel must be paired with accepting witnesses or
negative controls that distinguish meaningful acceptance from always-error.
The runner preserves fuel and input conversion for paired comparisons.

Blaster's current `Valid` verdict is its trusted solver result. These experiments
do not add a kernel-checked equivalence between a prepared `.prop` and `.exec`.
The harness records separate preparation and proof measurements and verifies
that the proof phase uses exactly the requested prepared source.

## Direction for larger gains

The more ambitious route is to specialize the fixed UPLC program into reusable
blocks while retaining dynamic data and path conditions separately. This would
avoid repeatedly walking the interpreter and distributing independent data
choices through every state. A sound implementation must preserve CEK step
accounting, errors, builtin semantics and binder scope; loop summaries need
explicit proof obligations rather than an assumed relationship to unrolling.

This direction is supported by staged symbolic-execution work such as
[GenSym (ICSE 2023)](https://continuation.passing.style/static/papers/icse23.pdf)
and the newer [GenWasym preprint](https://arxiv.org/abs/2608.18327), which stages
a definitional WebAssembly interpreter and uses continuations and snapshots.
Their results motivate an architecture experiment, not a predicted Blaster
speedup: concolic path exploration differs from universally quantified Cardano
proofs. No breakthrough or published speedup from those systems is claimed here.

The [archived prototype patches](../../Benchmarks/cardano/experiments/README.md)
make the rejected algorithm experiments inspectable and reproducible separately
from the unchanged production optimizer in this benchmark branch.

Raw measurement records are in [Benchmarks/cardano/results](../../Benchmarks/cardano/results).
Status fields distinguish successful runs, setup errors, timeouts, memory limits
and deliberate interruptions. Profiling times are excluded from comparisons.
