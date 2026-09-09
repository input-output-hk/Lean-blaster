# Cardano preparation benchmarks

These benchmarks isolate the expensive `#prep_uplc` phase on real
CardanoLedgerApiBlaster scripts. Proof checks are a separate phase. The WSC
case uses the production CIP-153 `programmableLogicGlobal.flat`, with all
inputs symbolic at preparation time.

## Recreate the workspaces

`pins.json` records the exact source revisions. The Cardano `7245eb8` and
PlutusCore WSC `5f2baa2a` revisions are local investigation commits: they were
not available in either upstream or Anastasia-Labs GitHub histories when
checked on 2026-09-09. Supply local clones containing these commits. This
script copies committed source only and applies the small, supplied dependency
and preparation-telemetry patches. It does not copy dirty source changes.

```sh
python3 Benchmarks/cardano/prepare_local.py \
  --root /tmp/cardano-baseline \
  --blaster /path/to/Lean-blaster \
  --cardano /path/to/CardanoLedgerApiBlaster \
  --wsc /path/to/CardanoLedgerApiBlaster-wsc \
  --plutuscore /path/to/PlutusCoreBlaster \
  --plutuscore-wsc /path/to/PlutusCoreBlaster-wsc
```

For a candidate, use a second new output directory and
`--blaster-rev YOUR_CANDIDATE_COMMIT`. Dependencies build before the script
returns. Use the same solver executable and environment for both workspaces.
The helper preserves the libraries' native compilation settings.

## Measure preparation

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-baseline \
  --label baseline --repeat 3 --timeout 240 --max-rss-gib 16 \
  --cases sellnft:1800 minting:1200 paramfeed:10000 governance:9000 global:1600
```

Run the two arms serially, preferably alternating them. No other build or
benchmark should be running during a timing comparison. Use `lake build`,
not a direct `lake env lean` invocation: native elaborator code materially
changes the performance being measured.

The runner removes only its generated module's compiled outputs before each
repetition. It records wall time, aggregate descendant RSS sampled every
0.5 seconds, the output module's size, optimizer milliseconds, final hash-cons
entry count, allocated context IDs, beta cache size, source hashes, revisions,
and tracked-patch hashes. RSS is a sampled process-tree estimate, not an OS
high-water mark. Dependency setup is excluded; module elaboration and teardown
remain included in wall time. `optimize_ms` ends when `Optimize.main` returns.

`results/LABEL/results.json` is checkpointed during execution. Full build logs
are kept beside it. The time and memory limits kill only the owned process
group. A timeout is a censored observation, not a successful preparation.

`--sample` takes one five-second macOS CPU sample after ten seconds. Keep
these profiling runs separate from unprofiled timing comparisons. The runner
uses standard-library Python and `ps`; process inspection must be allowed by
the environment. It does not change allocator settings.

## Check properties against the measured residual

Immediately after preparing one case, run:

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-baseline \
  --label global-proof --cases global:1600 --proofs-only \
  --timeout 240 --max-rss-gib 16
```

The existing preparation source must exactly match the requested case and
budget. No preparation is regenerated in this phase. The global check rejects
the production validator's `SeizeAct` arm with symbolic fields, transaction
info, purpose and parameter. At fuel 1453 or higher it also checks acceptance
of the existing `transfer-nonmember-covering-node` golden against the measured
residual with Blaster. This establishes one accepting execution, not all global
validator properties. SellNFT checks the two positive properties and three
expected counterexamples, including acceptance/non-vacuity. MintingPolicy
checks its two positive properties and negative control; ParamFeed checks its
parameter property. Governance checks its first four properties, through
`invalid_minFeeA_changed`. Each Blaster call has a 30-second solver timeout;
a separately bounded solver executable can enforce a process-level cap.

Blaster's `Valid` result is its existing trusted solver verdict, not a new
kernel-checked equivalence between `PrepUPLC.prop` and the CEK interpreter.
Fuel remains unchanged: CEK exhaustion maps to `State.Error`, so increasing
fuel changes the checked behavior. A cheap rejection property alone does not
show that an accepting execution is covered by the bound.

## Experimental flags and evidence

The [review](../../docs/reviews/cardano-preparation-2026-09-09.md) records the
baseline and explains the rejected prototypes. Archived patches and focused
tests are under `experiments/`. They are not part of Blaster's imported code.
The runner's `--retain-constructor-choices`, `--retain-choice-types` and
`--reduce-before-arguments` flags require the corresponding experimental patch;
they are not options present in the pinned baseline. Rebuild dependencies after
applying a patch, before starting any timed run.

Checked-in result JSON uses relative log basenames. Complete logs remain local;
re-running the harness produces fresh logs. Do not include setup errors,
interruptions, timeouts or profiling runs in successful-run speedup averages.

## Attribute preparation work

Use a checkout containing the normalization profiler (pass its revision with
`--blaster-rev` to `prepare_local.py`). The default pinned baseline predates it.
Build dependencies first and keep profiling separate from timing comparisons:

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label global-profile --cases global:1400 global:1600 \
  --profile-normalize --timeout 300
python3 Benchmarks/cardano/summarize_profile.py \
  /tmp/cardano-candidate/results/global-profile/results.json
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label conversion --cases global:1600 sellnft:1800 --conversion-only
```

`--conversion-only` normalizes the same input conversion function, with all its
arguments symbolic, without applying the interpreter. It is an isolation
experiment, not a subtraction that can be assumed additive: conversion may
interact with later symbolic branch contexts.

`set_option blaster.profileNormalize true` enables the profiler for an
`Optimize.main` invocation. The profiler records exclusive wall time under the
innermost uncached expression's constant head; anonymous expressions inherit
the enclosing head. Cache-hit processing is charged to its enclosing head.
Names are retained; expression graphs and hypothesis contexts are not.

Times sum to the profiled interval, but **include instrumentation overhead**.
Head names describe which normalization was in progress, not whether that work
was static or dynamic. In particular, time under a CEK matcher is not a CEK
transition count, and time under a constructor can include normalization of its
fields. Raw heads are emitted so readers can inspect the attribution rather
than relying on a heuristic namespace classification.

Rewrite-cache hits, misses and metavariable bypasses are counted separately.
Choice-propagation events name the function or constructor across whose argument
an `ite` or `match` was distributed. They count optimizer rewrites, not feasible
execution paths. The existing context and hash-cons sizes remain separate.

The runner sets `BLASTER_PROFILE_FILE` to a dedicated JSONL file. A snapshot is
flushed every million uncached normalization entries and on completion or error;
without this environment variable, snapshots go to command stdout. This avoids
losing every observation when Lean buffers stdout or the runner kills a slow
command. A killed run has only a partial profile. The summarizer checks exact
time accounting and, for completed profiles, balanced normalization frames.
The feature is disabled by default and profile state is local to one invocation.

`PREP_PHASE` reports construction of the interpreter application, final declaration
checking/compilation, and the complete `#prep_uplc` command. The existing
`PREP_METRICS.optimize_ms` measures normalization itself. Whole-module wall time
also includes decoding, other elaboration, and teardown.

## Gate accepting executions

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label global-acceptance --cases global:1600 --acceptance-only
```

This copies `fixtures/GlobalAcceptance.lean` to an owned benchmark module and
checks four existing post-#112 global goldens through the exact benchmark script
and `globalInputs1600` conversion. Successful decoding and a data round-trip are
mandatory. Three goldens must halt with **unit**, not merely halt with a closure;
the negative control must reach a genuine CEK error. Their expected terminal step
counts are 1453, 2782, 3441, and 2370, respectively. Each is also checked one step
short and at ten times its terminal budget. A bounded iteration of real `step`
distinguishes exhaustion from an error that the script actually reaches.

These are executable checks using `native_decide`, which trusts native compilation;
they are not kernel-reduced optimizer equivalence certificates. `--proofs-only`
adds Blaster acceptance and unit-return checks against the prepared `.prop` at fuel >=1453.
Prepare that case without profiling immediately before running its proof phase,
as the runner requires an exact preparation-source match. The gate does not
claim that every accepting witness satisfies every ledger validity condition.

## Verified fused interpreter experiment

Use `prepare_local.py --staged-cek --blaster-rev CANDIDATE` (together with the
source paths above) to apply the supplied interpreter patches. The named and
indexed pins have different environment representations; each patch carries
its own kernel-checked `run_eq_runSteps` and `execute_eq` proof. The indexed
version fuses all CEK transitions. The legacy named version fuses the
Eval/Return loop and retains the reference path for constructor/case control.
The setup also runs 11 named and 17 indexed normalization checks.

Then prepare **one case at a time**, and check its residual immediately:

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label fused-sellnft --cases sellnft:1800 --staged-cek
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label fused-sellnft-proof --cases sellnft:1800 --staged-cek --proofs-only
```

Omit `--staged-cek` for the reference arm on the same optimizer revision and
interpreter checkout. The flag enables the preparation option and adds local
`blaster_specialize` annotations for `StagedCek.eval` and `.ret` (fuel, index 2)
and `.lookupValue` (environment, index 1). Use `--specialize-functions NAME:INDEX`
to override a selected index in an exploratory run. This changes reduction
order using existing function equations, not interpreter semantics or fuel.
The runner requires `PREP_INTERPRETER staged=true` from successful fused prep;
setting a flag in metadata alone is insufficient evidence of activation.

New source files are marked intent-to-add by setup so the existing tracked-patch
hash covers the complete prototype. They are not automatically committed or
pushed. The common original pins and local-commit requirements still apply.
These patches are tied to those pins; the upstream PlutusCore PR targets the
current indexed environment instead.
