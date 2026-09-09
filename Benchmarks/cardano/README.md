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
info, purpose and parameter. It does not establish non-vacuity or all global
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
