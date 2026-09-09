# Certified recursive searches for the legacy Cardano interpreter

This opt-in adapter recognizes two literal SellNFT search bodies and replaces
their repeated CEK interpretation with direct Lean recursion. One searches an
association list for an integer payload; the other searches for a map payload.
Both use the empty byte-string key. This is an adapter for the pinned CEK with
named variables used by the Cardano examples. It is not an implementation for
the indexed interpreter in PlutusCore PR #44.

## Installation and measurement

Add `--staged-cek --lifted-search --blaster-rev YOUR_CANDIDATE_COMMIT` to the
[`prepare_local.py`](../../prepare_local.py) invocation documented in the
[benchmark guide](../../README.md). The script installs these modules in the
named PlutusCore checkout, applies the preparation switch, and builds the
integration and production-template checks. The indexed WSC adapter is not
extended by this flag.

```sh
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label search-preparation --cases sellnft:1800 \
  --staged-cek --lifted-search --timeout 120 --max-rss-gib 12
python3 Benchmarks/cardano_bench.py --root /tmp/cardano-candidate \
  --label search-proofs --cases sellnft:1800 --proofs-only \
  --staged-cek --lifted-search --timeout 120 --max-rss-gib 12
```

Keep the flags identical between preparation and proofs. Omit `--lifted-search`
for the fused CEK reference. The runner records and checks actual interpreter
activation. All timing comparisons must run serially after dependency builds.

Inside the prepared legacy workspace, the opt-in switch is
`set_option plutuscore.liftedSearch true`, together with
`set_option plutuscore.stagedCek true` and the specialization annotations emitted
by the runner. Its default is false. The `.exec` definition retains the original
CEK evaluator.

## Exact semantics

The syntax check alone does not authorize a replacement. Recognition also
checks the captured builtin bindings and recursive closure, preserving lexical
shadowing. Unrelated captured bindings are allowed. Other bodies, alpha-renamed
templates, unsupported arguments, and failed environment checks use the
ordinary interpreter path.

`SpecializedCall` describes a worker that returns a value and its remaining
original CEK fuel. Its certificate proves both fuel decrease and equality to
the reference evaluation under every continuation and semantics variant.
`CekBlocks` supplies composition and short-fuel lemmas. Each search proves:

- Empty list: 16 transitions to Return.
- Matching well-formed entry: 103 transitions to Return.
- Nonmatching well-formed entry: 92 transitions to the next loop entry.
- Invalid key: Error after 45 transitions; invalid payload: Error after 58.

Insufficient fuel is included in the proof. Malformed payloads still fail even
when their key does not match. The continuation resumes at the exact remaining
fuel; no larger budget or stronger input assumption is introduced.

Runtime dispatch uses booleans and an unindexed `CallPlan`. Theorems relate it
to the indexed certificate, avoiding repeated normalization of types containing
the captured environment. `LoopCekProofs.run_eq_runSteps` and `execute_eq` cover
all states, programs, inputs, and fuel. The equivalence proofs use only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. They do not use
`sorry`, `native_decide`, or `blasterProven`.

`LiftedTemplateSource.lean` separately proves that both templates occur in the
actual decoded production SellNFT script, without axioms. These certificates
do not rely on the diagnostic JSON export. `LoopCekControl.lean` contains 37
`#testOptimize` controls for captures, shadowing, fallback behavior, malformed
data, constructor/case behavior, and exact fuel boundaries.

## Scope and evidence

See the [measurement report](../../results/recursive-search-2026-09-09/README.md).
The current SellNFT preparation remains above 10 seconds. Governance has no
matching supported loop and incurs dispatch overhead when this flag is forced;
leave it disabled there. The remaining predicate search and Governance's
Z-combinator and mutual-recursion bodies are future specialization targets.

The first integrated, indexed-plan prototype regressed preparation and a
negative-control outcome. An unindexed single-search version reduced work but
still timed out on that control. The two-search candidate restores the original
outcomes in the measured runs. SellNFT still has its pre-existing 30-second
solver timeout; it is not counted as a successful proof.

The integration exposed Lean-blaster issue #245, fixed separately by PR #246
with `Issue245.lean`. This adapter is stacked on that fix. No new language
primitive or unproved rewrite is introduced into the solver.
