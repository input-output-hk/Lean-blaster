# Reconstruction benchmarks — 13 November 2026

The branch now reconstructs **426 of the 466 goals solved without reconstruction** in the 671-goal BlasterBenchmarking corpus. All 426 passed an independent axiom audit. Forty goals still lose coverage when checked reconstruction is required. The full Blaster source suite is **not green**.

## Revisions and measurement

- Before: `60c3538706747128d78b5158727b7e71076217a8`, with only the [timing instrumentation patch](txpipe-z3-baseline-timings.patch) and the new benchmark harness copied into the checkout. The patch adds logging, without changing proof construction.
- After: reconstruction implementation `1291064b1d7ee84b579c7ea69f99c08720015e40`; `fe5fe33` additionally hardens the focused test's axiom-audit helper. The final alternating measurements and focused rechecks include that test change.
- Corpus: `b7cc5304bde87c269bb3ba57e560304ffd9f2189` of BlasterBenchmarking, using its existing extraction functions and Lean 4.24 Mathlib project.
- Environment: Lean 4.24.0, **Z3 5.3.3**, macOS arm64, 12 logical CPUs. The earlier integration validation used Z3 5.4.0; those historical results are separate.
- Each Lean process explicitly loads the compiled `libBlaster` dynamic library. Earlier interpreter-only source-suite results are not an equivalent timing baseline.

The raw local artifacts are under `analysis/z3-bench-2026-11-13/` in the parent workspace: `final-corpus`, `final-suite-normal`, `final-suite-strict`, `final-focused-normal`, `final-focused-strict`, `final-native-micro`, and `final-paired-native`. They contain generated inputs, logs, replay events, repetitions and revision/configuration metadata. The final corpus library SHA-256 is `9c8984c69005468717eda7fabe2e73c6803fb6a5c3377f05930b513b8791939e`.

## What changed

1. Residual collection uses `getMVarsNoDelayed` and skips already assigned or delayed-assigned metavariables. It preserves the TxPipe replay chain instead of assigning delayed wrappers and generating unused residual proofs.
2. Nonnegativity of a natural-number cast is discharged directly with a checked arithmetic lemma, avoiding expensive general proof search for these encoding assertions.
3. Quantifier-free nonlinear queries first try the legacy Z3 arithmetic solver (`z3arith2`, `smt.arith.solver=2`). This automatic attempt has at most two solver seconds and a ten-second replay deadline, checked between replay steps. The existing portfolio remains the fallback. An explicitly selected portfolio keeps its requested order and budgets.
4. Scalar aliases, `Nat.succ`, and reducible concrete projections are lowered only after definitional-equality checks. Predicate aliases such as `Set α` are exposed as function types.
5. A checked preparation step at the SMT boundary unfolds predicate heads definitionally and rewrites function equality to pointwise equality. The only supplied simplification lemma is `f = g ↔ ∀ x, f x = g x`, proved using `congrFun` and `funext`. This also applies inside hypotheses. The returned Z3 proof is transported back and checked against the original residual before composing the original theorem proof.
6. Recursive interpretation/coercion consumes Lean recursion depth, so a cyclic SMT macro can be rejected normally. This does not eliminate every native stack overflow.

The boundary preparation in item 5 does not require a new user tactic call. It runs between optimizer certificate replay and SMT translation. It supplies an explicit proof for extensionality; it does not assume that the optimizer's result and its actual replay residual are definitionally equal. No trusted axiom or whole-goal `grind` fallback was added, and no optimizer proof expectation was weakened.

## Alternating before/after measurements

Three pairs per theorem, with order before/after, after/before, before/after. Fresh native processes, one solver seed, ten-second solver budgets, 120-second external limits. The table reports medians. The host was shared with other work; the measurements are observations, not confidence intervals.

| Goal | Wall time before → after | Expanded proof DAG before → after | Accepted residual replays before → after | Total accepted Z3 steps before → after |
|---|---:|---:|---:|---:|
| `∀ w x y z : Nat, w ≤ x → y ≤ z → w*y ≤ x*z` | 9.094 s → 1.761 s | 49,998 → 6,478 | 5 → 1 | 602 → 48 |
| `isInjective square` on `Nat` | 2.010 s → 1.805 s | 21,674 → 12,031 | 1 → 1 | 52 → 33 |
| `∀ x y : Nat, x / (y+1) ≤ x` | 3.315 s → 2.287 s | 39,928 → 35,330 | 2 → 1 | 187 → 94 |

For the multiplication example, this is about **5.2 times faster** end to end and **7.7 times fewer expanded DAG nodes**. Median theorem generation, including optimizer replay and proof checks but excluding process startup and the size traversal, drops from 7,646 ms to 365 ms. The old five accepted replays included unused certificates; they are not five parts of the final reachable proof.

The [paired results CSV](txpipe-z3-paired-benchmarks.csv) also records generation time, stored-forest size, output-file size and peak process RSS. These are comparisons with the preceding implementation, not with a short hand-written library proof.

### Size definitions and wider microbenchmarks

The harness captures the environment before elaborating the theorem. It follows reachable newly generated declarations and expands them for the DAG measurement. Imported library lemmas and benchmark definitions remain references. Unused generated declarations are excluded. A node is a distinct Lean expression object, including partial applications; sharing is preserved. This is neither printed line count nor allocated bytes.

The stored-forest metric additionally traverses the root type and reachable auxiliary types/values; it includes the small synthetic collector spine joining those expressions. `.olean` size includes the measurement harness and other module declarations. Peak RSS includes Lean startup and size measurement. `root_recheck_ms` checks the root with auxiliaries already available, and must not be presented as the cost of checking every auxiliary proof. Generation and replay timings include their checks.

The [16-case microbenchmark CSV](txpipe-z3-microbenchmarks.csv) includes every case, with three attempts per version. Before, 11 cases passed all repetitions; after, 14 did. The newly passing cases are successor existence and two predicate-equality examples. Some already small proofs grow because actual optimizer certificates are now composed; there is no general claim that every proof shrinks. Broad-run wall times were collected alongside corpus workers and are screening data; use the alternating table above for the targeted timing comparison.

Both difficult modulo cases failed all three final attempts at these budgets:

```lean
∀ x y z : Nat, (x + y*z) % y = x % y
∀ x y z : Nat, (z*x) % (z*y) = z * (x % y)
```

The second reconstructed in two of three earlier native attempts, but not in the final run. It remains unstable and is not counted as fixed.

## Full BlasterBenchmarking corpus

Every extracted goal ran once in each mode, for 1,342 attempts. `trusted` uses `blaster (reconstruct: 0)`; `strict` uses `blaster (gen-proof: 1)`. Both include the existing optimizer, with the same original per-goal external budgets: 20 seconds, or 90 seconds for UPLC. There were three workers, two Lean pool threads per process, and an 8 GiB per-process memory limit. Tactic portfolios can create additional threads. No ambient `BLASTER_*` override is inherited; solver seeds are the backend defaults.

| Outcome | Trusted | Strict |
|---|---:|---:|
| Passed | 466 | 426 |
| Failed with diagnostics | 148 | 174 |
| External timeout | 56 | 70 |
| Process crash | 1 | 1 |
| Total | 671 | 671 |

Every strict success was also a trusted success. The one crashing goal in both final modes was `UPLCDepth/d_sum_4096`. Failed theorem elaborations may leave an error-recovery `sorryAx` in Lean's diagnostic output; those attempts are failures, never accepted proofs.

| Suite | Goals | Trusted passed | Strict passed |
|---|---:|---:|---:|
| AesopHome | 50 | 28 | 28 |
| AutoHome | 50 | 36 | 30 |
| BlasterHome | 50 | 44 | 38 |
| HammerHome | 50 | 37 | 36 |
| ITL4 | 44 | 44 | 44 |
| MiniF2F | 96 | 48 | 34 |
| NNG4 | 108 | 103 | 103 |
| STG4 | 52 | 48 | 41 |
| SmtHome | 50 | 41 | 40 |
| UPLCDepth | 7 | 5 | 5 |
| UPLCWidth | 6 | 6 | 3 |
| Verina | 108 | 26 | 24 |

An earlier native full run before the predicate/alias preparation reconstructed 379 goals. The final run reconstructs 426: 49 newly passing and two previously passing goals now timing out (`MiniF2F/amc12_2000_p12` and `Verina/verina_basic_81`). Trusted successes were identical in the two runs. STG4 improves from 2 to 41 checked proofs. Timeout-sensitive changes elsewhere should not all be attributed to a single fix.

The corpus harness's first-theorem extraction is preserved. In particular, `Verina/verina_basic_47` and `verina_basic_48` benchmark the first helper theorem in their files, not their entire multi-theorem specifications. The generated-input manifests record that limitation.

All per-goal outcomes are in [txpipe-z3-corpus-results.csv](txpipe-z3-corpus-results.csv). The [40 reconstruction losses](txpipe-z3-corpus-losses.csv) include the original source, first diagnostic and an individual reproduction command:

| First observed failure category among trusted successes | Count |
|---|---:|
| External timeout | 14 |
| Untranslated instance-field projection | 7 |
| Recursive-function translation | 6 |
| Other translation failures | 6 |
| Recursion-depth limit | 3 |
| Polymorphic function coercion in STG4 | 3 |
| Eliminated binder | 1 |

These are first-failure categories, not a count of distinct root causes. Fourteen timeouts do not establish that replay is logically unsupported. Conversely, repairing a projection can expose another translation or reconstruction gap.

## Full Blaster source suite

Every one of the 161 sources was invoked afresh with the native library, in repository-default and strict modes, with a 120-second external per-file limit. After the test helper was hardened to resolve namespace names before auditing axioms, the focused Z3 file was rechecked in both modes; those two fresh rows replace its earlier rows.

| Outcome | Repository defaults | `BLASTER_GEN_PROOF=1` |
|---|---:|---:|
| Passed | 151 | 129 |
| Lean diagnostic failure | 3 | 19 |
| Native/process crash | 0 | 2 |
| External timeout | 1 | 5 |
| Dependency blocked | 6 | 6 |
| Total sources | 161 | 161 |

The six blocked entries are aggregate modules missing test dependency `.olean` files while the suite has failures. They are listed separately. Defaults still include explicitly strict tests such as `SmtNatMod`. Per-file results are in [txpipe-z3-native-suite-results.csv](txpipe-z3-native-suite-results.csv).

The default failures are the retained `NormChoiceAppDite_10` optimizer proof gap, two difficult strict modulo properties, and `Counter06`'s solver-sensitive counterexample-message mismatch. `SmtPredQualifier` times out. Strict mode additionally exposes polymorphic/recursive translation and replay gaps; `Issue29` also has user axioms that the standard-axiom policy intentionally rejects. `SmtMatch` and `SmtRecFun` still crash. The five strict file timeouts are `Issue17`, `SmtEqArith`, `SmtNatMod`, `SmtNatMul` and `SmtPredQualifier`.

The focused Z3 source passes in both modes: **16 named positive theorems and two checked commands**, plus negative checks for false claims, incomplete proofs, cyclic macros and forbidden axioms. The full strict source run emitted 380 accepted proof-request messages, including proofs in files that subsequently failed; this is not 380 independent benchmark successes. `lake build Blaster Tests.Reconstruct.Z3 Blaster:shared` also passes, 261 jobs.

## Reproduction

From this checkout, with the sibling corpus and its Lean 4.24 Mathlib project available:

```sh
lake build Blaster Tests.Reconstruct.Z3 Blaster:shared
python3 scripts/benchmark_reconstruction.py --out /tmp/blaster-micro --repeat 3
python3 scripts/benchmark_corpus.py --out /tmp/blaster-corpus --workers 3
python3 scripts/check_reconstruction_suite.py --mode normal --out /tmp/blaster-tests-default
python3 scripts/check_reconstruction_suite.py --mode strict --out /tmp/blaster-tests-strict

# One remaining loss; use a fresh output directory for a changed configuration.
python3 scripts/benchmark_corpus.py --modes strict --goals STG4/sub_inter \
  --out /tmp/blaster-sub-inter
```

`benchmark_corpus.py` also accepts `--corpus` and `--mathlib-project`. The microbenchmark accepts `--cases`, `--backends`, `--solver-timeout`, `--limit` and `--execution`. Native execution is the default.

To reproduce the old baseline, create a separate checkout at `60c3538`, copy `scripts/benchmark_reconstruction.py`, `scripts/ReconstructionBench.lean` and `scripts/reconstruction-cases.json` from this branch, apply `txpipe-z3-baseline-timings.patch`, and build `Blaster:shared` there. Run each checkout's microbenchmark with `--repeat 1 --cases nat_mul_mono` into distinct directories, alternating the order for three pairs; repeat for the other two goals. Keep both checkouts and solver binaries fixed throughout.

The branch remains `codex/txpipe-z3-reconstruction`, with all 29 pinned TxPipe PR heads preserved. It remains an experimental integration branch based on the TxPipe feature stack, not a rebase of that stack onto current main. No PR has been opened.
