# Certificate-directed reconstruction prototype

This experiment is on `codex/z3-certificate-replay`, based on `e91c7db` of the
TxPipe + Seungheon integration. It is **opt-in**, with
`BLASTER_SMTPROOF_CERTIFICATES=1`. The preceding reconstruction path remains the
default. No PR has been opened in either repository.

The prototype works in Blaster and in an experiment using the official Z3 Lean
exporter. **It has not established a performance improvement.** In particular,
the reflected identity is slower on the dense native test below.

## Implemented vertical slice

- `SmtProof/Encoding.lean` creates a `CheckedGoalEncoding` before the proof solver
  runs. It records the source goal, actual SMT assertion, its Lean interpretation
  and a kernel-checked proof of `¬source → interpreted assertion`. Replay can use
  that transport directly. This currently covers the main input assertion;
  auxiliary assertions and unsupported bridges keep the existing path.
- `Certificate/IntFarkas.lean` depends only on Lean. A certificate is a list of
  weighted polynomial expressions with strict/non-strict signs. `check_sound`
  proves that normalization to a contradictory constant yields `False` from
  the supplied bounds. `constant_eq` exposes the identity-checking component.
  The Boolean normalization checks are reduced by the kernel. The normalizer is
  Lean's existing verified commutative-ring normalizer.
- `SmtProof/Farkas.lean` reads integer, rational and finite-decimal coefficients,
  clears denominators, translates supplied arithmetic facts, and constructs an
  application of the checker theorem. It does not search for multipliers or run
  an arithmetic tactic. Inequality signs are normalized; equalities retain their
  signed multiplier. Unsupported hints retain the old replay fallback.
- Replay statistics distinguish `encoding-contract` and `certificate-farkas`
  from tactic methods. Structural replay, scopes, sharing, final kernel checks
  and axiom restrictions remain in force.

This is a proof of concept for two explicit contracts, not a replacement of the
entire translation registry or a complete verified SMT checker. Integer cuts,
coefficient-free arithmetic hints, nonlinear certificates, higher-order and
polymorphic encodings still need their own support. A malformed hint may fall
back to the old prover; the direct checker tests independently require rejection.

## Blaster validation

Lean 4.24.0, Z3 5.3.3, native Blaster library. The build
`lake build Blaster Tests.Reconstruct.Certificates Tests.Reconstruct.Z3 Blaster:shared`
passes (271 jobs). The new direct tests cover strict inequalities, clauses,
transport of bounds, signed equalities, rational/decimal weights, altered or
missing coefficients, zero denominators, consistent premises, incorrect source
provenance and unrelated input assertions. The named proofs and checker theorem
pass standard-axiom audits. The existing focused suite passes with the feature
enabled, including its 18 positive proof requests.

An initial alternating A/B screening ran four goals, three pairs each, using
fresh processes and one solver seed. All 24 attempts passed. The observed
median expanded proof DAG sizes were:

| Goal | Existing path | Prototype |
|---|---:|---:|
| Integer linear chain | 11,712 | 11,306 |
| Natural multiplication monotonicity | 6,478 | 6,596 |
| `isInjective square` | 12,031 | 12,139 |
| Natural division bound | 35,330 | 35,646 |

Wall times were close, without a consistent improvement. The prototype's 12
accepted residual replays used the input contract 12 times and direct Farkas
replay nine times. Multiplication monotonicity still uses the existing nonlinear
arithmetic path. These measurements preceded the factoring of the shared
identity lemma for the native exporter; their raw metadata records that source
state. They are screening results, not a speed claim for the final source.

The final full strict source run attempted all **162** files:

| Outcome | Files |
|---|---:|
| Passed | 130 |
| Lean diagnostic failure | 20 |
| Timeout | 4 |
| Process crash | 2 |
| Dependency blocked | 6 |

Relative to the previous 161-file strict run, the new certificate test passes;
`SmtNatMod` changes from timeout to diagnostic failure. All other file statuses
are unchanged. The suite is not green. It emitted 391 accepted proof-request
messages, including proofs in files that subsequently failed; these are not 391
independent benchmark successes. The full 671-goal corpus was not rerun for this
prototype.

Raw observations: [Blaster comparison](z3-certificate-prototype-blaster.csv),
[source-suite results](z3-certificate-prototype-suite.csv). DAG sizes use the
existing benchmark's expansion of all reachable fresh helpers, preserving
sharing and keeping imported lemmas as references.

## Official Z3 Lean backend experiment

The Python exporter was inspected at
[`708879ef23599153d4f0adb3af58fb514e2c8942`](https://github.com/Z3Prover/z3/blob/708879ef23599153d4f0adb3af58fb514e2c8942/examples/python/proof_to_lean.py).
It **already uses Farkas combinations** for selected large integer conflicts.
Its `_farkas_combination` constructs explicit nonnegativity evidence; the sum's
identity is discharged by `simp +arith`, with `omega` as fallback. Small
conflicts normally keep the tactic route. Thus "use the coefficients" alone
would duplicate existing upstream work.

`scripts/benchmark_z3_native_certificates.py` is a read-only adapter over that
exporter. For the same conflicts selected by its existing heuristic, it replaces
only the identity proof by `IntFarkas.constant_eq` with reflected expression and
valuation data. The existing bound evidence and the rest of the native proof
remain unchanged. It writes an isolated Lean workspace, not changes to the
upstream checkout.

Both variants consume the **same saved native certificate**. Each proposed
reflected helper is checked for an actual dependency on `constant_eq`, so a
silent fallback to the old tactic cannot count as a successful experiment.
Dependency inspection awaits asynchronous theorem elaboration. Every final
proof is compiled with `--trust=0`, warnings as errors, an 8 GiB limit, and a
standard-axiom audit. Both variants include the same Lean imports and audit
harness. The three fixtures are in `Tests/Reconstruct/CertificateInputs`.

Environment: Lean 4.34.0 and Python Z3 5.4.1.0 (`145c0c51570a357cc558ce898ce77573ba9d4fbf`).
Each table entry is the median of three alternating fresh-process checks.
Checking includes imports and the audit; solver runs and library compilation
are excluded. These timings cannot be compared directly to the Lean 4.24
Blaster measurements. The machine was shared, and timings varied substantially.

| Native fixture | Official | Reflected | Reflected Farkas identities |
|---|---:|---:|---:|
| Small linear chain, control | 0.924 s | 0.846 s | 0 |
| Wide conflict, 20 variables, large coefficients | 2.347 s | 2.278 s | 1 |
| Dense conflict, 20 variables | 6.662 s | 12.616 s | 1 |

All **18** checks passed. The control has no changed proof step, illustrating
the timing noise. The wide fixture does not demonstrate a speed improvement.
The dense fixture exposes a regression, rather than supporting replacement of
the existing identity prover. Its module size is slightly smaller (7,879,104
versus 7,861,144 bytes), while its printed source is larger. Module size includes
the encoding, helpers and audit harness, not just a root proof term.

The portable checker and this benchmark are concrete material for evaluating a
contribution. A useful next experiment would be a checker specialized to sparse
linear combinations, avoiding general polynomial normalization. Whether that
helps must be measured against the official heuristic and larger real inputs.
The current results do not justify a performance PR.

Raw [native observations](z3-certificate-prototype-native.csv) include process RSS,
source/module sizes and repetitions. Local full artifacts, generated Lean and
native JSON are under `analysis/z3-certificate-prototype-2026-11-13/` in the
parent workspace (`native-final`, `native-dense`, `paired`, `source-suite`).

## Reproduce

```sh
lake build Blaster Tests.Reconstruct.Certificates Tests.Reconstruct.Z3 Blaster:shared
python3 scripts/benchmark_reconstruction.py --certificates \
  --out /tmp/blaster-certificates --cases int_linear_chain nat_div
BLASTER_SMTPROOF_CERTIFICATES=1 python3 scripts/check_reconstruction_suite.py \
  --mode strict --out /tmp/blaster-certificate-tests
```

For a normal theorem, keep `blaster (gen-proof: 1)` and set the environment flag
for the Lean process. Native source invocation on macOS:

```sh
BLASTER_SMTPROOF_CERTIFICATES=1 lake env lean \
  --load-dynlib=.lake/build/lib/libBlaster.dylib MyTheorem.lean
```

The corpus runner also accepts `--certificates`. To compare against the official
backend, use a Python environment with `z3-solver` installed and the pinned Z3
checkout; the experiment uses the Lean toolchain from that checkout:

```sh
python scripts/benchmark_z3_native_certificates.py \
  --upstream /path/to/z3 --out /tmp/z3-native-certificates \
  Tests/Reconstruct/CertificateInputs/chain.smt2 \
  Tests/Reconstruct/CertificateInputs/wide.smt2 \
  Tests/Reconstruct/CertificateInputs/dense.smt2
```

The standalone checker also compiles directly with Lean 4.34.0; it imports no
Blaster module. A contribution would still require upstream review of its API,
appropriate benchmarks and evidence of benefit for the chosen use case.
