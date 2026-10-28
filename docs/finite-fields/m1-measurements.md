# FFM-20: M1 normalization and native-pipeline measurements

## Job summary

Added the offline bounded runner, result checker, pinned configuration, shared
proof-metric support, paired normalization harnesses, native harness, isolated
replay invocation, raw results and retained setup/harness diagnostics.
Production code and protected existing files are unchanged.

The final [results.json](../../benchmarks/finite-fields/results.json) contains
**54 cases / 216 actual runs**: 54 warmups and 162 measured repetitions.
Measured outcomes are **150 successful harness/corpus checks, nine command
failures and three heartbeat-limit failures**. Across warmups too, counts are
200, 12 and four respectively. The failures are the explicitly retained false
goals, composite-ring certificate rejection and low-heartbeat experiment.
Successful harness execution of the unsupported-input case means its rejection
checks passed, **not** that the unsupported proposition was solved.

All 26 required runnable parent entries were exercised. Both approaches proved
all 12 paired representative identities. The final runner/checker passed,
including all 15 evidence-corruption rejection scenarios. Both exact PROJECT
gates and `make test-pure` passed. No required local validation remains unrun.

Configuration SHA-256:
`733b1dc15325519aa53dea2fb0f32a957b4afdc1a7fce2a1a8f2bfa81294b83a`.
Corpus SHA-256:
`62dc069a61c5f5d7fe2af100f547d709eccac16e14c9156515d0f2767f98a3cf`.

The measured platform is Linux/aarch64,
`7.2.12-orbstack-00394-gbecdd6130068`, with 16 exposed CPUs but a cgroup quota of
**200,000 µs per 100,000 µs period** (two CPU-equivalents), and an 8 GiB memory
ceiling. The exposed ARM identifiers are implementer `0x61`, part `0x000`,
architecture 8, variant `0x0`; the physical host model is not disclosed.
Configuration validation pins these exposed identifiers, kernel and quotas;
results retain full raw hardware metadata.

Maximum observed measured-run memory was **1,256,496 KiB** by wait4 and
**2,002,264,064 bytes** by aggregate sampled RSS. No final measured run hit a
wall, CPU, memory, output or worker-kill limit. The heartbeat-limit failures are
separate from those OS resource limits.

## Scope and trust boundary

This investigation consumes the committed [FFM-19 corpus](benchmark-corpus.json)
and [audit bookmark](m1-rule-audit.md). The latter explicitly defers the full M2
rule audit: this report does not turn it into a proof qualification.

Every one of the parent's 26 runnable entries is required, grouped into its 16
unchanged invocations. The 24 catalogue-only entries remain catalogue-only.
Missing Nethermind, cyclic-5 and exact historical constraints are not replaced
by invented sources. Newly authored F7 and Curve25519 circuits retain the
parent's provenance and limitations. The eight-gate degree-five certificate is
a bounded circuit representative, not a production cryptographic scale result.

The native harness calls the existing `Translate.main`, records its actual
route and retained solver transcript, and checks the staged native-field route.
A native `unsat`/`Valid` result is **not a reconstructed Lean proof**. No
production code, optimizer rule, solver protocol or trust boundary is changed.

| Production stage | Measurement boundary |
| --- | --- |
| Optimization | Existing `profileTask` wall trace, when completed |
| Translation | Existing trace; unavailable if optimization discharges the goal or translation rejects it |
| SMT submission | Existing trace, when a query is sent |
| Solve | Existing composite trace, including protocol and optional model extraction |
| Solver-only time | Not separately available |
| Value display | Not separately timed; native false-goal case requires actual get-value requests/responses and nonempty display values |
| Capability preflight/setup | Included in whole-file time; no exclusive production timer |
| Production proof reading | **Not available at M1** |
| Production proof checking | **Not available at M1** |
| Final verified transport | **Not available at M1** |

The isolated FF-04 fixed-text reader is not the production native pipeline or a
general FF-rule checker. Checked normalization proves only the supplied reflected
identity; it does not supply reification, ideal membership, finite-domain
completeness or transport through arbitrary optimizer rewrites.

## Reproduction contract

- [config.json](../../benchmarks/finite-fields/config.json) pins the corpus,
  parent inputs, local Lean sources, new harnesses, runner/checker, probe, tool
  executables and Lean shared libraries by SHA-256. It records exact commands,
  environment, grammar, assumptions, provenance and setup requirements.
- [benchmark.py](../../scripts/finite_fields/benchmark.py) never fetches tools.
  It invokes the unchanged parent `--offline --check` interface before running
  any benchmark. `make ff-stage` is the sole acquisition step.
- Runs are serial: one retained warmup and three measured repetitions per case,
  repeat-major ordering. Adjacent decide/grind cases reduce, but do not eliminate,
  ordering and thermal/cache bias. Imported modules and filesystem caches are
  warm; theorem files are elaborated afresh.
- Both approaches use the exact imported parent reflected expressions and the
  same unconditional `lhs.eval ctx = rhs.eval ctx` goal. Decide applies
  `Expr.denote_eq_from_toPolynomial_eq` and ordinary kernel `decide`; grind
  unfolds those expressions and uses **`grind (ematch := 0)`**. No imported
  equality certificate is reused to close the comparison goal.
- Circuit/implication comparisons measure the unconditional certificate identity,
  not a change in source hypotheses. The unchanged parent invocations separately
  check residual-zero lemmas and source conclusions.
- Nominal `Residue` nonzero-modulus instances are proved, not assumed. The exact
  Curve25519 **base** field and existing primality proof are retained. Source,
  evidence and successful proof metrics enforce the transitive allowlist
  `propext`, `Classical.choice`, `Quot.sound`; no native decision axiom is allowed.
- Most Lean harnesses use 200,000 heartbeats and 30 s wall/CPU limits. The explicit
  one-heartbeat case is a separate resource-limit experiment, not one side of a
  comparison. Parent invocations retain their 20/60 s wall limits. Every run
  records its own exact limits.
- The worker has an 8 GiB cgroup memory ceiling. Each benchmark process has a
  4 GiB **virtual-address-space** ceiling; process-group RSS is sampled and the
  group killed above 3 GiB. These are different metrics. Serial execution leaves
  a 5 GiB resident-memory budget for the agent, runner and other tools. No build
  or test workload runs concurrently with measurements.
- Process groups are killed on wall, aggregate sampled-memory or output limits.
  CPU and virtual-address limits are inherited by children. Diagnostics are
  bounded at 1 MiB; output-limit termination is an explicit outcome. A durable
  `running` journal makes worker interruption incomplete, never successful.

## Units and availability

Whole-file/process elapsed time uses `time.monotonic_ns` around fork/exec/wait.
It includes Lake, imports, elaboration, kernel work, `.olean` emission where
requested, logging and monitoring. The selector samples approximately every
10 ms plus `/proc` traversal; observation latency and shared-worker scheduling
matter especially for short solver invocations. Raw user/system CPU times and
resource observations are retained alongside wall time.

`wait4_maxrss_kib` is the largest individual-process resident high-water mark,
including waited descendants, **not an aggregate simultaneous tree peak**.
`sampled_peak_tree_rss_bytes` sums the process group's sampled RSS; shared pages
can be counted repeatedly and brief peaks can be missed. Neither is presented
as exact aggregate physical memory. Hardware, OS, `/proc/cpuinfo`, cgroup limits
and complete execution environment are recorded in results.

Lean profiler diagnostics are retained raw. Lean 4.24's `Lean/Util/Profile.lean`
defines these as **exclusive component times**; `Lean/AddDecl.lean` places the
`type checking` timer around kernel declaration checking. Both sources are pinned
in the configuration. The runner extracts the cumulative `elaboration`,
`type checking` (reported as kernel), `tactic execution` and `import` totals.
These are whole-file components, including harness declarations and metric
emission, not isolated theorem costs. Elaboration excludes separately labelled
tactic/typeclass work; kernel time excludes imported declarations. Disabled or
missing profiler components remain null. Normalization/reconstruction within a
single tactic are not separately instrumented.

Production `profileTask` stage traces have 1 ms resolution; a printed zero means
a rounded sub-millisecond stage, not a zero-duration successful run. Whole-run
success must have strictly positive finite elapsed time.

**Proof-size metric:** recursively count nodes in the resulting theorem's
`Lean.Expr` tree, including binder types and repeated occurrences. Referenced
constant declarations are not unfolded; this is neither transitive proof size
nor kernel reduction cost. Newly emitted `.olean` bytes are reported separately
as compiled-artifact size, never as proof-term size. Native verdicts have no
reconstructed proof-size value.

## Integrity checks

[check_benchmark_results.py](../../scripts/finite_fields/check_benchmark_results.py)
verifies immutable inputs/tools/config, the successful offline parent probe,
every configured warmup and measured run, exact commands/environment/limits,
status consistency with exit/output evidence, log-derived metrics and recomputed
summaries. Missing parent corpus classes cannot be replaced by catalogue rows.
Incomplete journals, invalid setup and all-no-work categories are rejected.

Summaries retain all outcome counts and all-run distributions, with a separately
labelled success-only distribution. They use sample standard deviation; warmups
are excluded. Failures are not silently discarded. This is a consistency checker,
not a cryptographic attestation that a human could never fabricate a complete,
self-consistent log.

## Initial setup failure

[setup-failures.json](../../benchmarks/finite-fields/setup-failures.json) preserves
the first attempt, including the exact command, limits and raw output. At a 2 GiB
virtual-address ceiling, the `Semantic.lean` setup compilation exited 139 with
empty diagnostics; no measured case ran. The same setup command passed with a
4 GiB virtual-address ceiling (1.400236056 s; wait4 maximum 1,223,684 KiB;
sampled aggregate RSS 1,938,411,520 bytes). This supports an address-space-budget
explanation, not a theorem or solver failure. The final configuration records
the revised ceiling for both normalization approaches identically.

The initial 53-case full pass also exposed two harness-only expectation errors.
Its failure observations and all summary counts are retained in
[initial-harness-diagnostics.json](../../benchmarks/finite-fields/initial-harness-diagnostics.json):
representation admission rejects *during* optimization, before an `End` trace;
and closed arithmetic retains a nominal-sort association, not a source-variable
association. The latter's intermediate smoke failure is retained too. The
corrected checks require the observed unsupported route before assertion or
`check-sat`, and require no free-variable associations for the closed identity.
No production implementation or existing expected result was changed.

An initial checker invocation exposed a dictionary-iteration bug in category
coverage (`string indices must be integers, not 'str'`). The checker now iterates
case values. The final configuration pins the corrected checker and harnesses;
earlier measurements are diagnostic evidence, not mixed into final medians.

## Historical evidence is not a winner

The historical **0.6116 s / 0.6019 s** five-run whole-file medians remain historical.
They are neither current stage measurements nor evidence of a demonstrated
winner. The preserved four small identities are retained within the larger
measurement set, not offered alone as scale evidence. The current nominal
instances and checked corpus are re-elaborated; absent historical discovery
sources are explicitly not claimed to have been recovered or reproduced.

## Validation commands and protected scope

Run from the repository root. No default-environment `lake test` was used.

```sh
make ff-stage
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
python3 scripts/finite_fields/probe_solver.py --manifest docs/finite-fields/solver-manifest.json --artifact-root .artifacts/finite-fields --profile solving --offline --check
python3 scripts/finite_fields/benchmark.py --config benchmarks/finite-fields/config.json --output benchmarks/finite-fields/results.json
python3 scripts/finite_fields/check_benchmark_results.py --config benchmarks/finite-fields/config.json --results benchmarks/finite-fields/results.json
python3 scripts/finite_fields/check_benchmark_results.py --config benchmarks/finite-fields/config.json --results benchmarks/finite-fields/results.json --self-test
make test-pure
python3 -m py_compile scripts/finite_fields/benchmark.py scripts/finite_fields/check_benchmark_results.py
```

`make ff-stage` passed; subsequent probe executions were offline and passed all
required setup/solving/model capabilities. No proof profile was requested:
the consumed manifest explicitly defers proof export to M2.

Both exact PROJECT gates passed with
`/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting `Z3 version 4.15.2 - 64 bit`.
`check_blaster` completed 246 jobs in 112.22 s; `check_tests` completed the FF
pure discovery, ordinary pure tier and 767-job Z3 tier in 250.53 s. The separate
`make test-pure` invocation also passed. Existing negative fixtures emitted
their existing `sorryAx` and solver lifecycle/model-unavailable warnings;
no warning, expected outcome or check was weakened. The new benchmark proofs
enforce their own transitive axiom allowlist.

Only `benchmark.py` and `check_benchmark_results.py` were added under `scripts/`.
The parent probe and every existing test, script, workflow, Lake and toolchain
file remain unchanged. New Lean harnesses and JSON artifacts live alongside
the benchmark, not in the protected test tree. Generated `.olean` files are
measurement outputs, not committed inputs. This investigation adds no permanent
test module or production optimization.

The native harness exercises the staged cvc5 path directly. Additional
`test-cvc5`, support-floor, all-solvers and `test-cvc5-ff` suites were not run;
they are not substituted for the prescribed PROJECT gates. No production proof
reader/checker/transport, external proof qualification, solver-completeness
claim or maintainer completion signoff is supplied by this ticket.

## Final normalization observations

Seconds; median **[minimum, maximum]** across three measured runs. Every row
below succeeded three times per method; warmups are excluded.

| Identical reflected pair | Ordinary decide | Bounded grind |
| --- | --- | --- |
| F7 square | 0.6099 [0.6052, 0.6130] | 0.6245 [0.6169, 0.6254] |
| F7 constants | 0.6098 [0.5903, 0.6152] | 0.6159 [0.6042, 0.6248] |
| F7 characteristic | 0.6004 [0.5997, 0.6131] | 0.6010 [0.5905, 0.6147] |
| F7 recursive sum | 0.5960 [0.5897, 0.6025] | 0.6208 [0.6168, 0.6351] |
| Curve25519 identity | 0.6047 [0.6000, 0.6127] | 0.6231 [0.6066, 0.6354] |
| Curve25519 implication certificate | 0.6328 [0.6160, 0.6369] | 0.6200 [0.6059, 0.6554] |
| Five-constraint F7 certificate | 0.6267 [0.6257, 0.6314] | 0.6270 [0.6238, 0.6336] |
| Eight-gate Curve25519 certificate | 0.7037 [0.6954, 0.7118] | 0.6330 [0.6289, 0.6361] |
| Historical distribution | 0.6054 [0.5966, 0.6060] | 0.6212 [0.6167, 0.6248] |
| Historical characteristic | 0.6018 [0.5993, 0.6129] | 0.6164 [0.6158, 0.6345] |
| Historical fourth power | 0.6500 [0.6454, 0.6595] | 0.6349 [0.6258, 0.6356] |
| Historical large coefficients | 0.6149 [0.6120, 0.6368] | 0.6207 [0.6170, 0.6486] |

The selected prime is exactly `2^255 - 19`; this is not a similarly sized
substitution. Component medians below are seconds. They are separately rounded
whole-file components and must not be summed as a theorem-only duration.

| Case / method | Elaboration | Kernel type checking | Tactic execution | Imports | Proof nodes | `.olean` bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Curve25519 identity / decide | 0.0847 | 0.00714 | 0.00759 | 0.271 | 272 | 26,128 |
| Curve25519 identity / grind | 0.0865 | 0.00352 | 0.00257 | 0.275 | 41 | 38,352 |
| Curve25519 circuit / decide | 0.0878 | 0.0614 | 0.0470 | 0.270 | 272 | 26,128 |
| Curve25519 circuit / grind | 0.0853 | 0.0152 | 0.00279 | 0.268 | 41 | 46,864 |

Top-level proof nodes can stay constant while kernel reduction cost grows.
Grind can refer to auxiliary declarations; those referenced bodies are outside
the defined node metric. The larger grind `.olean` despite fewer top-level nodes
is a concrete reason not to claim a proof-size winner from either measure alone.

### Failures, fallback and unsupported grammar

| Case | Measured outcome, all three repetitions | Whole-file median |
| --- | --- | ---: |
| False `x = x + 1`, decide | Command failure; certificate cannot be proved | 0.472649 s |
| False `x = x + 1`, grind | Command failure; goal remains unproved | 0.502342 s |
| Composite `Residue 6` zero-product, decide | Command failure; unequal normal forms | 0.483248 s |
| Same composite identity, grind | Semantic identity proved | 0.618298 s |
| Curve25519 certificate, one heartbeat | Explicit heartbeat-limit failure | 0.481167 s |
| Expr inverse/division | Not available in the pinned grammar; no fake runnable substitute | Not measured |

The unchanged parent corpus independently proves the false-goal counterexample
and composite-ring semantic boundary. A failed normal-form equality is not a
general semantic refutation. The successful grind comparison demonstrates an
isolated fallback candidate, **not** a new production fallback dispatcher.

## Final native-pipeline observations

Median seconds across three measured runs. All seven supported cases actually
used qualified native cvc5, including the closed identity and both circuits;
none happened to take the allowed optimizer-only branch. Every transcript and
solver command line is retained in the per-run metric records.

| Case | Whole file | Optimization | Translation | Submission | Solve + model |
| --- | ---: | ---: | ---: | ---: | ---: |
| F7 square | 2.664827 | 0.020 | 0.205 | 0.023 | 0.017 |
| F7 false goal | 2.622737 | 0.020 | 0.137 | 0.025 | 0.040 |
| Curve25519 identity | 2.739410 | 0.020 | 0.279 | 0.023 | 0.013 |
| Five-constraint F7 circuit | 2.727944 | 0.021 | 0.240 | 0.024 | 0.013 |
| Eight-gate Curve25519 circuit | 3.139485 | 0.024 | 0.553 | 0.026 | 0.015 |
| New proved-instance F7 self-division probe | 2.639442 | 0.020 | 0.178 | 0.025 | 0.014 |
| Unsupported representation/order probe | 1.730303 | Unavailable: rejected before end trace | Not reached | Not reached | Not reached |
| Closed F7 wraparound | 2.572844 | 0.019 | 0.113 | 0.024 | 0.013 |

The false-goal run returned `sat`, requested values and displayed
`x: (0 : Blaster.FiniteField.Residue 7) [#f0m7]`. Its Solve time includes model
extraction; no solver-only or separate rendering time is inferred. The other
supported runs returned `unsat`. The unsupported probe was rejected before
query assertion or `check-sat`. New self-division and representation probes are
explicit analogues, not recovery of missing historical source artifacts.

Native harness exclusive elaboration medians were 0.306–0.320 s; kernel
type-checking medians were 0.00466–0.00488 s. **That kernel work checks harness
source/evidence declarations, not a cvc5 proof.** Production proof reading,
checking and final verified transport remain unavailable, as in the stage table.
Whole-file native time includes compilation/interpreted harness work, imports,
qualification, logging and teardown outside the four production trace scopes.
Do not report the table's whole-file values as solver time.

## Parent corpus and isolated checked fixture

All four unchanged Lean module invocations passed all repetitions: historical
ordinary-decide module median 0.622317 s; historical corpus/boundary module
0.578410 s; Semantic module 1.002720 s; Circuits module 1.128462 s. Their shared
module commands check every entry assigned to them, not just one theorem.

All twelve parent SMT inputs also passed their declared outcomes:

| Parent input | Solver status | Whole-process median |
| --- | --- | ---: |
| F3 no-root | unsat | 0.017426 s |
| F3 no-root with field hint | unsat | 0.017175 s |
| F7 no-root | unsat | 0.016906 s |
| F7 no-root with field hint | unsat | 0.017284 s |
| F7 zero product | unsat | 0.017286 s |
| F7 zero product with witness | unsat | 0.005279 s |
| F7 square implies nonzero | unsat | 0.015394 s |
| Modulus 394357 linear | unsat | 0.016245 s |
| F3 enumeration | unsat | 0.017771 s |
| F7 false goal | sat | 0.017363 s |
| F2 guarded Fermat-zero | unsat | 0.014520 s |
| F2 unguarded Fermat-zero | sat | 0.015411 s |

These process times are strongly affected by launch/observation granularity.
In particular, the witness median is not evidence that adding a witness speeds
up solving. No hint/no-hint or solver-completeness conclusion follows.

The unchanged `Tests/FiniteField/Prototype.lean` isolated fixed-text fixture was
re-elaborated, including its original-goal proof and five negative checks.
Median whole-file time was **0.724469 s**; exclusive elaboration **0.117 s**,
kernel type checking **0.0148 s**, tactic execution **0.0176 s**, imports
**0.266 s**. Parsing, individual replay checks and fixed-fixture transport are
not separately instrumented. No live proof acquisition or production proof
reconstruction was performed.

## M2 handoff and evidence-limited next questions

- **Supported measured subset:** all runnable parent fixtures; 12 paired
  polynomial identities including the two synthetic circuits and exact selected
  prime; semantic rejection/fallback boundaries; qualified native polynomial,
  model and inverse-graph paths; explicit representation rejection; isolated
  historical checked replay.
- **Variability:** three measured repetitions, one warmup, fixed method order,
  shared virtualized worker, two CPU-equivalents and warm imports. Many
  decide/grind ranges overlap; differences change direction across identities.
  The eight-gate case has lower grind whole-file and kernel times in this sample,
  but neither it nor the historical four identities demonstrates general
  performance superiority or realistic cryptographic scaling.
- **Measurement-led questions, not implemented optimizations:** the selected
  circuit's decide kernel component (61.4 ms versus 7.14 ms for its small
  identity) motivates investigating checked normal-form reduction cost.
  Native circuit translation (553 ms) exceeds its composite Solve median
  (15 ms), motivating finer translation/qualification attribution before
  solver tuning. Large import/harness costs motivate an isolated in-process
  measurement design, not an inference that solver work dominates.
- **Still unavailable:** original Nethermind/cyclic-5 and other catalogue-only
  sources, automatic checked reification, full rule audit, proof acquisition,
  production proof reading/checking/transport, proof-profile qualification,
  ideal/variety/root-completeness reconstruction and multi-platform results.
  The consumed solving manifest's 1.4.1 versus older 1.3.4 decision discrepancy
  remains inherited and explicit; no pin was silently changed.
- Any implementation optimization, optional pre-solver grind or altered
  production rewrite family requires explicit FFM-22 scope. M2 design and
  completion signoff remain with Riley. Rerun this configuration after changing
  any pinned corpus, toolchain, solver, harness or schema input.

The final fully profiled benchmark plus checker/self-test command exited 0 in
182.44 s. The checker confirmed **54 cases / 216 runs** and rejected all 15
mutations: missing/duplicate runs, zero/nonfinite durations, invented success,
config/corpus mismatch, missing probe, interruption, changed summary, false
verified transport, changed limits, missing circuit class/source pin/tool.
The earlier 54-case pass before enabling native component profiling is retained
as calibration summary evidence only; its observations are not mixed into the
final statistics.
