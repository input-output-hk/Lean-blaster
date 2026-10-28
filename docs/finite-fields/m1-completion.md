# M1 integrated interface and trust-boundary handoff

## Scope

FFM-21 adds integrated regressions and the [public usage guide](native-support.md).
It does not implement a new solver, optimizer rule or proof reconstruction path.
The [ticket report](ffm-21-ticket-report.md) records this job's exact validation
commands, worker results and head-specific PR #412 CI evidence. Completion
signoff, the aggregate draft PR's readiness and merging remain with Riley.

Local validation passed: both exact Z3 4.15.2 PROJECT gates; clean library
coverage with cvc5 selected; dynamic pure coverage **18/18**; standalone ordinary
cvc5 baseline; direct deterministic outcome execution; strict ordinary cvc5
1.4.1; detached all-solvers (**800 jobs**, exit 0, no hang); complete dedicated FF
coverage, including **2 SAT / 1 UNSAT** new integrated live cases; and executable
guide examples with both public import surfaces. The committed measurement
checker and its 15 corruption-rejection scenarios also passed. The report
records the corrected initial parser error in the new integration test, rather
than presenting every development attempt as green.

Latest completed PR #412 ordinary/floor and dedicated arm64/x86_64 CI evidence
passed on `f726b4f7faecc625e83cfea7bd25a8f6e30fbe4a`. That is not validation of
this ticket's eventual publication head, and the ordinary CI run still uses
1.3.4 until the maintainer's documented transition.

The current public carrier is `Blaster.FiniteField.Residue p`, exported by
`import Blaster` and the algebra-only `import Blaster.FiniteField`. Ring
operations require a nonzero modulus; field operations and native SMT admission
require checked `PrimeModulus p` evidence. Native admission additionally requires
a concrete closed modulus and the supported residual fragment. A prime-field
SMT sort is not a primality proof.

## Implemented production stages

The implementation is [Translate.main](../../Blaster/Smt/Translate.lean), with
[preflight](../../Blaster/Smt/FiniteFieldPreflight.lean),
[polynomial/division translation](../../Blaster/Smt/Translate/FiniteField.lean)
and [optional model decoding](../../Blaster/Smt/FiniteFieldModel.lean).

1. Validate solver options and establish the session-owner boundary. Concurrent
   ordinary modes start their required sessions before optimization.
2. Elaborate/check the input proposition and optimize it. An optimizer-decided
   result need not reach an SMT backend; this is not evidence of native FF solving.
3. Inspect the residual nominal fields, checking each exact modulus's proof
   input. Resolve explicit/environment/default backend selection without silently
   switching Z3 to cvc5. Native FF requires single cvc5 mode; `first`/`agree`
   reject and retire their sessions before native theory broadcast.
4. Qualify the selected cvc5 executable against the finite-field protocol.
   An explicit cvc5 SMT-LIB-only run translates without discovering a binary.
5. Translate supported field polynomials and total inverse/division graphs.
   Each modulus retains its own sort. Inverse witnesses and their constraints
   belong to the same query epoch; zero inverse and division by zero are zero.
6. Submit the negation of the translated goal (including the division encoding's
   witness scoping), then read `check-sat`: `unsat` is `Valid`, `sat` is
   `Falsified`, and `unknown` is `Undetermined`. Transport/protocol failures
   remain errors, not successful verdicts.
7. Optionally request and decode counterexample values. Missing, malformed or
   mismatched evidence must not reverse a decisive SAT verdict. Values are
   diagnostic display, not a Lean proof of a counterexample.
8. Retain the current query's diagnostics and retire owned sessions, including
   exceptional exits. No model/variable/witness state may leak across queries.

## Exactly what remains trusted

**Native M1 solving is not verified or reconstructed proof production.** The
[tactic implementation](../../Blaster/Command/Tactic.lean) still closes a `Valid`
goal with the existing unrestricted `Blaster.Tactic.blasterProven` axiom. It emits
`declaration uses 'blasterProven' (SMT-verified, no proof term)` when the normal
warning is enabled. The warning's historical “SMT-verified” wording does not mean
kernel-checked reconstruction. This ticket neither changes nor widens that axiom
and does not suppress its warning.

Accepting native results therefore still trusts the optimizer, reification and
translation, modulus/sort/witness correspondence, assertion polarity, solver
implementation and executable, protocol/result handling, and the connection to
the original goal. Checked algebra, primality and inverse-graph theorems establish
local mathematical facts; they do not constitute a checked proof of every
production translation or final result. `#blaster` reports a verdict rather than
creating a theorem. A displayed SAT model is optional untrusted evidence.

The isolated historical FF-04 fixed-text replay and the reflected polynomial
normalizer are separate checked experiments. They do not turn the native pipeline
into a production proof reader, general rule checker or verified dispatcher.

## Consumed audit, corpus and resource evidence

- [Rule-audit bookmark](m1-rule-audit.md): source-linked deferred-M2 questions,
  **not a completed rule audit**. It carries the scaling/cancellation obligations
  for `FF_POLY_NORM_EQ`, disequality witness semantics, root-list completeness,
  ideal/variety certificates and finite-domain exhaustion obligations.
- [Corpus](benchmark-corpus.json) and [FFM-19 report](ffm-19-ticket-report.md):
  26 runnable entries, with 24 other entries still catalogue-only. Missing
  original sources are not replaced by invented provenance. Synthetic F7 and
  Curve25519 circuits are bounded examples, not production cryptographic scale.
- [Measurement report](m1-measurements.md),
  [configuration](../../benchmarks/finite-fields/config.json) and
  [raw results](../../benchmarks/finite-fields/results.json): 54 cases / 216 runs,
  comprising 54 warmups and 162 measured repetitions. The measured results
  contain 150 successful harness/corpus checks, nine intentional command
  failures and three intentional heartbeat-limit failures. These are not 150
  reconstructed native proofs.
- This job reran the committed result checker and all 15 evidence-corruption
  rejection scenarios successfully; it did **not** rerun or relabel the parent's
  benchmark measurements. Configuration SHA-256:
  `733b1dc15325519aa53dea2fb0f32a957b4afdc1a7fce2a1a8f2bfa81294b83a`;
  corpus SHA-256:
  `62dc069a61c5f5d7fe2af100f547d709eccac16e14c9156515d0f2767f98a3cf`.

The retained production traces measure optimization, translation, submission and
composite solve/model handling. They do not separately measure solver-only time,
model rendering or exclusive capability qualification. Whole-file measurements
also include imports, elaboration, qualification and teardown. The parent reports
maximum measured wait4 memory of 1,256,496 KiB and sampled aggregate RSS of
2,002,264,064 bytes on its two-CPU-equivalent, 8 GiB worker; these are distinct
metrics, not current-job measurements or a scalability guarantee.

**Production proof reading, production proof checking and final verified
transport are absent.** The committed JSON records each as `not_available` with
null seconds. Harness kernel-checking time is not solver-proof checking time.

## Pins and lane ownership

The operative [solving manifest](solver-manifest.json), introduced by FFM-09,
pins cvc5 **1.4.1**, source `2b2e84419f70817ec919a784a48806e79f677240`, GPL/CoCoA,
with `ff-field-polys=false` and `ff-solver=gb`. Older decision/audit text mentioning
1.3.4 is historical; it does not override this manifest. Proof export is deferred.

| Platform | Archive SHA-256 | Executable SHA-256 |
| --- | --- | --- |
| Linux arm64 | `e6cac10f5b80177b21ef56660ea580120fb8b614ceacc8ba8907c0fcfd9a1e7c` | `b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86` |
| Linux x86_64 | `d0b54324ec2129697975da8753767fd255309947b87832917d32a78da7d16666` | `b265759b80da81b51df0eac26f6289630860617ed7cdce86f93352e4ce84e59f` |

The worker uses Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`),
release Z3 4.15.2 for the PROJECT gates, and its installed cvc5 1.4.1 GPL/CoCoA
for ordinary cvc5/concurrent checks. Dedicated FF tests use the separately staged,
hash-verified executable, not PATH selection. `make ff-stage` is the only solver
acquisition step; subsequent FF checks are offline.

Ordinary CI is independent of the staged profile and must remain usable without
CoCoA. The support-floor lane owns cvc5 1.2.1. The protected checkout's ordinary
CI pin is still 1.3.4; Riley moves it to 1.4.1 after M1. This ticket does not edit
that workflow or provision another solver. The report distinguishes completed CI
on its exact head from pending evidence on this ticket's eventual head. CI is
evidence, not a worker completion gate.

## Unfinished work and limitations

- **M2 proof infrastructure:** checked automatic reification; premise/context and
  variable correspondence; proof acquisition/reading; semantic rule checking;
  ideal membership, root completeness and finite-domain reasoning; final checked
  transport through optimization to the original Lean goal.
- **Deferred proof-producing solver profile and full rule audit:** qualification,
  distribution/platform provenance and proof-format decisions remain unresolved.
  The audit bookmark's fork identity and source/binary discrepancy are not a
  qualified M1 proof dependency. No proof profile is staged by this ticket.
- **FF optimizer rewrites:** deferred; no new rewrite family or optional
  pre-solver strategy is implemented or implied by the measurements.
- Symbolic moduli, extension fields, representation-dependent operations,
  unsupported residual quantification/higher-order terms and mixed unsupported
  theories are not made native-capable by this integration work. See the guide's
  diagnostic/remediation table rather than weakening admission checks.
- Benchmark conclusions are bounded to the recorded corpus, repetitions and
  hardware. Catalogue-only source gaps, finite-domain completeness and realistic
  cryptographic scaling remain unresolved.
- Final public API confirmation and completion signoff remain maintainer decisions;
  this handoff does not mark PR #412 ready, merge it or authorize upstream outreach.
