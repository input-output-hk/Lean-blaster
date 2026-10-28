# FF-04: reconstruction architecture and checked prototype

## Settled decision and FFM-08 scope

Retain the **local nominal modular-ring layer, selective checked polynomial
normalizer port, and untrusted textual CPC reader producing kernel-checked Lean
proofs**. This ticket reproduces that experiment on the selected Lean 4.24.0
base; it does not reopen the architecture decision, promote a public field API,
or implement the production normalizer-first dispatcher.

The frozen public source is lean-blaster
[`724e32c377b5c6bfdecaf200984203b21c75355b`](https://github.com/input-output-hk/lean-blaster/tree/724e32c377b5c6bfdecaf200984203b21c75355b/Blaster/FF04).
Its [architecture report](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/docs/finite-fields/ff-04-reconstruction.md)
contains the historical candidate comparison, live solver smoke and measurements.
Those are historical evidence, not commands rerun or solver qualification claimed
by FFM-08. The applicable parent contracts are
[FFM-01](m1-execution-decision.md) and [FFM-02](m1-toolchain-decision.md).

The selected local port remains Mathlib-free. The original polynomial algorithm
came from lean-smt
[`9b314968f6405395ecbc030c4d3f9b35e4974aa1`](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/Smt/Reconstruct/ZMod/Polynorm.lean).
The FF-04 source already replaces its Mathlib coefficient algebra with core
`Lean.Grind.CommRing` and adapts proofs to Lean 4.24.0. Its authorship and Apache
license header are preserved. No upstream package, Qq reifier, native normalizer,
lean-cvc5 FFI or Logos backend is added. Logos remains a parser/Boolean design
reference; a nominal-to-Mathlib bridge remains a separate optional package, not
a core dependency.

## Exact compatibility edits

- `Tests/FF04/Nominal.lean`, `Polynorm.lean`, `Corpus.lean` and `Replay.lean`
  retain the pinned source without algebra, algorithm, proof or parser changes.
  No Lean API compatibility fix was necessary: the source already targets the
  selected toolchain. The nominal type, normalizer and replay stay under
  `Blaster.FF04`; the inherited corpus namespace `Test.FiniteFieldPolynorm` is
  also retained rather than renamed.
- `TestsSolver/FiniteFieldPrototype.lean` becomes
  `Tests/FiniteField/Prototype.lean`;
  `TestsSolver/FiniteFieldPolynormDecide.lean` becomes
  `Tests/FiniteField/PolynormDecide.lean`; and
  `TestsSolver/FiniteFieldPolynormGrind.lean` becomes
  `Tests/FiniteField/PolynormGrind.lean`. Each prepends `import Tests.Pure`;
  the remaining source, including the fixed trace and rejection tests, is
  retained.
- `Blaster.lean` imports `Blaster.FF04.Corpus` and `Blaster.FF04.Replay`, making
  all four modules reachable by the existing clean library coverage check.
- `Tests/FixedIssues.lean` receives exactly three end-appended individual imports
  for the new test modules. This reaches them through the existing backend/Z3
  aggregate without changing any previous imports. `Tests.Pure` is unchanged;
  its existing Make target does not itself discover these new files, so FFM-08
  also executes each file directly.
- No toolchain, dependency declaration, manifest, solver pin, check script,
  Makefile, CI configuration, production translator/optimizer/tactic or
  `blasterProven` implementation changes.

## Nominal ring and ordinary checked normalization

`Residue p` is a structure wrapping `Fin p`, not an abbreviation. Its modular
operations and core commutative-ring/characteristic instances require
`[NeZero p]`. It supplies neither `Inv` nor `Div`; truncating `Fin.div` is not
field division. Ring identities need no primality assumption. This is not a
field API, and a production field instance must separately require checked
primality evidence.

The normalizer retains sorted monomial insertion/merge, fold-based multiplication
and repeated powers. `Expr.eval_toPolynomial` proves semantic preservation;
`Expr.denote_eq_from_toPolynomial_eq` transports a kernel-checked equality of
normal forms to equality of the original reflected expressions. The decide
comparison applies that theorem followed by ordinary `decide`, not
`native_decide`, `nativeEqTrue` or a solver-result axiom.

The shared corpus covers distribution, characteristic cancellation, a fourth
power expansion and a quadratic product with large coefficients, all over
`Residue 65537`. It also retains `rejectsFalseCertificate` for `x = x + 1` and
`acceptsTrueCertificate`. The composite-ring limitation is deliberately unchanged:
over `Residue 6`, `(2*x)*(3*x)` leaves a zero-coefficient monomial rather than the
empty polynomial. `zeroProductNotCanonical` proves the representation inequality;
`zeroProductSemanticallyZero` proves the actual identity with grind. Failure to
normalize to the same representation is failure to certify, not evidence of a
false identity. No completeness claim or algorithm repair is part of this port.

## Original-goal replay boundary

The embedded fixed text is independent of any locally installed solver. The
pinned source records it as cvc5 1.4.1 CPC output with explicit conclusions for
`x = 2` and the negation of `x*x = 4` over modulus 7. FFM-08 neither discovers a
solver nor regenerates this certificate. Its `TRUST_THEORY_REWRITE` warning and
trust-labelled identity are retained as input, not adopted as proof authority.

`Replay.lean` preserves all five checks:

1. Each declaration resolves by name to an original Lean local of exactly the
   nominal type and numeric modulus. Mixed/mismatched moduli fail.
2. Aliases and literals become typed Lean expressions; unknown identifiers,
   mismatched literal moduli and unsupported syntax fail.
3. Each assumption must match an original Lean hypothesis or the negated
   original goal. Parsing cannot create a new assumption.
4. Every step is reproved as a closed implication over the declared variables
   and exactly its referenced premises, using `withLCtx {} {}` and
   `intros; grind (ematch := 0)`. An unrelated original `False` cannot leak into
   a premise-free step. Labels, including `trust`, and `:args` carry no authority.
5. The final proof must have type `False`; classical contradiction discharges the
   negated original goal. Failed proof search and unsupported inputs are errors,
   never skipped obligations or admissions.

The fixture checks all 13 step conclusions and proves
`originalGoal (x : Residue 7) (h : x = 2) : x * x = 4`. The preserved negative
cases reject changed assumptions, a false trust-labelled identity, a wrong
modulus, an unknown premise reference and leakage of an unrelated `False`.
The executable `Lean.collectAxioms` guard traverses the theorem's dependencies
and rejects every axiom outside `propext`, `Classical.choice` and `Quot.sound`.
This includes rejection of project trust, admission and native-decision axioms;
merely printing axioms is not the acceptance check.

## Retained identity-checking policy and production gaps

The settled design selects ordinary normalization plus its semantic theorem as
the default identity checker, with one bounded grind fallback in the supported
ring fragment using only referenced premises. Retain the initial default
200,000-heartbeat command ceiling and no unrelated E-matching (`ematch := 0`);
no automatic budget escalation or admission fallback is authorized. This is an
architecture policy, not an implemented production dispatcher or a calibrated
performance guarantee. **The replay experiment itself uses grind for every
step**, not the normalizer-first policy.

Remaining limitations:

- No production proof transport through optimizer rewrites to the original
  goal, ProofStep infrastructure, verified closure, proof acquisition or new
  public field API is supplied. The fixed original-goal fixture is not such a
  general bridge. `blasterProven` is unchanged and excluded from its proof.
- No general FF-rule checker, ideal/variety reasoning, primality certificate,
  division/inversion, symbolic modulus or extension-field support.
- No automatic reifier: the corpus supplies explicit reflected expressions.
  No production normalizer-first dispatch or integration with solver output.
- The narrow reader accepts one wrapped proof (optionally prefixed by `unsat`),
  comments, aliases, explicit conclusions, one numeric modulus, binary add/mul,
  negation, equality/not and the demonstrated labels. It is not a general CPC
  grammar, omitted-conclusion engine or rule-shape auditor. Quoted symbols,
  scoped subproofs, arbitrary n-ary operations, include files and multiple proof
  responses remain unsupported.
- No production parser resource limits, certificate service hardening, broad
  rule coverage, protocol negotiation or general diagnostics are introduced.
- The inherited zero-coefficient representation limitation remains visible.
  The tiny corpus cannot establish realistic scaling or a speed winner.
- No original lean-smt/lean-cvc5/Logos package build, Mathlib bridge, new protocol
  probe, live proof production or external checker is run for this port.
  Those are not prerequisites for the embedded solver-independent experiment.

The [FFM-08 ticket report](ffm-08-ticket-report.md) records the exact local
validation commands, measured reproduction, outcomes and unrun checks. Historical
FF-04 timings and solver smoke are not substituted for this port's validation.

## Measured FFM-08 reproduction

Observed on 2026-10-27: Lake `5.0.0-src+797c613`, Lean `4.24.0`, release
`aarch64-unknown-linux-gnu`, compiler commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. The local manifest has no packages.
`lake build Blaster` passed (183 jobs, 90.19 s), and `make test-pure` passed
(212 jobs, 26.89 s), preparing the imported modules. No upstream package was
built.

The following commands each passed once directly, then once in a sequential
timed reproduction with no concurrent build/check workload:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Prototype.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/PolynormDecide.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/PolynormGrind.lean
```

| File | Timed exit | Whole-process elapsed | Observed proof dependencies |
| --- | --- | --- | --- |
| `Prototype.lean` | 0 | 0.7093 s | `originalGoal`: `propext`, `Classical.choice`, `Quot.sound`; executable transitive allowlist and all five negative cases pass |
| `PolynormDecide.lean` | 0 | 0.5823 s | All four theorems: `propext`, `Quot.sound` |
| `PolynormGrind.lean` | 0 | 0.5981 s | All four theorems: `propext`, `Classical.choice`, `Quot.sound` |

Python `time.perf_counter` measured each complete subprocess, including Lake,
imports, elaboration, kernel checking and axiom output. These are single warm
reproduction measurements, not the historical five-run profiler experiment,
isolated tactic timings, an optimization before/after comparison or evidence of
a speed winner. Direct Lean execution runs the replay elaborator and its negative
tests, and checks the ordinary normalization proofs; it does not merely load
previously compiled test theorems.

The library build also checked the shared corpus's false-certificate rejection,
true-certificate acceptance and both composite-ring examples. The generic
soundness theorem, representation checks and certificate booleans report only
`propext` and `Quot.sound`; `zeroProductSemanticallyZero` additionally uses
`Classical.choice`. No expected result or inherited algorithm was changed.

### Project gates and reproduction risk

Both mandatory PROJECT checks passed with the prescribed Z3 4.15.2-only solver
PATH:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

The clean build passed in 91.94 s (183 jobs). The final test gate passed in
196.68 s (212 pure-tier and 668 Z3-tier jobs), including all three new modules.
Both commands selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, version 4.15.2.

Two earlier test-gate runs failed in the unchanged `Tests.Smt.CrashLifecycle`
module during the Z3 tier. The retained second-run diagnostic was
`Tests/Smt/CrashLifecycle.lean:608:0: malformed response was not classified as protocol failure`.
Isolated execution of that module and an exact-gate diagnostic run on the
immutable starting snapshot both passed; the final port gate then passed without
any code or configuration changes. The 50 ms fake-solver race is a suspected
scheduling sensitivity, not a fixed or conclusively diagnosed defect. The
[ticket report](ffm-08-ticket-report.md#earlier-gate-failures-and-diagnostic-runs)
retains every attempt, command and outcome; the successful retry does not hide
this reproducibility risk.

No required local validation command remains unrun. Additional cvc5,
support-floor, all-solvers and native-FF lanes, remote CI and live proof
production were not exercised. No production proof transport or new solver
capability is inferred from the local passing checks.
