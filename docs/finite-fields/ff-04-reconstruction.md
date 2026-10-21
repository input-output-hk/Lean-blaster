# FF-04: reconstruction architecture and checked prototype

## Decision and scope

Select a **local nominal modular-ring layer and a selective port of the checked
lean-smt polynomial normalizer**, with an untrusted textual CPC reader producing
kernel-checked Lean proofs. Keep the public finite-field type nominal. Do not
adopt lean-smt's whole native stack or Logos's whole calculus as a dependency.
Logos remains a useful parser/Boolean design reference, not an integrated backend.

This is an isolated checked architecture experiment, not FF-05, a production
field API, or a new `blaster` mode. The modules are under `Blaster/FF04/`, imported
by the library root so the existing clean-compilation gate builds every module.
The translator, optimizer, production tactic and `blasterProven` boundary are
unchanged; only the explicitly invoked `ff04_replay` experiment is registered.
FF-25 owns grind-before-solver policy; this decision concerns checking certificate
identities **after** solver output, not tactic ordering.

The supplied synthetic root was `33a3212f8eade9bb1636c80e1f73ab6c64694b25`.
Fetching only the approved public head
`075fc92393730e05957ab6cc3064b41004663099` established identical trees:
`105337770ef1e3991d2eff27b3183a597d52a19e`; the tree diff was empty. No history
rewrite, merge, other project checkout or publication was performed. FF-01 code
and `ff-01-integration.md` remain unchanged. The coordinator retains remote-head
recheck, publication and signoff for draft PR #367; this report is not Kanban
completion.

## Candidate comparison

All external sources below are frozen public, read-only inputs. Versions are
observed declarations, not claims that these upstream packages were built here.

| Candidate | Lean / Mathlib | FFI and dependency cost | Integration and maintenance decision |
| --- | --- | --- | --- |
| Local nominal port | Project Lean 4.24.0; no Mathlib | Existing empty Lake package list; core `Lean` only for the prototype; executable cvc5 text output, no new FFI | Chosen. Own the nominal instances, selective algebra-lemma port, interpretation and original-goal bridge. Maintain a small supported certificate fragment rather than the whole upstream reconstructor. |
| lean-smt through a proved nominal-to-`ZMod` bridge | Lean 4.32.0; Mathlib v4.32.0, manifest revision `81a5d257c8e410db227a6665ed08f64fea08e997` | 11 manifest packages, including lean-auto, lean-cvc5, Mathlib, Qq, batteries, aesop, proofwidgets, importGraph, LeanSearchClient, plausible and Cli. The pinned lean-cvc5 adds C++ FFI and custom native cvc5 artifacts. | Not directly compatible with project pins. A bridge must prove injectivity and preservation of numerals, add/mul/neg/sub/powers, then transport assumptions and the result back. Merely unfolding the nominal type or obtaining a `ZMod` theorem is insufficient. This route could reuse ideal/variety lemmas but imports a much larger maintenance surface. No bridge or upstream build is claimed here. |
| Logos parser / Boolean machinery | Lean 4.34.0; no Mathlib or external Lake packages | No solver FFI in its Lake declaration; generated CPC programs/tables and their proofs. Regeneration uses `ethos-eoc`. | Reuse the separation between syntax, signature tables and semantic proofs, not the package wholesale. Backporting newer Lean APIs and bridging Logos models to original Lean propositions remain work. No finite-field implementation was located in the inspected pinned parser/calculus/model/signature. |

Sources:

- lean-smt [toolchain](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lean-toolchain),
  [lakefile](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lakefile.lean),
  [manifest](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lake-manifest.json).
- lean-cvc5 [toolchain](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lean-toolchain),
  [lakefile](https://github.com/abdoo8080/lean-cvc5/blob/4733baf0722c870a5a449f132afa690947e00e2a/lakefile.lean).
  Its empty Lake manifest does not remove native dependencies: the lakefile
  downloads `psaccomani15/cvc5` release `clean-wip`, generates enums from headers,
  compiles C++17 and links cvc5/parser, CoCoA, CaDiCaL, GMP/GMPXX and
  picpoly/picpolyxx. The release tag is not an immutable native checksum. That
  artifact was not downloaded; the installed solver is not claimed equivalent.
- Logos [toolchain](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/lean-toolchain),
  [lakefile](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/lakefile.toml),
  [README](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/README.md).
  Its README's more-than-two-hour full development build and representative-rule
  CI warning are upstream documentation, not local timings.

### Reconstructor and parser boundaries

The pinned [lean-smt reconstructor](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/Smt/Reconstruct/ZMod.lean)
uses `ZMod`, multivariate polynomials, ideals, Nullstellensatz and finite-field
lemmas; its variety interface explicitly requires `[Fact n.Prime]`. A nominal
bridge must preserve that checked field assumption, not replace it with nonzero
modulus. Those dependencies are not needed to prove the small ring identities in
this experiment. Its generic
[reconstruction code](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/Smt/Reconstruct.lean)
returns skipped obligations for unsupported steps; that is distinct from its
separate `trust` configuration, which admits goals. The local path does neither:
a failed step fails reconstruction. No skipped obligations become success.

The [existing normalizer](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/Smt/Reconstruct/ZMod/Polynorm.lean)
contains two different trust paths: ordinary `polyNorm` uses
`of_decide_eq_true (Eq.refl true)`, while `nativePolyNorm` uses
`Meta.nativeEqTrue`. Only the former kernel-evaluation boundary is retained.
The port preserves the list/sorted-monomial insertion, fold and repeated-power
algorithm and its semantic proofs, generalized from `ZMod` to core
`Lean.Grind.CommRing`; it does not substitute a different algorithm and call it
an upstream measurement. The Qq reifier and native path are not ported.

Logos's [parser documentation](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/docs/parser.md)
and [parser implementation](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/Logos/Parser.lean)
separate a command reader from signature-specific operations. Its normal input
is a bare command sequence, not the outer `get-proof` wrapper and `unsat` status.
It supports optional conclusions and scoped proof references. Its parser is
outside its verification theorem, and ignored `include`/`reference` commands do
not authenticate assumptions against an original problem. Actual checked
Boolean rules exist, including
[Contra](https://github.com/cvc5/logos/blob/4cd3a10e302a9f794f29eac5f0abd6a9a885242e/Cpc/Proofs/Rules/Contra.lean)
and resolution rules. Reusing those still requires a semantic bridge; an external
Logos exit status alone cannot prove a Lean goal.

## Complete checked prototype

`Nominal.lean` defines `Blaster.FF04.Residue p` as a structure containing `Fin p`,
not an abbreviation, and proves core commutative-ring and characteristic-p
instances for `[NeZero p]`. No `Div` or `Inv` instance exists. The representation
uses modular arithmetic only; truncating `Fin.div` is never field division.

`Replay.lean` parses a narrow S-expression/CPC fragment with explicit step
conclusions. No external checker is invoked by the tactic. The proof boundary is:

1. Each `declare-const` resolves to an original Lean local with exactly the
   nominal type and numeric modulus. Different moduli are rejected.
2. Each term alias is interpreted as a typed Lean expression. Numerals carry
   matching moduli; unknown names and unsupported forms fail.
3. Each parsed `assume` is discharged by an existing original Lean hypothesis
   or the negated original goal. The parser cannot introduce a new assumption.
4. Each step is proved as a **closed** theorem universally quantified over the
   declared variables and implying its explicit conclusion from exactly its
   referenced premises. Proof search runs with an empty local context; unrelated
   hypotheses, including `False`, cannot justify a premise-free step.
5. The final step must prove `False`. Lean's classical contradiction theorem
   then discharges the negated goal, producing the original goal's proof.

Rule labels and `:args` are not trusted semantics. The accepted labels identify
this experiment's slice; every conclusion must be independently reproved from
its named premises. In particular a solver `trust` step is not an admission.
This is a semantic rechecker for explicit conclusions, not an implementation of
all CPC rule-shape checks or omitted-conclusion inference.

The actual command used to produce the fixture was
`cvc5 --lang=smt2 --proof-format-mode=cpc --proof-print-conclusion` with stdin:

```smt2
(set-logic QF_FF)
(set-option :produce-proofs true)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f2m7))
(assert (not (= (ff.mul x x) #f4m7)))
(check-sat)
(get-proof)
```

Observed exit 0, `unsat`, no stderr. The complete returned CPC trace is embedded
in `TestsSolver/FiniteFieldPrototype.lean`. It includes a
`TRUST_THEORY_REWRITE` warning and a `trust`-labelled `2 * 2 = 4` step. Lean
reproves that step without premises. All 13 step conclusions are checked, and
`originalGoal (x : Residue 7) (h : x = 2) : x * x = 4` compiles.
`#print axioms originalGoal` reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

An executable transitive-axiom allowlist also guards that theorem. Regressions
reject an altered assumption, a false trust-labelled identity, a modulus mismatch,
an unknown premise, and leakage of an unrelated original `False` hypothesis.
These check the parser-to-goal and proof-isolation boundary, not merely an exit
status or the presence of some generated proof text.

## API, primality and trust policy

- Preserve the own-type decision: the future public field type must remain
  nominal, with modulus-dependent operator keys. FF-01's numeric modulus cache
  is not a primality certificate and must not be treated as one.
- This experiment supplies a modular **ring**, not a field. `[NeZero p]` is enough
  for its representation and ring laws; its polynomial proofs do not assume
  primality. The replay slice requires a numeric modulus at least two but does
  not purport to certify primality or field completeness.
- A production field constructor/instance must require a kernel-checked proof of
  primality. If Mathlib is absent, select and prove an appropriate core primality
  API/certificate separately. A solver declaration, native Boolean primality
  test or cached Nat does not meet that contract. Composite ring examples in the
  normalizer tests are deliberately not advertised as field reasoning.
- Numerals, `+`, `*`, unary `-`, subtraction and natural powers form the proposed
  public polynomial fragment; equalities/disequalities compose propositionally.
  No inversion/division, symbolic moduli, extension fields, roots, GCD,
  finite-field splitting or radical/ideal reasoning is promised by this prototype.
- **No interim trusted mode is introduced or required for this decision.** The
  production base still has its existing `blasterProven` behavior, unchanged.
  That path is not the verified FF path. A future separately approved trusted
  mode, if desired, must be explicitly named and distinct; this work adds no
  project trust axiom and does not widen `blasterProven`.
- The verified path excludes `blasterProven`, `sorryAx`, additional project trust
  axioms and native-decision trust. Lean's foundational `propext`,
  `Classical.choice` and `Quot.sound` are allowed and reported, not concealed.

## Production gaps and inaccessible inputs

The full September 30 discovery-plan document and separate completed static-audit
artifact were not present in the supplied tree; scoped searches located only
FF-01, the Fin baseline and pass reports. The ticket and frozen public sources
were accessible. No contents or conclusions are attributed to missing documents.
No new toolchain, Mathlib dependency or custom native artifact was authorized or
installed. Consequently no original lean-smt/lean-cvc5/Logos package build or
original `ZMod` benchmark is claimed. Such execution needs a scoped prerequisite
approval if required beyond the measured local adaptation.

Remaining production work is explicit, not a silent broadening of this prototype:

- Production nominal API, primality evidence, indexed sort/operator translation,
  and a proof-producing bridge through every optimizer rewrite to the original
  goal. FF-01's existing interfaces are preserved, not replaced.
- General atom reification and polynomial-certificate integration; the benchmark
  supplies explicit reflected expressions, whereas the CPC slice rechecks small
  step implications with grind. The selected default identity checker is not yet
  wired into a production reconstructor.
- General CPC grammar, omitted conclusions, scoped subproofs, Boolean coverage,
  finite-field-specific rules and version/capability negotiation. This parser
  accepts one wrapped proof, comments, aliases, one numeric modulus, binary
  add/mul, negation, equality/not and the demonstrated rule labels. No quoted
  symbols, arbitrary n-ary operators, multiple proof responses or include files.
- Production certificate input/resource limits and diagnostics. The prototype
  uses Lean's bounded proof search, not an unbounded admission fallback; its
  partial parser is an untrusted experiment, not a hardened public input service.
- Broader representative certificates before changing thresholds or claiming a
  complete solver reconstruction backend. A normalization mismatch is failure to
  certify by that method, not evidence that the identity is false.

## Identity checking and bounded fallback decision

Use `Expr.denote_eq_from_toPolynomial_eq` with a kernel-checked `decide` proof
of equal normal forms as the default certificate identity check. Prefer its
explicit soundness theorem and predictable supported grammar; the choice is
not a claim that it is faster than grind. Keep the native normalizer out.

On failure to certify, allow **one** bounded grind attempt for the same supported
ring fragment, with only the certificate's referenced premises. Use the default
200,000-heartbeat Lean command budget as the initial ceiling, no automatic budget
increase, and no E-matching against unrelated lemmas (`ematch := 0`, as in the
replay prototype). Budget exhaustion or an unsolved obligation returns unsupported
reconstruction; it never invokes the production admission path. These are initial
architecture limits, not a calibrated production performance guarantee. The
prototype does not implement the production dispatcher.

The port deliberately retains upstream incompleteness: over `Residue 6`,
`(2*x)*(3*x)` evaluates to zero but leaves a zero-coefficient monomial rather than
the empty polynomial. `Corpus.lean`'s `zeroProductNotCanonical` (in namespace
`Test.FiniteFieldPolynorm`) kernel-checks the failed representation equality, and
`zeroProductSemanticallyZero` proves the identity with grind. This supplies a
concrete reason for bounded semantic fallback; it does not justify rejecting a
true identity or changing the upstream algorithm silently.


## Measured polynomial comparison

Environment: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, release aarch64 Linux; installed Z3
5.1.0 build `ca39e58c525c5b03c2484f118ade2b92fae31215`; installed cvc5
1.4.1 `[git 2b2e844 on branch HEAD]`. No pins changed.

`Blaster/FF04/Corpus.lean` supplies identical explicitly reflected expressions
over nominal `Residue 65537` for both benchmark files. Cases: distribution;
`65536*x + x + y = y`; expansion of four factors `(x+y)`; and a quadratic product
with coefficients 123456789, 987654321, 7654321 and 1234567. Powers in the expanded
certificates are natural powers. This is a bounded certificate corpus, not a
solver benchmark or automatic-reification benchmark.

After building the finalized library graph, each command ran five times
sequentially, with no concurrent build/check workload. Python `perf_counter`
measured the complete subprocess, including imports, elaboration, kernel checking
and axiom printing:

```sh
lake env lean -Dprofiler=true -Dprofiler.threshold=1 TestsSolver/FiniteFieldPolynormGrind.lean
lake env lean -Dprofiler=true -Dprofiler.threshold=1 TestsSolver/FiniteFieldPolynormDecide.lean
```

All ten runs exited 0.

| Whole-file elapsed seconds | grind | Reflective port + kernel decide |
| --- | --- | --- |
| Run 1 | 0.6361 | 0.6019 |
| Run 2 | 0.6094 | 0.6290 |
| Run 3 | 0.6116 | 0.6009 |
| Run 4 | 0.6114 | 0.5931 |
| Run 5 | 0.6196 | 0.6120 |
| Median | 0.6116 | 0.6019 |
| Run 1 import, ms | 248 | 253 |
| Run 1 cumulative kernel type checking, ms | 42.6 | 53.0 |

Representative first-run exclusive profiler buckets:

| Certificate | `grind` bucket, ms | `decide` tactic bucket, ms |
| --- | --- | --- |
| Distribution | 1.23 | 4.38 |
| Characteristic cancellation | 1.57 | 3.57 |
| Nested products | 1.83 | 26.3 |
| Large coefficients | 1.84 | 14.5 |

**The exclusive buckets are not equivalent whole-proof costs.** Grind also pays
for expression simplification, canonicalization, typeclass inference and kernel
checking. Whole-file ranges overlap; these measurements establish that both
approaches are practical for these small cases, not a statistically established
speed winner or scaling claim. The normalizer selection is architectural; grind
is a viable bounded fallback. The pre-integration single runs were 0.645 s
(grind) and 0.640 s (normalizer); the repeated finalized-graph measurements above
supersede them. No production optimizer was changed, so there is no claimed
before/after Blaster speedup.

All four normalizer theorems and the generic soundness theorem report only
`[propext, Quot.sound]`; the four grind theorems report
`[propext, Classical.choice, Quot.sound]`. The tests also prove acceptance of the
distribution certificate and rejection of the false certificate `x = x + 1`.

## Live integration smoke

A second invocation of the installed cvc5 generated a fresh proof from the SMT
input above. A throwaway Lean source was constructed from that exact stdout,
without manually editing the certificate, then run with `lake env lean`.
Solver exit 0 with empty stderr; Lean exit 0 in 0.619 s, reporting:

```text
'liveOriginal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The temporary source was removed. This exercises producer text → parser →
per-step proof checking → original nominal Lean goal, rather than relying only
on the stored fixture. The stored regression retains the complete certificate
and executable trust-boundary negative cases.


## Configured verification and preservation

The finalized module graph passed `lake build Blaster` (225 jobs, exit 0,
6.16 s incremental). `LEAN_NUM_THREADS=5 lake test` and the cold
`make check_blaster` both subsequently exited 0. The latter rebuilt all four
FF-04 modules and the existing library, without changing the compilation script.

Two earlier execution failures are retained for clarity:

- An initial cold `lake build Blaster` failed after 219.19 s because its dependency
  graph had been discovered before the library root gained the new corpus import;
  `Blaster/FF04/Corpus.olean` was absent. Rediscovering the finalized graph with
  the exact build command succeeded, followed by the successful cold gate above.
- The first chained verification run passed `lake test` and `make check_blaster`
  but then stopped at preparation command `lake clean Tests` with
  `error: unknown package Tests`. `Tests` is a library, not a Lake package. No
  test failed in that chain. The subsequent preparation used `lake clean`, not
  a changed test/check configuration.

An explicit immutable-base comparison exited 0 with empty output:

```sh
git diff --exit-code 075fc92393730e05957ab6cc3064b41004663099 -- Tests scripts .github lakefile.toml lakefile.lean lean-toolchain docs/finite-fields/ff-01-integration.md Blaster/Optimize Blaster/Smt
```

No protected existing file, FF-01 implementation/report, expected solve result,
toolchain pin, dependency declaration or solver installation was modified.


Final remaining gates, run sequentially after `lake clean`, all exited 0
(456.92 s for the whole chain, including the clean rebuild):

| Command | Observed result |
| --- | --- |
| `LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests` | Success; 729 build jobs, including all FF-04 modules and existing tests. |
| `make test-solver` | Success; includes the FF-01 interface regression, both FF-04 benchmark proof files, CPC reconstruction and transitive-axiom allowlist. |
| `make test-cvc5` | Success; configured cvc5 suite, including existing Fin baseline and concurrent/backend tests. |
| `make solvercheck` | Success; both installed Z3 and cvc5 accepted. |
| `lake exe z3check` | Success; exact pinned assurance Z3 build reports `recfun-finder available`. |

The solver suite emitted model-unavailable, model-response-timeout, malformed
response and closed-output warnings from `CrashLifecycle.lean` and
`ResponseLifecycle.lean`, preserving Falsified verdicts; these diagnostics were
not silenced. The cvc5 suite reported its expected Valid/Falsified/Undetermined
outcomes and counterexamples. `CounterexampleSpike.lean` is excluded by the
unchanged configured `make test-cvc5` target; no additional exclusion was added.
The fresh finite-field CPC smoke above was run separately.

All required checks passed on the finalized source. Remaining gaps are the
explicit production and upstream-build limits above, not failing local gates.
Publication and completion signoff remain with the coordinator.

