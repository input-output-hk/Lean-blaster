# FFM-19: representative corpus and deferred-audit handoff

## Job summary

Added an executable, content-pinned corpus and the deferred M2 audit bookmark.
The manifest contains **26 runnable entries**, executed by **16 distinct
invocations**, and **24 explicitly non-runnable historical catalogue entries**.
All runnable entries passed. Both required PROJECT gates passed with Z3 4.15.2.
The 197 original protected files checked before/after remain byte-identical.

The circuit representatives are **new, project-authored arithmetic circuits**:
a complete five-constraint F7 contradiction and an eight-gate, degree-five
Curve25519 circuit certificate. They are not recovered Nethermind, cyclic-5,
or historical F7 artifacts. The required representative circuit and selected
large-prime classes have actual executable inputs; unrecovered historical
candidates do not stand in for either class.

No production implementation, existing test, script, workflow, Lake file,
toolchain pin or expected result changed. No external repository was cloned.
No proof-producing binary was staged, no proof-production probe was run, no
proof trace was produced, and no new FF proof-rule example was checked in Lean.
The new kernel-checked examples are polynomial/semantic corpus certificates,
not implementations or probes of solver proof rules.

## Committed artifacts

- [m1-rule-audit.md](m1-rule-audit.md): the exact FFM-03 fork identity, seven
  commit-pinned source-file bookmarks, ordinary normalization soundness
  interfaces, excluded native-decision paths and open M2 questions. This is a
  bookmark, not the full rule-obligation audit.
- [benchmark-corpus.json](benchmark-corpus.json): source revisions,
  redistribution basis, SHA-256 pins, propositions/reflections, context slots,
  instances, grammar, expected results and exact argument vectors. A shared
  module invocation checks every entry assigned to that module.
- [Semantic.lean](../../fixtures/finite-fields/audit/Semantic.lean): F7 square,
  constant wraparound, characteristic cancellation, explicitly unfolded
  recursive sum, selected-prime identity/implication and an actual false-goal
  counterexample.
- [Circuits.lean](../../fixtures/finite-fields/audit/Circuits.lean): explicit
  gate constraints, residual expressions, normal-form equality certificates,
  residual-zero connections and semantic conclusions for both circuits.
- Twelve new `.smt2` files in [fixtures/finite-fields/audit](../../fixtures/finite-fields/audit):
  solver-only edge cases, with no proof requests or proof options enabled.
- [run_corpus.py](../../fixtures/finite-fields/audit/run_corpus.py): checks 42
  committed input hashes and the solving executable hash, then executes each
  distinct declared invocation once and checks the declared outcomes. It does
  not time tactics, regenerate fixtures, fetch binaries or contact maintainers.

The imported `Tests/FF04/Corpus.lean`, its ordinary-decide comparison module
and replay are unchanged. Five manifest entries retain the four historical
normalization pairs plus the false-certificate/composite-ring boundary. The
historical report's timings are not presented as new measurements.

## Exact representative certificates

### Five-constraint F7 circuit

Context slots are `0=x, 1=y, 2=m, 3=s`. All five constraints are committed:

```text
x=2; y=3; m=x*y; s=m+x; s=0
r0=x-2; r1=y-3; r2=m-x*y; r3=s-(m+x); r4=s
r4-r3-r2-(y+1)*r0-2*r1 = 1  (mod 7)
```

`fiveCertificate` checks the reflected identity by ordinary `decide`.
`fiveResidualsZero` and `fiveCombinationZero` connect the actual constraints
to zero; `fiveContradiction` derives `0=1` and rejects it. This is not a claim
that the unrecovered historical five constraints were these constraints.

### Selected-prime circuit and provenance

The modulus is exactly the Curve25519 **base** field,
`57896044618658097711785492504343953926634992332820282019728792003956564819949`
(`2^255-19`), not the scalar field or a similarly sized substitute.

```text
u=x+y; v=u*x; w=v+y; t=w*x; z=t+y; a=z*x; b=a+y; out=b*x
out = x^5+x^4*y+x^3*y+x^2*y+x*y
```

Each gate has a committed residual `r0` through `r7`. The normalizer checks

```text
x^4*r0+x^3*(r1+r2)+x^2*(r3+r4)+x*(r5+r6)+r7
  = out-(x^5+x^4*y+x^3*y+x^2*y+x*y).
```

The source constraints imply each residual is zero; `chainConclusion`
transports the certificate to the stated output. This is a bounded synthetic
straight-line circuit, not a production cryptographic circuit or scaling claim.

Both new modules import the existing `Tests.FiniteField.LargePrime` fixture
and expose its exact modulus equality and primality theorem. The
[consumed decision](m1-large-prime-decision.md) and
[implemented proof provenance](large-prime-fixture.md) remain authoritative:
`Hex.Nat.curve25519_prime` and `curve25519Cert` from public hex-primality
`e89daa43f1c6f2038a59674598e2a5097e64c3df`, selectively ported by FFM-12.
No new proof source or dependency is substituted. Ring normalization itself
needs `NeZero`, not a primality assumption; the imported prime theorem is
separately included in each module's transitive axiom allowlist.

## Licensing and historical recovery limits

New inputs are original project contributions under the repository Apache-2.0
license. Their mathematical statements are not copied external circuit text.
Their content hashes identify the newly authored source revision until the stack
assigns its publication commit. Existing dependencies are pinned to supplied
baseline `4cf0ce952db0d95bb4f15497bf67fc9c918da5c4` and exact bytes. Existing
normalizer and prime-port attribution/license notices remain intact.

The recovery scope was the consumed local docs/modules/fixtures and the frozen
public FF-04 report at `724e32c377b5c6bfdecaf200984203b21c75355b`. Those inputs
did not supply the original discovery document, exact Nethermind four
constraints, historical F7 five constraints, cyclic-5 parameters, or their
redistribution basis. No such artifact was copied or reconstructed by guessing.
The catalogue explicitly records missing content, revision and/or license.
Where the ticket gives a complete mathematical statement, a separately labelled
new representative may implement it; that does not recover the historical input.

The catalogue includes every requested discovery family: F7 square/constants/
characteristic; Nethermind F41; modulus 394357; selected-prime identity and
implication; `.val`/order/no-wrap; bit-weighted sum; recursive sum; zero-product
with/without witness; nonzero self-division; square-implies-nonzero; five-constraint
F7; F3/F7 no-root with/without field facts; F3 enumeration; cyclic-5 with/without
field hints; and a false goal. Representation/bitness entries remain outside
native M1 unless separately proved. No tautological inverse-witness example is
substituted for the missing historical native self-division input.

Missing historical inputs block measurements of **those exact cases**, including
Nethermind and cyclic-5. They do not block measurement of the separately authored
committed circuits. Any voluntary maintainer outreach is nonblocking future
context; no automated outreach occurred.

## Validation commands and observed outcomes

All commands ran from the repository root on 2026-10-28. No default-environment
`lake test` was run. No checks failed during this ticket's validation.

### Required PROJECT gates

The exact prescribed commands were executed through `/bin/bash`:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reported
`Z3 version 4.15.2 - 64 bit`, and exited **0**.

- Build: clean Blaster coverage build completed, **246 jobs**.
- Tests: FF pure discovery compiled **17/17 modules** (**298 jobs**), ordinary
  pure tier completed **275 jobs**, and Z3 tier completed **767 jobs**.
- Existing lifecycle tests emitted model-unavailable/timeout/framing warnings.
  Existing `Tests/FiniteField/AxiomAudit.lean:11` and
  `Tests/FiniteField/DivisionEncoding.lean:324` emitted `sorryAx` declaration
  warnings in their existing negative-test inputs. These files were unchanged;
  no new corpus theorem admits that axiom. No warning suppression or expected
  result change was made.
- These gates recompile the preserved fixed-text FF-04 replay tests. They do not
  generate new solver proofs or convert this ticket into a rule audit.

### Direct corpus validation

```sh
lake env lean fixtures/finite-fields/audit/Semantic.lean
lake env lean fixtures/finite-fields/audit/Circuits.lean
python3 fixtures/finite-fields/audit/run_corpus.py
python3 -m json.tool docs/finite-fields/benchmark-corpus.json >/dev/null
test -s docs/finite-fields/m1-rule-audit.md
```

Every command exited **0**. Each direct new Lean module produced empty stdout
and stderr. Their executable transitive axiom checks allow only `propext`,
`Classical.choice` and `Quot.sound`; the checks include the imported selected
prime theorem. The modules keep the default bounded heartbeat budget and use
ordinary kernel `decide` for normal-form equalities.

The runner verified **42 input hashes** and the cvc5 executable hash, then
passed **26 entries / 16 distinct invocations**, distinguishing all **24
catalogue-only entries** without attempting to execute them. The four distinct
Lean invocations were:

```sh
lake env lean Tests/FiniteField/PolynormDecide.lean
lake env lean Tests/FF04/Corpus.lean
lake env lean fixtures/finite-fields/audit/Semantic.lean
lake env lean fixtures/finite-fields/audit/Circuits.lean
```

The two historical module commands printed their existing axiom summaries;
all stderr was empty. The two new module commands were silent and successful.

For each row below the exact argument vector was
`["cvc5", "--lang", "smt2", "fixtures/finite-fields/audit/<file>"]`.
Each ran once individually before manifest integration and once through the
runner, exiting **0** with the listed sole stdout line and empty stderr:

| File | stdout |
| --- | --- |
| `f3-no-root.smt2` | `unsat` |
| `f3-no-root-field-hint.smt2` | `unsat` |
| `f7-no-root.smt2` | `unsat` |
| `f7-no-root-field-hint.smt2` | `unsat` |
| `f7-zero-product.smt2` | `unsat` |
| `f7-zero-product-witness.smt2` | `unsat` |
| `f7-square-implies-nonzero.smt2` | `unsat` |
| `f394357-linear.smt2` | `unsat` |
| `f3-enumeration.smt2` | `unsat` |
| `f7-false-goal.smt2` | `sat` |
| `f2-guarded-fermat-zero.smt2` | `unsat` |
| `f2-unguarded-fermat-zero.smt2` | `sat` |

`command -v cvc5 && cvc5 --version` exited **0**, identifying
`/usr/local/bin/cvc5`, version `1.4.1`, source `2b2e844`. SHA-256 of that existing
binary was
`b0dd6483a078269251618cf7e354c675120f8a659990111c5bfc785e91057d86`, matching the
consumed FFM-09 `solving` profile. The corpus runner enforces that identity.
No binary acquisition or staging was needed. Solver SAT/UNSAT statuses are
not Lean proofs of finite-domain completeness.

The inherited FFM-03 text selects `1.3.4`/`solve`, whereas the explicitly
consumed FFM-09 manifest selects `1.4.1`/`solving`. This report records, rather
than silently repairs, that discrepancy. These executions qualify only the
consumed 1.4.1 bytes for the listed inputs; no 1.3.4 qualification is inferred.
The deferred fork identity remains exactly the FFM-03 bookmark.

### Protected-file check

An in-process Python SHA-256 inventory was taken before writing artifacts for
all existing files under `Tests`, `scripts`, `.github`, plus `lakefile.lean`
and `lean-toolchain` (`lakefile.toml` is absent). At completion, comparison of
every recorded path/hash passed: **197 unchanged original files**, none
missing. No test import was appended. The inventory is an ephemeral validation
check, not a replacement for the stack's immutable-base protection.

## Remaining scope and unrun checks

- Full FF-rule audit, proof acquisition, rule schemas, root-list completeness,
  ideal membership, finite-field exhaustion and original-goal verified closure
  remain M2. Fork partially structural checks and upstream 1.4.2's absent FF
  checker are source bookmarks, not newly qualified executable capabilities.
- Retain the local nominal/ordinary-decide architecture. The exact normalizer
  interfaces are recorded in the bookmark; no automatic reifier or production
  normalizer-first dispatcher is added. `nativeEqTrue`-dependent reference
  paths are excluded. Neither solver statuses nor failed tactics prove falsity.
- The F2 Fermat cases establish why the zero guard remains necessary when
  `p-2=0`. This is an explicitly exercised alternative only, not an enabled
  inverse encoding or performance recommendation.
- FFM-20 owns normalizer-versus-grind and production-pipeline measurements.
  This ticket reports correctness checks, not historical timing reproduction,
  optimization speedups, representative production performance or scalable
  finite-domain reasoning.
- No new proof-producing executable, source build, external package build,
  x86_64 run, cvc5 1.3.4/floor/all-solvers lane, or remote CI execution was
  performed. No claim is made that the installed solving binary provides proofs.
- No required local validation remains unrun. Missing historical inputs and
  the inherited solver-decision discrepancy remain explicitly recorded limits;
  completion signoff and publication remain with Riley/the stack.
