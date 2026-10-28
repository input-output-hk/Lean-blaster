# FFM-12: Checked primality before native-field admission

## Job summary

Completed the checked-primality boundary and the consumed Curve25519 fixture
on Lean 4.24.0. All requested pure validations and both exact PROJECT gates
passed. No acceptance check remains incomplete. Publication, integration-branch
ancestry, and maintainer completion signoff are not claimed by this local run.

The selected modulus is the Curve25519 **base field** integer
`57896044618658097711785492504343953926634992332820282019728792003956564819949`,
equal to `2^255 - 19`. It is not the curve's subgroup order. The
[fixture document](large-prime-fixture.md) records the exact hexadecimal value,
meaning, pinned public proof provenance, mathematical adaptation, caller input
example, and compilation requirements. The consumed
[FFM-05 decision](m1-large-prime-decision.md) was not revised: the selected
proof port met its resource bounds before admission implementation proceeded.

## Changes

- `Blaster/FiniteField/Prime.lean`: mathematical divisor characterization
  `Prime p := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`; Prop-valued class
  `PrimeModulus p` containing that proof; proved lower bound, positivity,
  nonzeroness and the derived `NeZero` instance. Includes the required bounded
  small-divisor and prime-divisor lemmas, not a Boolean primality oracle.
- `PrimeFermat.lean`, `PrimeOrder.lean`, `PrimeBLS.lean`: selected mathematical
  closure for Fermat, multiplicative order, prime-power Pocklington witnesses,
  square-root Pocklington and sieve-free cube-root BLS. Source copyright and
  Apache-2.0 notices retained. Newer conditional lemma names were adapted to
  Lean 4.24.0's `if_pos`/`if_neg`; the needed list-counting fact is proved locally.
- `PrimePower.lean`: structurally recursive modular repeated squaring with a
  kernel-checked correctness theorem. The concrete proof supplies 256 binary
  digits of fuel and uses `decide +kernel` for large witness arithmetic.
- `Admission.lean`: `admitNativeField` consumes and revalidates a
  `ResidueDescriptor`; kernel equality ties both its original modulus and full
  carrier to the normalized integer. It accepts explicit `PrimeModulus`
  evidence or a matching hypothesis/local instance in the current Lean context.
  Kernel checking and a transitive axiom audit include used local-let values.
  Numeric recognition, Boolean results, unrelated proofs, solver-admitted
  proofs and native-decision/compiler trust do not authorize admission.
- `Blaster/FiniteField.lean`: imports the new modules through the existing
  library umbrella, so the normal library build covers the entire source slice.
- New `Tests/FiniteField/Primality.lean`: solver-free accepted/rejected/scoped
  evidence cases and executable axiom guards. Covers 2, 7, 11, reducible aliases,
  0, 1, composites 6/9/15, missing evidence, opaque/symbolic/free/metavariable/
  bound-variable moduli, `Fin` versus `Residue`, forged descriptors, unrelated
  or wrong-modulus proofs, malformed proof terms, solver/native trust, local
  lets/instances, and escaped evidence. The same translation state crosses
  scope boundaries; a previously admitted modulus is rejected without evidence.
- New `Tests/FiniteField/LargePrime.lean`: actual checked three-node proof for
  the selected modulus, explicit wrapper theorem, numeral/decimal/RFC-alias
  admission, missing-evidence rejection after successful admission, and
  executable transitive axiom guards. The five small-prime leaves are proved
  by bounded divisor checks, not imported from a prime table.
- Appended exactly the two individual new imports to `Tests/FixedIssues.lean`.
  No pre-existing test body or import was rewritten or reordered. No existing
  file under `Tests`, `scripts`, or `.github` was otherwise modified; no Lake,
  solver, toolchain or check configuration was changed.

There is no Mathlib dependency, generic certificate datatype/checker/search,
standard-modulus registry, new axiom, `sorry`, `admit`, or widening of
`blasterProven`. Composite rings continue to require only `NeZero`, outside
native admission. The admission calls neither discover solvers nor emit SMT
commands; both new test modules assert empty command/session state.

## Exact validation commands and outcomes

Commands ran from the repository root. Final requested checks:

| Command | Outcome |
| --- | --- |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Primality.lean` | Exit 0; accepted/rejected/scoped cases and axiom guards pass; final fresh run 1.253 s, peak RSS 1,251,256 KiB. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/LargePrime.lean` | Exit 0; actual selected proof, all three modulus spellings, missing-evidence rejection and axiom guards pass; final fresh run 1.245 s, peak RSS 1,258,984 KiB. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Carrier.lean` | Exit 0; unchanged composite-ring API and existing carrier audits pass; final fresh run 0.931 s, peak RSS 1,211,560 KiB. |
| `make test-pure` | Exit 0, 31.98 s; all 9 discovered finite-field pure modules freshly compiled, followed by the existing `Tests.Pure` tier. Also rerun successfully as part of the final `check_tests` gate after library-umbrella integration. |

The exact PROJECT commands were:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting
`Z3 version 4.15.2 - 64 bit`.

- Final `check_blaster`: exit 0, 216 jobs, 101.02 seconds. All new library
  modules were freshly compiled.
- Final `check_tests`: exit 0, 224.69 seconds. Finite-field pure coverage 9/9;
  `Tests.Pure` completed 245 jobs; `Tests.Z3` completed 713 jobs, including both
  new files through the appended aggregate imports.
- Existing lifecycle tests emitted model-unavailable, timeout, malformed
  response and diagnostic-file warnings while preserving their expected
  results. They did not fail. No expected result was weakened or changed.

### Documented caller smoke, with no solver on PATH

First verified solver absence:

```sh
env PATH=/home/agent/.elan/bin:/usr/bin:/bin /bin/sh -c '! command -v z3 && ! command -v cvc5'
```

Exit 0. Then supplied the complete Lean example from the fixture document on
standard input to:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS PATH=/home/agent/.elan/bin:/usr/bin:/bin lake env lean --stdin
```

Exit 0, actual output:

```text
admitted normalized modulus: 57896044618658097711785492504343953926634992332820282019728792003956564819949
'suppliedCurve25519' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This exercises the public descriptor/admission API using a transported caller
proof, not just compilation of a theorem. The smoke used standard input; no
throwaway source file remains.

Both new files were then freshly elaborated again with neither solver on PATH:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS PATH=/home/agent/.elan/bin:/usr/bin:/bin lake env lean Tests/FiniteField/Primality.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS PATH=/home/agent/.elan/bin:/usr/bin:/bin lake env lean Tests/FiniteField/LargePrime.lean
```

Both exited 0 with no diagnostics. Primality: 1.257 s, 1,253,552 KiB peak
RSS. LargePrime: 1.304 s, 1,259,892 KiB peak RSS. These additional runs used
the same serialized measurement wrapper and retained all finite proof limits.

## Proof resource measurement

A dedicated serialized source-artifact rebuild removed generated proof outputs
only, then ran the following commands, each with `LEAN_NUM_THREADS=1`:

```sh
rm -f .lake/build/ir/Blaster/FiniteField/Prime* .lake/build/lib/lean/Blaster/FiniteField/Prime*
lake build Blaster.FiniteField.PrimeOrder
lake build Blaster.FiniteField.PrimeBLS
lake build Blaster.FiniteField.PrimePower
```

The first target rebuilt `Prime`, `PrimeFermat`, their required C objects, and
`PrimeOrder`; the following targets rebuilt `PrimeBLS` and `PrimePower`.
Bundled libraries and the existing shared-library/OS caches were retained;
this is a clean proof source-artifact build, not a cold-machine benchmark.
No full gate or other Lean process ran alongside this measurement.

| Target | Exit | Wall time | Peak child RSS |
| --- | --- | --- | --- |
| `Blaster.FiniteField.PrimeOrder` | 0 | 2.019 s | 1,203,060 KiB |
| `Blaster.FiniteField.PrimeBLS` | 0 | 2.419 s | 1,326,848 KiB |
| `Blaster.FiniteField.PrimePower` | 0 | 0.592 s | 1,148,364 KiB |

Total wrapper-observed wall time: **5.096 seconds**. Maximum measured peak:
**1,326,848 KiB**, below 4 GiB. Fresh final fixture checking with dependencies
built: **1.245 seconds**, below 60 seconds. The 600-second proof-build bound
was not approached.

Measurements used a fresh Python wrapper for each command, `time.monotonic()`
for wall time, and `resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss`
for Linux child peak RSS in KiB. Each wrapper waited for its command before
starting another. The three direct file checks also used
`LEAN_NUM_THREADS=1`; the PROJECT commands retained their prescribed
concurrency. No proof measurements were taken concurrently with those gates.

`Prime`, `PrimeFermat`, `PrimeOrder`, and the fixture use finite
`maxHeartbeats 800000`; the fixture uses finite `maxRecDepth 2048`. Other proof
modules retain Lean's finite defaults. No heartbeat or recursion limit was
disabled or raised after failure.

### Resolved validation failures

- Initial modular-power proof elaboration used unavailable `conv_rhs` syntax;
  replaced with Lean 4.24.0's `conv => rhs` syntax.
- Initial order-module elaboration used newer `ite_eq_left`/`ite_eq_right`
  names; replaced with the equivalent bundled `if_pos`/`if_neg` lemmas.
- Initial large arithmetic used plain `decide` and reached the meta evaluator's
  recursion limit at the large witness obligations. Replaced those arithmetic
  invocations with the consumed decision's `decide +kernel` path, preserving
  finite options. The axiom guard rejected Lean's error-recovery `sorryAx`
  during that failed elaboration. The final proof checks cleanly with only the
  allowed foundational axioms; no placeholder was added to source.
- Initial pure-test elaboration had an extra closing parenthesis in an opaque
  descriptor case; corrected before successful execution.
- Initial exact build gate completed the old library root but failed coverage:
  `Blaster.FiniteField.PrimePower NOT compiled`. Added the new modules to the
  existing finite-field umbrella and reran the exact gate successfully. No
  build/check configuration was changed or bypassed.

## Remaining boundaries

No requested FFM-12 validation remains incomplete. The following are deliberate
scope boundaries, not implemented features:

- A local `PrimeModulus` hypothesis remains a caller assumption. Admission
  checks its type and context; it does not turn assumptions into closed theorems.
- Admission results containing local free variables are not globally reusable
  capabilities. Call `admitNativeField` again in a changed context. No admission
  cache or global instance search is provided.
- Symbolic/open native moduli, probable-prime/Boolean admission, general
  certificate automation and a standard-modulus registry remain excluded.
  Arbitrary closed moduli require a caller-supplied checked theorem.
- Solver routing/capability checks, finite-field SMT emission, inverse/division
  laws and verified solver reconstruction belong to later tickets. No cvc5
  finite-field profile, cvc5 floor tier, all-solvers gate, or default-environment
  `lake test` was run or claimed here.
- Resource numbers are this worker's measurements, not performance guarantees
  for other hosts or a comparison with upstream's newer Lean toolchain.
