# FFM-11: Public nominal ring and instantiated opacity

## Completed changes and job summary

Implemented the carrier and export policy selected in
[m1-public-api-decision.md](m1-public-api-decision.md). This report records the
implementation and validation; it does not claim outstanding maintainer naming
confirmation, integration-branch publication, or final signoff.

- `Blaster/FiniteField/Basic.lean` defines the sole nominal
  `Blaster.FiniteField.Residue (p : Nat)`, with `rep : Fin p`. Its only import is
  the pinned toolchain's `Init.GrindInstances.Ring.Fin`. No optimizer, translator,
  solver, replay, primality registry, or external package is imported.
- `Blaster/FiniteField/Residue.lean` supplies the selected narrow import;
  `Blaster/FiniteField.lean` is the algebra-only umbrella. `Blaster.lean`
  re-exports that umbrella. There are no placeholder prime/field modules.
- The kernel-checked `Lean.Grind.CommRing` and `Lean.Grind.IsCharP` instances,
  literals, natural/integer casts, natural powers, and scalar operations retain
  their actual nonzero assumptions. The inherited `Fin` add/mul/neg/sub
  operations need no `NeZero` assumption, even on the empty carrier. This does
  **not** supply a ring, numeral, or inhabitant at modulus zero. Modulus one is
  the one-element ring; nonzero composite moduli remain rings. No `Inv`, `Div`,
  or `Field` instance is introduced.
- `Tests/FF04/Nominal.lean` now imports the public carrier and provides the
  expressly permitted reducible compatibility alias, with `mk`, `rep`, `ext`,
  and `mk.injEq` forwards. It contains no duplicate ring instances. Corpus and
  replay implementation references use the canonical public carrier. The
  historical `Tests/FiniteField/Prototype.lean` is unchanged.

## Recognition and dependency boundary

`Blaster/FiniteField/Structural.lean::getResidueModulus?` recognizes the nominal
carrier and reducible carrier aliases without requiring a closed modulus. It
can therefore protect operations over symbolic `p` in low-level optimizer
modules. It never treats `Fin p` as `Residue p`.

`Blaster/FiniteField/Recognize.lean::getResidueDescriptor?` is above
`Optimize.Basic`, not imported back into it. The descriptor retains:

- `type`: the original complete type expression, including an input type alias;
- `modulus`: the recognized modulus expression;
- `modulusValue`: the concrete natural number obtained through the consumed
  `getNatModulus?` helper.

Open expressions, including assigned-but-uninstantiated metavariables in the
original type, are rejected by concrete recognition. Closed opaque moduli with
no computable numeral are rejected too. Zero, one, and composites are valid
numeric descriptors: this API makes no mathematical primality or field-admission
claim. Existing closed-modulus caching and error propagation are reused.

## Opacity and translator audit

`Optimize.isOpaqueResidueOperation` checks the actual canonical instantiated
dictionary, its modulus, heterogeneous carrier positions, literal index, and
natural exponent type. It recognizes `HAdd`/`Add`, `HMul`/`Mul`, `HSub`/`Sub`,
`Neg`, `OfNat`, natural powers, and the natural/integer cast spellings Lean
actually elaborates, including `Nat.cast` and `Int.cast`. Definitionally equal
dictionary aliases are supported; unrelated or unknown local dictionaries and
canonical dictionaries for another modulus are not accepted. Comparison
metavariables are isolated from the caller's state.

The same recognition protects `Env.isOpaqueFun`, the generic
`Utils.isNotFoldable` / `getUnfoldFunDef?` route, and application reduction.
`Optimize.Basic` routes canonical applications before generic implicit-argument
normalization can reduce their dictionaries or literals into `Fin` operations.
Explicit operands still traverse the existing optimizer, including nested
residue expressions. No new finite-field rewrite family is added.

`Smt/Translate/Application.lean` rejects canonical residue operations before
name-only application dispatch or arbitrary-function fallbacks, and guards
`translateOpaqueFun` itself. The name-only `translateConst.translateDefineFun?`
check intentionally remains unchanged: that entry accepts only unapplied
constants and rejects implicit arguments before reaching this check. It cannot
carry an instantiated residue dictionary. Applied operations use `translateApp`.

`translateOpaqueType` examines the **complete applied type** before splitting
its head and arguments. It retains the concrete modulus in its unsupported
translation diagnostic, or diagnoses a nonconcrete modulus. No residue sort,
representation datatype fallback, or uninterpreted arithmetic encoding is
introduced. Native SMT emission remains FFM-15 work. Residue is not added to
`relationalCompatibleTypes`; Nat/Int/Fin behavior is covered by regressions and
the ordinary project suite.

## Regression and proof-boundary evidence

The only test registrations are these two final imports appended to
`Tests/FixedIssues.lean`:

```lean
import Tests.FiniteField.Carrier
import Tests.FiniteField.Opaque
```

Both new files import `Tests.Pure`.

`Carrier.lean` checks symbolic ring and characteristic laws; zero versus one;
composite zero divisors and subtraction; characteristics two, seven, and eleven;
modulus and numeral-index aliases; natural powers and casts; absent
inverse/division/field instances; definitional FF04 interoperability; and actual
canonical-carrier replay and polynomial normalization. Its executable
`Lean.collectAxioms` audit covers the ring/characteristic instances and new named
algebraic proofs, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The modulus proof in `Opaque.lean` has the same executable allowlist. No added
trust axiom, native-decision trust, `sorry`, or `admit` is accepted.

`Opaque.lean` runs the actual optimizer and translator entry points. It checks
canonical operations, partial applications, symbolic moduli, aliases, nested
operation preservation, all six unrelated arithmetic dictionaries, an unknown
local dictionary, and a canonical dictionary for a different modulus. It also
checks direct generic unfolding guards, reduction, full-type translator dispatch,
unsupported translation without emitted SMT commands, concrete descriptors,
open/opaque modulus rejection, and existing numeric sort/relational handling.
No solver session is started by these opacity checks.

An in-memory comparison against the immutable local `HEAD` examined all 184
existing protected files under `Tests`, `scripts`, and `.github`, plus existing
root lake/toolchain files. Every byte matches, except exactly the two authorized
final imports above. This includes the inherited `Prototype.lean`. No protected
script, workflow, existing test expectation, package pin, or check configuration
was changed.

## Validation commands and outcomes

Commands below ran from the repository root. No default-environment `lake test`
was run. The direct-file commands execute elaboration, checked proofs, and the
metaprogrammed optimizer/translator scenarios, rather than relying only on an
already-built test import.

| Exact command | Outcome |
| --- | --- |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Carrier.lean` | Pass, exit 0, including executable axiom audits. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Opaque.lean` | Pass, exit 0, including canonical/custom dictionary discrimination, generic optimizer preservation, and translator rejection. |
| `env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Prototype.lean` | Pass, exit 0; original goal reports exactly `[propext, Classical.choice, Quot.sound]`, and inherited rejection cases and axiom guard pass. |
| `make test-pure` | Pass, exit 0. Existing finite-field discovery freshly compiled all 7/7 modules, including both new files; the ordinary `Tests.Pure` build completed with 227 jobs. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass, exit 0; clean compilation and source coverage, 198 jobs, 92.26 s. Selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 4.15.2. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass, exit 0, 226.30 s. Same Z3 4.15.2 binary; finite-field pure coverage 7/7 (236 jobs), ordinary pure tier 227 jobs, Z3 tier 689 jobs. Both new files and unchanged historical fixtures compiled in the Z3 aggregate too. |
| `lake build Blaster` | Pass after the integration corrections below, 198 jobs. |
| `lake build Tests.Pure` | Pass, 227 jobs. |
| `lake env lean FFM11Smoke.lean` | Pass after removing an unsupported diagnostic command. Actual evaluated results: `(19 : Residue 7)^3` has representative `6`; `(2 : Residue 6)*3` has representative `0`; `(1 : Residue 1) = 0` evaluates to `true`. It also printed the actual power-instance and cast elaborations. Throwaway file removed after verification. |

The three final direct commands ran together with `&&` and completed in 3.46 s.
The successful integration chain `lake build Blaster &&` the direct Opaque command
`&& make test-pure` completed in 89.11 s. These are whole-process observations,
not an optimization benchmark or speedup claim.

### Integration corrections and earlier failures

- Initial `lake build Blaster` exited 1 because the generated natural-power
  instance is `Residue.instHPowNat`, not `Residue.instHPow`. Corrected recognition
  to use the actual declaration; the carrier and FF04 modules had already built.
- An initial diagnostic `lake env lean FFM11Smoke.lean` exited 1 because this Lean
  version does not accept `#print prefix`. `#synth` and `#check` still exposed the
  actual instance names and assumptions. Removed the unsupported diagnostic and
  reran the completed smoke successfully.
- Initial direct Carrier and Opaque commands each rejected a numeral over a
  non-reducible named modulus because no `NeZero` instance for that name had been
  provided. Added checked local-fixture nonzero evidence, rather than changing
  production instance requirements. Carrier's axiom audit also rejected the
  elaboration-generated `sorryAx` from the failed declaration; the final audit
  passes with no such dependency.
- The next direct Opaque run exposed that ordinary cast notation elaborates to
  `Nat.cast`/`Int.cast`, rather than directly to class projections. Added these
  spellings to the same canonical-dictionary recognition, then reran the full
  direct scenario successfully.
- Before executing Carrier, source inspection confirmed that the pinned `Fin`
  add/mul/neg/sub operations require no nonzero premise. New tests were corrected
  to assert their availability on the empty carrier, while preserving every
  negative ring/literal/cast/power test at zero. No existing test was changed.

The lifecycle suites emitted their model-unavailable, model-response timeout,
closed-stream, and malformed-response warnings while preserving Falsified
verdicts. Successful checks were not silenced and expected outcomes were not
changed.

## Remaining boundaries

- Checked primality/admission, large-prime evidence, and prime-derived nonzero
  evidence remain FFM-12 work. A descriptor is not proof of primality.
- Native finite-field SMT emission and typed translation metadata remain FFM-15
  work. Residue translation deliberately fails explicitly in this ticket.
- Inverse/division laws and the conditional field instance remain FFM-17 work.
- No new rewrite families, ordered representation bridges, Mathlib dependency,
  native-decision proof path, or widening of `blasterProven` is introduced.
- Native finite-field solving, solver proof production, cvc5 backend/floor/all-
  solver tiers, and solver-distribution profiles were not exercised by this
  ticket. The historical fixture replays its checked fixed CPC text without
  invoking an external solver.
- Maintainer confirmation recorded as outstanding in the consumed API decision
  remains outstanding. Final review, publication, and signoff are not claimed.

All requested FFM-11 validation commands passed. No requested check remains
incomplete; the unexercised out-of-scope lanes and future-ticket boundaries are
listed above. This report and job summary are supplied in the project tree for
the stack's owner-attributed commit; no separate local commit or push is claimed.
