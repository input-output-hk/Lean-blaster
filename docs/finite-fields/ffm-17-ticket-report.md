# FFM-17: Total field operations and the inverse graph

## Job summary

Implemented total prime-field operations and the inverse graph on the existing
nominal carrier. The full pinned Field interface, pure examples, and executable
transitive axiom allowlist pass. Both exact PROJECT gates pass with Z3 4.15.2.
No requested validation remains incomplete. Publication and maintainer signoff
are not claimed by this local run.

## Changes and mathematical construction

- `Blaster/FiniteField/Field.lean` adds `Inv`, `Div`, integer powers, and the
  complete Lean 4.24.0 `Lean.Grind.Field` instance under `PrimeModulus p`.
  The installed pinned `Init/Grind/Ring/Field.lean` was read before implementation.
  `Basic`'s nominal carrier, ring operations, casts and natural powers are unchanged.
- Inverse is explicitly zero at zero. Otherwise it computes the modular power
  with exponent `p - 2` using the existing, kernel-verified `powMod` repeated
  squaring implementation. Fuel `p` is sufficient by `p - 2 < 2 ^ p`; recursion
  stops when the halved exponent becomes zero rather than traversing all fuel.
  `inv_eq_pow` connects the executable operation to the existing natural power.
- `coprime_rep` derives coprimality directly from the actual mathematical prime
  predicate and the nonzero representative's bound. The existing local
  `pow_pred_mod` theorem then proves `mul_inv_cancel`. The dependency chain is
  natural-number arithmetic, not a prior field instance or solver assertion.
- `eq_inv_of_mul_eq_one`, `inv_one` and `inv_inv` are proved using the ring and
  inverse law before constructing `Field`. This avoids circular use of generic
  field laws in the integer-power implementation. Nonnegative integer powers
  are definitionally the old natural powers; negative powers invert those powers.
  The negation law includes zero and negative exponents.
- Division is definitionally multiplication by the denominator's inverse,
  never truncating `Fin.div`. The primality requirement does not grant inverse,
  division or a field instance to a composite ring.
- `Blaster/FiniteField/InverseGraph.lean` defines
  `InverseGraph b y := (b = 0 ∧ y = 0) ∨ b * y = 1` and proves
  `inverseGraph_iff`, `inverseGraph_total`, `inverseGraph_functional` and
  `div_eq_mul_of_inverseGraph`. The last theorem gives `a / b = a * y` from
  a denominator witness, including zero denominators.
- The public `Blaster/FiniteField.lean` umbrella imports both new mathematical
  modules. Neither module registers optimizer rules.
- New `Tests/FiniteField/Field.lean` covers generic inverse/division laws,
  characteristic two and seven, zero inverse, zero division, `0 / 0`,
  nonzero self-division, `0 ^ 0`, positive powers of zero, negative integer
  powers, natural/integer coherence, composite-ring instance rejection,
  nontruncating division, and the unchanged FF04 one-carrier compatibility path.
- New `Tests/FiniteField/AxiomAudit.lean` runs a throwing transitive
  `collectAxioms` allowlist over all new public operations, proof prerequisites,
  the Field instance, graph theorems and named regression proofs. Only
  `propext`, `Classical.choice` and `Quot.sound` are accepted. Missing audit
  targets are errors, not silently empty axiom sets.
- Audit negative controls place two wrapper definitions between the guard and
  each forbidden dependency: `sorryAx`, `Lean.trustCompiler`,
  `Lean.ofReduceBool`, and an arbitrary fresh axiom. Each control checks both
  transitive discovery and rejection by the same guard used on public terms.
  Synthetic declarations exist only inside a restored temporary environment;
  explicit leak checks prevent them from becoming exported declarations.
- Test registration consists solely of appending the two new imports to
  `Tests/FixedIssues.lean`. No pre-existing bytes of that file or other existing
  protected tests, scripts, workflows, Lake configuration or pins were changed.

No carrier-cardinality theorem is assumed or needed. In particular, the proof
never infers cardinality from `Field` and characteristic alone. Using the local
Fermat arithmetic to construct inverse adds no Fermat optimizer reduction,
zero-product rewrite registration, solver emission, or proof reconstruction.

## Validation commands and outcomes

Commands ran from the repository root:

- `lake build Blaster.FiniteField.Field`: exit 0, 17 jobs. All fields of the pinned
  interface and their arithmetic prerequisites kernel-check.
- `lake env lean --run FieldSmoke.lean`: exit 0. A temporary executable checked
  every inverse graph and double inverse at moduli 2 and 7, all 4 and 49 division
  pairs respectively, and integer powers from -7 through 7 against natural
  powers and their inverses. Output:

  ```text
  modulus 2: all inverse graphs, double inverses, division pairs and powers -7..7 passed
  modulus 7: all inverse graphs, double inverses, division pairs and powers -7..7 passed
  ```

  The temporary smoke program was removed after successful execution.

- `lake build Tests.FiniteField.Field Tests.FiniteField.AxiomAudit`: final exit 0,
  245 jobs. Both pure modules compiled, including all rejection controls.
  An initial run found a regression-harness instance-shadowing error: binding
  an opaque local `CommRing` made `IsCharP` refer to that new ring rather than
  the public instance. The new test now checks positive instance synthesis
  inside `Nonempty` without shadowing the carrier's ring. All positive and
  negative checks remain present; no existing tests were changed.

The exact PROJECT commands were:

```sh
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster
PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests
```

Both selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, reporting
`Z3 version 4.15.2 - 64 bit`.

| Check | Outcome |
| --- | --- |
| `make check_blaster` with the exact PATH above | Exit 0; clean library build and source coverage check passed, 240 jobs. |
| `make check_tests` with the exact PATH above | Exit 0; finite-field pure coverage 15/15 freshly compiled modules (290 jobs), `Tests.Pure` (269 jobs), and `Tests.Z3` (755 jobs) passed. |

The audit emits `declaration uses 'sorryAx'` while constructing its temporary
negative-control wrapper. This expected diagnostic is not suppressed. The
control must be rejected by the actual allowlist, and the audit explicitly
checks that its declarations do not escape the restored environment. No new
public proof or instance depends on `sorryAx`, native-decision trust, or a new
axiom. Existing lifecycle tests also emitted model-unavailable, response-timeout
and malformed-response warnings; the Z3 tier emitted Undetermined warnings at
`Tests/Smt/SmtNat/SmtNatMod.lean:37` and `:41`. The gate still exited 0, and no
expected result or check was changed.

## Scope and remaining limitations

- No incomplete acceptance check remains.
- No Mathlib dependency, solver call in the new mathematical/regression modules,
  permanent new axiom, or change to `blasterProven` was introduced.
- Native inverse/division emission remains FFM-18; this ticket exposes the
  mathematical denominator-witness theorem it needs.
- No optimizer registration, Fermat reduction rule, generic certificate
  automation, or production proof reconstruction was added.
- No cvc5 backend tier was run: this change is solver-independent and the
  required PROJECT gates are the Z3 4.15.2 tier.
