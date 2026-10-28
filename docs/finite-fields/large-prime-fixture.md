# Curve25519 checked-primality fixture

## Identity and frozen proof source

The consumed [FFM-05 decision](m1-large-prime-decision.md) selects the **base
(coordinate) field of Curve25519**, not its scalar/subgroup-order field.

- Expression: `2^255 - 19`.
- Decimal: `57896044618658097711785492504343953926634992332820282019728792003956564819949`.
- Hexadecimal: `0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed`.
- Bit length: 255.
- Parameter meaning: [RFC 7748 §4.1](https://www.rfc-editor.org/rfc/rfc7748#section-4.1).
  The RFC identifies the field; it is not a primality proof.

The proof data and mathematical arguments are selectively adapted from:

- [`HexPrimality/Examples/Curve25519.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Examples/Curve25519.lean),
  theorem `Hex.Nat.curve25519_prime`, and its literal `curve25519Cert`.
- [`Order.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Order.lean),
  [`Cert3.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Cert3.lean),
  and the mathematical witness transport in
  [`Cert.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Cert.lean).
- [`HexArith/Nat/Prime.lean`](https://github.com/leanprover/hex-arith/blob/5ae42d0127e49eb3973ae01a5304a7adb2a9ee65/HexArith/Nat/Prime.lean),
  for the divisor characterization, binomial/Fermat argument, and prime-divisor
  lemmas.

Copied arguments retain the upstream Lean FRO, LLC / Kim Morrison Apache-2.0
notice. These are source ports, not new Lake dependencies or imported compiled
artifacts. The upstream toolchain is 4.35.0-rc3; this project remains on 4.24.0.

## Mathematical adaptation

`Blaster.FiniteField.Prime` is explicitly

```lean
2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p
```

`PrimeModulus p : Prop` packages that proposition. Its lower bound, positivity,
and `NeZero p` instance are proved from the packaged theorem. `Residue p`
remains a modular ring under `NeZero p`; composite rings do not acquire a
primality requirement.

The concrete proof in `Tests/FiniteField/LargePrime.lean` follows three nodes:

| Subject | Criterion | Known factored part |
| --- | --- | --- |
| `31757755568855353` | Cube-root BLS | `2^3 * 223 * 4153` |
| `74058212732561358302231226437062788676166966415465897661863160754340907` | Cube-root BLS | `2 * 353 * 57467 * 31757755568855353` |
| Curve25519 base modulus | Square-root Pocklington | preceding 236-bit prime |

The five small leaves are proved by bounded divisor checks. Prime-power
multiplicative-order arguments produce divisibility of each prime divisor's
predecessor; explicitly checked coprimality combines the factors. BLS rules
out a factorization using the nonsquare discriminant witnesses in the consumed
decision. The final node uses the square-root bound.

`PrimePower.lean` supplies structurally recursive modular repeated squaring and
its correctness theorem. Closed arithmetic uses kernel-checked `decide`, not
`native_decide`, a solver, or a probabilistic primality result. No astronomical
full power is evaluated. The port replaces upstream module-system syntax,
provides the required list-counting argument locally, and avoids the upstream
prime table, sieve, Montgomery backend, certificate datatype/checker, search,
and registry.

## Supplying evidence

Import `Blaster.FiniteField.Prime` for the proposition and ring consequences;
import `Blaster.FiniteField.Admission` for the meta-level admission boundary.
Package a mathematical theorem with `PrimeModulus.mk`. There is deliberately no
global concrete-prime instance or automatic primality search.

`admitNativeField descriptor (some proofExpr)` accepts an explicit proof term.
With no explicit term, it searches only the current Lean local context for a
matching `PrimeModulus` hypothesis or local instance. It does not synthesize a
global instance. The proof subject must be definitionally equal to the exact
normalized numeral. An external proof using a propositionally equal spelling
can first be transported with its equality theorem.

This complete example uses the checked fixture theorem; it is also the
documented proof-input smoke program:

```lean
import Tests.FiniteField.LargePrime

open Lean Meta Blaster.Optimize Blaster.FiniteField
open Test.FiniteFieldLargePrime

theorem suppliedCurve25519 : PrimeModulus (2 ^ 255 - 19) :=
  curve25519_eq ▸ curve25519_evidence

run_meta do
  let action : TranslateEnvT Unit := do
    discard <| Optimize.main (mkRawNatLit 0)
    let type := mkApp (mkConst ``Residue) (mkNatLit (2 ^ 255 - 19))
    let some descriptor ← getResidueDescriptor? type
      | throwError "expected a concrete residue carrier"
    let admitted ← admitNativeField descriptor (some (mkConst ``suppliedCurve25519))
    logInfo m!"admitted normalized modulus: {admitted.residue.modulusValue}"
  discard <| action.run (default : TranslateEnv)

#print axioms suppliedCurve25519
```

The fixture is intentionally a test module, not a production standard-modulus
registry. Production callers supply their own theorem through the same
`PrimeModulus` interface. The reusable mathematical lemmas are in the
`Blaster.FiniteField.Prime*` modules.

Admission kernel-checks the proof and audits its transitive constants, including
used local-let values. Allowed axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. Solver-admitted proofs and compiler/native-decision trust are
rejected, including when hidden behind a correctly typed local let. Boolean
primality results and `NeZero` instances are not proof inputs.

The result retains the original full carrier expression, original modulus
expression, normalized integer, and proof expression. A proof containing local
free variables is scoped: the result must not be cached as a global capability.
Readmit it in a changed context. Every call revalidates the descriptor and
current proof context; an earlier successful call never supplies missing
evidence to a later call. Local assumptions remain assumptions of the caller's
theorem, not closed proofs of primality.

## Compilation requirements and limits

Use the repository's Lean 4.24.0 and bundled libraries. No Mathlib or external
package setup is required. The proof files use finite heartbeat limits of
800,000 where specified; the concrete fixture sets `maxRecDepth 2048`.

The consumed decision requires serialized proof measurement, at most 4 GiB
peak RSS, at most 600 seconds for the clean selective proof build, and at most
60 seconds for fresh fixture elaboration with built dependencies. Measurements,
exact commands, outcomes, and any incomplete validation belong to the
[FFM-12 ticket report](ffm-12-ticket-report.md).
