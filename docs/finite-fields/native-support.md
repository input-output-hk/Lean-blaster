# Native finite fields: M1 usage and trust boundary

M1 supplies a nominal modular-ring/prime-field API, checked prime admission,
source translation to cvc5 native finite fields, total inverse/division, and
solver verdicts with optional counterexamples. It does **not** reconstruct
native solver proofs. A successful native query is not a kernel-checked proof
of the original Lean proposition.

The executable companion is [GuideExamples.lean](../../ff-tests/GuideExamples.lean).
Its algebra theorems use ordinary checked Lean proofs; its solver examples
observe results without closing theorems with `blaster`. See the
[M1 completion record](m1-completion.md) for integrated validation, the
[measurement report](m1-measurements.md) for bounded experiments, and the
[rule-audit bookmark](m1-rule-audit.md) for the unfinished M2 obligations.
Historical decision records describe earlier plans: the current modules and
[solver manifest](solver-manifest.json), not their intended-only module tables
or older binary selection, define this guide's implemented surface.

## Imports and the selected API

For commands/tactics and algebra, use:

```lean
import Blaster
open Blaster.FiniteField
```

For algebra alone, use:

```lean
import Blaster.FiniteField
open Blaster.FiniteField
```

The algebra-only umbrella does not invoke or configure a solver. Narrow imports
include `Blaster.FiniteField.Residue` (ring carrier),
`Blaster.FiniteField.Prime` (the actual prime-evidence module), and
`Blaster.FiniteField.Field` (conditional field operations). There is no module
named `Blaster.FiniteField.PrimeModulus`: `PrimeModulus` is a declaration in
`Prime`. An import does not implicitly open the namespace.

- `Residue (p : Nat)` is a nominal structure with `rep : Fin p`, not an alias
  for `Fin p`. `Residue.ext` transports equality of representatives.
- `[NeZero p]` supplies modular numerals, natural/integer casts, addition,
  multiplication, negation, subtraction, natural powers, `Lean.Grind.CommRing`
  and `Lean.Grind.IsCharP`. Composite nonzero moduli are valid rings; modulus
  one is the zero ring. Modulus zero does not have this ring interface.
- `Prime p` means `2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p`.
  `PrimeModulus p : Prop` packages that mathematical statement in its `prime`
  field. It implies `NeZero p`.
- `[PrimeModulus p]` enables inverse, division, integer powers and
  `Lean.Grind.Field` on the **same** carrier. Integer powers exist in the Lean
  algebra API but are outside the native translation fragment.
- `Fin.div` is truncating representative division, not this field operation.
  `Fin p` itself does not select native finite-field translation.

For example, this whole block works with the algebra-only import above and is
also present in the executable companion:

```lean
theorem primeSeven : Prime 7 :=
  prime_of_bounded 7 2 (by decide) (by decide) (by decide)

theorem evidenceSeven : PrimeModulus 7 := ⟨primeSeven⟩

example : (5 : Residue 6) + 3 = 2 := by decide

section
local instance : PrimeModulus 7 := evidenceSeven

example : (1 : Residue 7) / 2 = 4 := by decide
end

example (p : Nat) [PrimeModulus p] : (0 : Residue p)⁻¹ = 0 :=
  Residue.inv_zero

example (p : Nat) [PrimeModulus p] (x : Residue p) : x / 0 = 0 := by
  rw [Residue.div_eq_mul_inv, Residue.inv_zero, Lean.Grind.Semiring.mul_zero]
```

Here `prime_of_bounded 7 2` uses the checked bound `7 < (2 + 1) * (2 + 1)`
and checks the possible divisor `2`. Ordinary `decide` discharges finite closed
arithmetic obligations; there is no primality oracle or `native_decide`.
Generic algebra can use symbolic `p`; native admission cannot.

## Exact prime evidence and large moduli

There is no global concrete-prime registry or automatic primality search.
Even `Residue 7` needs matching evidence before a residual query enters the
native route. Nonzeroness, a Boolean primality answer, a printed SMT field
sort, or success on an earlier query does not supply that evidence.

Admission checks the proof's type against `PrimeModulus` of the exact normalized
closed modulus, kernel-checks it, and audits transitive constants and used
local-let values. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed
axioms. Evidence depending on `blasterProven`, an admission, or native-decision
trust is rejected. A local hypothesis remains a hypothesis, not a closed proof
that a prime exists.

For ordinary algebra, install checked evidence using a local instance, or
`letI : PrimeModulus p := hp` in a scope where it is needed. Native admission
searches the **current local context**, not global instance synthesis. A global
instance that lets Lean elaborate division is not by itself a native admission
input. Expose a matching top-level evidence parameter in a command, as below,
or supply checked evidence through a scoped local let in a direct client. The
meta-level `admitNativeField descriptor (some proofExpr)` interface also accepts
an explicit proof expression; it does not launch a solver.

For large primes, provide a checked mathematical theorem for your exact modulus
and package it as `PrimeModulus p`. Reducible closed aliases are normalized;
propositional equality alone requires explicit transport first. Do not replace a
large proof by trial division, a probable-prime result, or a solver assertion.

The checked repository fixture is the **Curve25519 base field** `2^255 - 19`,
not its scalar/subgroup-order field. Its decimal modulus is
`57896044618658097711785492504343953926634992332820282019728792003956564819949`.
[large-prime-fixture.md](large-prime-fixture.md) records its frozen proof sources,
Pocklington/BLS adaptation, ordinary checked arithmetic and resource conditions.
In this checkout, after building the test fixture, the companion uses:

```lean
import Tests.FiniteField.LargePrime

open Blaster.FiniteField Test.FiniteFieldLargePrime

theorem suppliedCurve25519 : PrimeModulus (2 ^ 255 - 19) :=
  curve25519_eq ▸ curve25519_evidence
```

This import is a repository **test fixture**, not a production dependency or a
standard-modulus registry. Downstream clients supply their own checked theorem
through the same interface. The companion then runs a concrete large-field
query with the theorem installed in a scoped local let:

```lean
private instance : NeZero (2 ^ 255 - 19) := ⟨by decide⟩

private def largeDistributive : Prop :=
  ∀ x y : Residue (2 ^ 255 - 19), x * (y + 1) = x * y + x

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt

run_meta do
  let proof := mkConst ``suppliedCurve25519
  withLetDecl `checkedPrime (← inferType proof) proof fun _ => do
    let environment : TranslateEnv :=
      { (default : TranslateEnv) with optEnv.options.solverOptions := {
          solver := some .cvc5, timeout := some 30 } }
    let ((result, _), _) ←
      (Translate.main (mkConst ``largeDistributive)).run environment
    match result with
    | .Valid => logInfo "Curve25519: Valid (solver verdict, not a reconstructed proof)"
    | .Falsified _ => throwError "Curve25519 distributivity was falsified"
    | .Undetermined => throwError "Curve25519 distributivity was undetermined"
```

The explicit `NeZero` instance here only elaborates the ring-valued proposition;
the local `checkedPrime` is the separate admission evidence. The result is a
solver observation, not a declaration proving `largeDistributive`.

## Commands, verdicts and the tactic warning

Choose cvc5 explicitly with `(solver: cvc5)`, not `(solver := cvc5)`.
Default backend selection remains explicit option, then `BLASTER_SOLVER`, then
Z3. Native residual queries require cvc5 in `single` mode; they do not silently
switch from Z3. `first` and `agree` are unsupported for native fields.

The following companion queries retain the evidence parameter explicitly.
They ask conditional questions under `PrimeModulus 7`; `evidenceSeven` above
independently establishes that this assumption has checked evidence.

```lean
#blaster (solver: cvc5) (timeout: 30)
  [∀ (_ : PrimeModulus 7) (x y : Residue 7),
    x * y = 0 → x = 0 ∨ y = 0]

#blaster (solver: cvc5) (timeout: 30) (solve-result: 1)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x * x ≠ 2]

#blaster (solver: cvc5) (timeout: 30)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x / 0 = 0]

#blaster (solver: cvc5) (only-smt-lib: 1) (solve-result: 2)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x ^ (7 : Nat) = x]
```

The first and third expect `Valid`; the second expects `Falsified` because
`3 * 3 = 2` modulo 7 (the solver may instead display the other root, 4).
`solve-result` is an expected-result check: `0` means `Valid` (default), `1`
means `Falsified`, and `2` means `Undetermined`. It is not a proof-strength
selector. A native `Valid` corresponds to UNSAT of the negated goal; native
`Falsified` corresponds to SAT. An ordinary `unknown` remains `Undetermined`.
Timeouts, malformed responses and process failures are not evidence of validity.
A model-fetch failure preserves `Falsified` and reports unavailable/partial
counterexample details, rather than inventing values or changing the verdict.

The last command is a translation-only example: `only-smt-lib` performs no
solver discovery, capability probe or solver execution. It still enforces the
carrier, evidence, backend and syntax boundaries. `only-optimize` also does not
launch a solver. A query completely discharged by existing optimization never
needs the native route; it cannot demonstrate solver capability.

`#blaster` reports a verdict without declaring a theorem. By contrast,
`by blaster (solver: cvc5)` closes a `Valid` goal using the existing
`Blaster.Tactic.blasterProven` axiom. With the normal warning setting, it emits:

```text
declaration uses 'blasterProven' (SMT-verified, no proof term)
```

The warning's historical “SMT-verified” label does **not** mean Lean proof
reconstruction. Suppressing the warning does not change the dependency. The
executable guide deliberately does not use this tactic to make proof claims.
For checked theorems, use the algebra laws and ordinary Lean proof procedures;
solver success alone is insufficient, even for an optimized goal.

## Supported residual fragment and diagnostics

After the existing optimizer runs, native translation supports:

- Closed concrete `Residue p` carriers with exact checked `PrimeModulus p`
  evidence. Multiple separately admitted moduli can occur in one query; there
  is no coercion between their fields.
- Top-level theorem parameters and hypotheses; field variables; canonical
  modular literals and closed natural/integer coefficients; addition,
  multiplication, negation, subtraction, inverse and division.
- Closed natural-number exponents, encoded by square-and-multiply with
  logarithmic expression size. `0 ^ (0 : Nat) = 1`.
- Equality/disequality, propositional Boolean structure and supported `ite`
  branches. Proof-dependent branches are not supported.

Residual quantifiers or lambdas, symbolic/open moduli, variable or integer
exponents, `.rep`/`.val`, order comparisons, representation constructors/casts,
variable natural/integer-to-field conversions, higher-order expressions and
mixed non-Boolean theories are outside this fragment. Algebraic validity or a
Lean typeclass instance does not enlarge it. There is no silent integer,
datatype or uninterpreted-function fallback for an unsupported field expression.

Useful diagnostic fragments include:

| Diagnostic | Meaning / action |
| --- | --- |
| `missing checked PrimeModulus 7 evidence` | Put exact checked evidence in the current local context, or make the command's evidence parameter explicit. |
| `evidence type/modulus mismatch` | Transport/package a proof for the exact modulus, not another prime or just `Prime p`. |
| `below 2 and cannot be prime` | Zero and one cannot be admitted as prime fields. |
| `concrete closed Residue modulus` | Close and normalize the modulus; symbolic algebra is not symbolic native solving. |
| `resolved backend z3 ... use solver: cvc5` | Select cvc5 explicitly; no backend fallback occurs. |
| `do not support solver-mode` | Use single-cvc5 mode, not concurrent modes. |
| `residual quantified or higher-order FF queries` | Restrict to top-level parameters and the supported first-order body. |
| `native finite-field polynomial fragment: unsupported expression` | Inspect the reported expression against the fragment above. |
| `native finite-field solving capability preflight failed` | Repair the staged inventory/protocol capability, not the theorem or its expectations. |

Division is total: `0⁻¹ = 0`, `a / 0 = 0`, and `0 / 0 = 0`, including in
characteristic two. Cancellation such as `a / b * b = a` needs `b ≠ 0`.
The translator encodes a fresh inverse witness `u` with the full graph
`(b = 0 ∧ u = 0) ∨ (b ≠ 0 ∧ b * u = 1)` and uses `a * u` for division.
Graph obligations are positive assertions outside the negated goal, not
polarity-dependent assumptions. No native SMT division operator or `Fin.div`
semantics is substituted.

## Staged solver, capabilities and execution

Use repository Lean **4.24.0**, Python 3, and the complete separately staged
native inventory. The operative `solving` profile is **cvc5 1.4.1**, revision
**`2b2e844`**, static **GPL/CoCoA**, with exact archive and executable hashes in
[solver-manifest.json](solver-manifest.json). Earlier 1.3.4 selection text in the
[distribution decision](m1-solver-distribution-decision.md) and audit bookmark is
historical, not permission to substitute those bytes for the current manifest.

The manifest inventories Linux arm64 and x86_64. Its retained native arm64
qualification is affirmative; the retained x86_64 row records hash acquisition
but no executable qualification. Do not generalize an arm64 run into an x86_64,
macOS or Windows validation claim. Each consumer must pass its offline checks.

CoCoA is required **only for native finite-field solving**, not for pure algebra,
ordinary cvc5 tests or ordinary `Fin` regressions. The intended ordinary CI
version after the maintainer's post-M1 workflow update is **cvc5 1.4.1**, retaining
the **1.2.1 support-floor** lane. The protected workflow in this checkout still
pins ordinary cvc5 **1.3.4**; M1 does not edit it or claim that update has landed.
Ordinary non-GPL cvc5 and the hash-pinned GPL native profile remain separate even
when their version numbers match. A working PATH `cvc5` or its version string
alone does not qualify a native session.

From the repository root, acquisition/setup (network-enabled operator step) is:

```sh
make ff-stage
```

An image can instead deliver the complete approved `.artifacts/finite-fields`
tree before offline jobs start. Retain archive, payload, metadata and evidence,
not just a copied executable. Separate-process execution approval is not blanket
public redistribution or corresponding-source-review approval.

Consumers use the offline gate; it must not download or fall back to PATH:

```sh
python3 scripts/finite_fields/probe_solver.py \
  --manifest docs/finite-fields/solver-manifest.json \
  --artifact-root .artifacts/finite-fields --profile solving --offline --check
```

Qualification checks inventory identity, version/configuration, complete setup,
SAT/UNSAT solving and model support. The profile uses `ff-field-polys=false` and
`ff-solver=gb`; it is not a split-solver or proof-export qualification. Production
preflight uses the same repository manifest/probe contract before launching the
native session. Run from inside the staged checkout, with `python3` on PATH.
Missing inventory, a bad hash, missing CoCoA or failed protocol capability is a
hard setup error, not a skipped test or a reason to use another executable.

To elaborate the executable guide after staging, run these commands serially:

```sh
lake build Blaster Tests.FiniteField.LargePrime
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS \
  BLASTER_FF_CVC5="$PWD/.artifacts/finite-fields/solving/bin/cvc5" \
  lake env lean ff-tests/GuideExamples.lean
```

`BLASTER_FF_CVC5` names the staged executable for the native test harness
convention; it does not override production preflight's manifest selection.
The guide's commands select cvc5 explicitly and set a 30-second solver timeout.
No PATH solver substitution is needed. The separate integrated native tier is
`make test-cvc5-ff`; ordinary gates remain separate. These suites clear shared
outputs, so do not run their builds/checks concurrently. The guide is a standalone
executable documentation source, not an implicit addition to the tier's imports.

## What remains unfinished

M1 algebra proofs, checked admission and semantic integration do not constitute
M2 proof infrastructure. The production native pipeline still lacks proof
reading, checked FF-rule reconstruction, general checked reification and final
transport to the original goal. The historical FF-04 fixed-text replay and
checked reflected polynomial normalizer are narrower experiments, not a general
native proof dispatcher.

The proof-producing solver profile and its distribution/provenance qualification,
the full FF rule audit (including root completeness, disequality witnesses,
ideal/variety certificates and exhaustion), and **FF optimizer rewrites** remain
deferred. The [audit bookmark](m1-rule-audit.md) explicitly is not a full audit;
[measurements](m1-measurements.md) of normalization and native solving do not
fill these gaps. No new axiom, native-evaluation trust, relaxed result expectation
or verified-native claim is authorized by this guide.
