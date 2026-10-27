# FFM-05: One large-prime fixture and its checked proof source

## Decision and acceptance boundary

Select the **Curve25519 base field**, with modulus `p = 2^255 - 19`, as the
single real large-prime fixture for FFM-12. Select the concrete Lean theorem
`Hex.Nat.curve25519_prime` and its committed certificate identified below as
the mathematical proof source. This is a source selection, not an implementation
of `PrimeModulus`, a promise that the upstream package builds on M1, or native
admission acceptance.

An actual proof source is available: this is not a request for an unidentified
supplier to discover a proof later. No person is assigned by this record and no
maintainer signoff is claimed. **M1 port feasibility remains provisional** until
FFM-12 re-elaborates the necessary argument and fixture on Lean 4.24.0 within the
budget below. Do not mark native admission accepted on the strength of this
record, the arithmetic smoke checks, or the existing PROJECT checks. If the
source cannot be supplied or its required port is infeasible, this decision
must be revised before admission implementation proceeds; an adapter alone is
not the missing proof.

This choice uses the ticket's allowance for one concrete large prime rather
than requiring BLS12-381 or a Pasta field. It is motivated by an accessible,
compact, already written kernel-proof source, not by numerical recognition or a
solver's primality response.

## Exact field identity and modulus

| Property | Selected value |
| --- | --- |
| Field | The prime coordinate/base field of Curve25519, `F_p` |
| Role | **Base**, not scalar/subgroup-order field |
| Modulus expression | `2^255 - 19` |
| Decimal modulus | `57896044618658097711785492504343953926634992332820282019728792003956564819949` |
| Hexadecimal modulus | `0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed` |
| Bit length | 255 |

[RFC 7748, section 4.1](https://www.rfc-editor.org/rfc/rfc7748#section-4.1)
identifies the Curve25519 field and separately gives the subgroup order
`2^252 + 27742317777372353535851937790883648493` and cofactor 8. Neither that
subgroup order nor the full curve order is this fixture's modulus. The RFC is
identity evidence, **not** the checked-proof supplier. Its parameters were
located through web search; direct RFC/Datatracker reads were blocked by HTTP
403 in this worker.

No BLS12-381 base or scalar field and no Pallas/Vesta field is selected. In
particular, there is no ambiguous "Pasta prime" alias or inference that a
Pallas base modulus and Pallas scalar modulus are interchangeable. Any later
substitution of a different field requires an explicit revised fixture decision.
This fixture tests prime-field admission, not curve operations or group orders.

## Immutable checked-proof source and provenance

The selected public source is `leanprover/hex-primality` at commit
`e89daa43f1c6f2038a59674598e2a5097e64c3df` (GitHub commit API reports
2026-10-15). These are frozen references for inspection/selective port, not new
Lake dependencies or permission to clone or install packages:

- [Concrete proof and literal certificate: `HexPrimality/Examples/Curve25519.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Examples/Curve25519.lean).
  Git blob `ea15e2a4b1e735e74be2a34834877d187abf8c0e`; the file credits
  Kim Morrison, copyright Lean FRO, LLC, Apache-2.0. Preserve applicable notices
  if source is ported. It supplies `curve25519Cert` and the theorem
  `curve25519_prime : Hex.Nat.Prime (2 ^ 255 - 19)`, proved by
  `prime_of_checkPrimeAt (c := curve25519Cert) (by decide +kernel)`.
- [Checker and its soundness: `HexPrimality/Cert.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Cert.lean).
  `prime_of_checkPrimeAt` requires both certificate-subject equality and checker
  acceptance. It concludes primality, not probable primality or nonzeroness.
- [Cube-root criterion: `HexPrimality/Cert3.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Cert3.lean)
  and [order argument: `HexPrimality/Order.lean`](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/HexPrimality/Order.lean).
  These provide the Brillhart–Lehmer–Selfridge and multiplicative-order
  arguments behind the concrete certificate, not merely certificate data.
- [Locked source dependencies](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/lake-manifest.json):
  HexArith `5ae42d0127e49eb3973ae01a5304a7adb2a9ee65`, HexBasic
  `f3ec4bd78149d07b4fd2372010563334f285b37e`.
  [HexArith's prime predicate and arithmetic lemmas](https://github.com/leanprover/hex-arith/blob/5ae42d0127e49eb3973ae01a5304a7adb2a9ee65/HexArith/Nat/Prime.lean)
  are Mathlib-free; these pins document provenance, not authorization to add
  their dependency graph to Blaster.

The concrete proof file contains a guarded `#print axioms` result listing only
`propext`, `Classical.choice`, and `Quot.sound`. That is inspected upstream
source evidence of ordinary Lean kernel checking, **not a local replay** or a
claim of zero foundational Lean axioms. No `sorryAx`, `nativeEqTrue`, solver
axiom, new primality axiom, or widening of `blasterProven` is acceptable in the
M1 port. The upstream source, its certificate, and the relevant soundness
interfaces were read over HTTPS at the pinned revisions; no upstream build,
transitive proof audit, or foreign `.olean` import is claimed here.

## Predicate and adapter contract

The source predicate is explicitly:

```lean
2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p
```

This is `Hex.Nat.Prime p`, not Mathlib's `Nat.Prime`, a Boolean probable-prime
filter, `NeZero p`, or an assumed field-law instance. FFM-12 must transport the
proved conjunction into the actual core `PrimeModulus` interface once that
interface is implemented. This ticket does not invent its constructor or fields.
If it uses the same divisor characterization, transport is unfolding and
packaging; if it uses a bounded-divisor formulation, prove both needed
implications using `2 ≤ p`, positivity and divisor bounds. A numerical equality
must tie the proof subject to the exact admitted modulus; accepting a proof
about a different number is forbidden.

The field layer also needs consequences, not extra assumptions: positivity and
nonzeroness of `p`; no nontrivial divisors; coprimality of each nonzero residue
with `p`; and the Euclidean/Bézout or equivalent argument used to construct an
inverse. These algebra requirements belong to their implementation tickets.
Primality plus an adapter does not by itself implement field laws or verified
SMT reconstruction.

## Concrete arithmetic route, without a general checker

The stored certificate has three non-leaf nodes. Its factor entries are
`(base, exponent-minus-one, child)`; the exponent offset must not be lost.
Let:

```text
q = 74058212732561358302231226437062788676166966415465897661863160754340907
t = 31757755568855353
```

| Subject | Criterion and known factored part F | Witness data |
| --- | --- | --- |
| `p` | Square-root Pocklington, `F = q` | base 2 for q, exponent 1; `F ∣ p-1`, `p < F²` |
| `q` | Cube-root BLS, `F = 2 * 353 * 57467 * t = 1288466195128439863020806` | base 2 for every factor; exponents 1; `r = 2028478494862525422475607`, `s = 22304740449229861598212`, `w = 2028478494862525422475606` |
| `t` | Cube-root BLS, `F = 2^3 * 223 * 4153 = 7408952` | base 5 for factor 2 with exponent 3; base 2 for 223 and 4153 with exponent 1; `r = 4028945`, `s = 289`, `w = 4028944` |

For each prime factor `c` and corresponding base `a`, prove the Fermat residue
`a^(n-1) % n = 1` and the gcd condition
`gcd ((a^((n-1)/c) % n + n - 1) % n) n = 1`.
The order/divisibility lemmas imply `F ∣ d-1` for every prime divisor `d` of
`n`. Square-root Pocklington concludes primality at the top node. At each
cube-root node additionally prove:

- `F ∣ n-1`, `F` even, and `R = (n-1)/F` odd;
- `R = 2*F*s + r`, `1 ≤ r < 2*F`;
- `n < (F+1) * (2*F*F + (r-1)*F + 1)`;
- the nonsquare discriminant condition, here witnessed by
  `w*w < r*r - 8*s < (w+1)*(w+1)`.

The five distinct small-prime leaves are `2`, `223`, `353`, `4153`, `57467`.
The upstream checker discharges them using its proved table. The bounded M1
route instead supplies just these five proofs by finite divisor checks and a
proved small-divisor criterion, avoiding a populated prime table. Ordinary
kernel reduction is adequate for these small checks; do not trial-divide the
255-bit modulus.

**Selective-port plan for FFM-12:**

1. Port only the natural-number prime/divisor, order and Pocklington/BLS lemmas
   needed for these three nodes, with their proof dependencies. Supply concrete
   node theorems bottom-up, then the one public fixture theorem. Reusable
   mathematical lemmas needed by this proof are permitted; a generic certificate
   datatype, checker, search tactic or registry is not required by this choice.
2. Use a structurally recursive modular repeated-squaring function with a
   kernel-checked correctness theorem to discharge the eight factor-witness
   obligations. Never expand the astronomical full powers before reduction.
   `Nat.gcd`, division, remainder and exact integer comparisons handle the other
   closed arithmetic. Prove the five small leaves, rather than porting the
   upstream table, sieve, search or Montgomery/native backend.
3. Remove newer module-system syntax/attributes as necessary; resolve every
   changed core lemma/tactic API against bundled Lean 4.24.0. Port proof terms,
   not compiled artifacts. Keep imports in Lean's bundled libraries and local
   Blaster modules. Preserve license notices on copied arguments.
4. Kernel-check the result and adapter, inspect their transitive axioms, and
   exercise actual native admission using this theorem in FFM-12. Negative
   composite and wrong-subject cases must not be admitted. Do not use a trusted
   FF mode to discharge any of these obligations.

[INFERENCE] This is an attainable source-port route because the proof is a
finite three-node argument with explicit witnesses and a Mathlib-free
soundness source. It is **not measured evidence** that the complete dependency
slice compiles on 4.24.0. The upstream
[toolchain](https://github.com/leanprover/hex-primality/blob/e89daa43f1c6f2038a59674598e2a5097e64c3df/lean-toolchain)
is `leanprover/lean4:v4.35.0-rc3`, not M1's 4.24.0. Its `Cert.lean` imports
`Cert3`, `Order`, `Table` and `HexArith.Montgomery.Context`; `Order` also imports
`HexBasic.ListShim`. Whole-package import is neither a minimal proof port nor
an approved dependency change. The remaining compatibility risk is the
arithmetic/order proof closure and its reduction cost, not finding the modulus
or hoping for a certificate generator.

## Compilation and resource budget

The [FFM-02 baseline](m1-toolchain-decision.md) remains Lean 4.24.0, source
commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, with no Mathlib or external
Lake packages. No pin, manifest, build declaration or trust boundary changes.

The proposed FFM-12 feasibility budget is **one Lean process at a time**, at
most **4 GiB peak RSS**, **600 seconds** for a clean build of the selective
proof slice, and **60 seconds** for fresh elaboration/kernel checking of the
fixture module once its dependencies are built. These are explicit stop and
review thresholds for this fixture, not observed results or changes to PROJECT
check timeouts. Reserve the remainder of the shared 8 GiB worker envelope for
the agent and system; do not run proof measurements alongside full gates.
Record wall time, peak RSS, exact command, options, cold/warm state and axioms
in FFM-12. Keep finite heartbeat/recursion limits and report their values; do
not silently disable limits, change compilers, or replace kernel reduction with
native trust when a limit is reached.

The upstream example reports 679 ms module elaboration/kernel checking and
4.505 seconds total wall time on an AMD EPYC 9455 with Lean 4.35.0-rc3 and
built dependencies. Those are **upstream host-specific comments**, not worker
measurements or an M1 budget guarantee. No local large-prime proof compilation
or peak-memory measurement has been performed by this decision ticket.

If the proof closure exceeds these thresholds or requires unavailable APIs,
record the failing obligation and obtain a revised scope/budget decision before
admission implementation proceeds. Do not silently swap primes, add Mathlib,
import all of Hex, or implement a general certificate engine to declare success.

## Scope boundary

Only this one field fixture is selected. Small child-prime lemmas are private
proof prerequisites, not additional standard-field fixtures. FFM-12 owns the
actual proof port, predicate adapter and admission evidence. FFM-22 must select
any optional general certificate automation or populated standard-modulus
registry. This decision implements neither, and does not use the historical
numeric-recognition or assumed-law probes as acceptance evidence.

## FFM-05 ticket report and job summary

Change: add this decision record only. It identifies the exact field, an
immutable concrete proof and its mathematical dependencies, a Mathlib-free
selective-port route, bounded resource expectations, and the unverified M1
compatibility boundary. No executable source, protected files, tests, expected
outcomes, dependency declarations, solver pins or toolchain pins are changed.
This section serves as the ticket report and job summary for the stack's commit;
local publication and maintainer signoff are not claimed.

### Validation performed

On 2026-10-27, from the repository root:

| Exact command | Observed outcome |
| --- | --- |
| `lake --version && lake env lean --version && lake env lean --githash` | Pass, exit 0: Lake `5.0.0-src+797c613`, Lean `4.24.0`, aarch64 Release, source hash `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. |
| `lake env lean --stdin` with the input below | Pass, exit 0, no diagnostics. Only numeral identity, lower bound and availability of kernel-decision syntax were checked; this is not a primality proof. |

```lean
import Lean
example : (57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat) = 2 ^ 255 - 19 := by decide
example : 2 ≤ (2 ^ 255 - 19 : Nat) := by decide
example : (17 : Nat) % 3 = 2 := by decide +kernel
```

A throwaway Python evaluation independently checked all three nodes' arithmetic
premises above with exact integer multiplication/division, modular `pow`, and
`math.gcd`, and trial-divided the five distinct small leaves through their
integer square roots. All assertions passed. This checks transcription and
feasibility only: it does not supply a Lean theorem or replace the selected
checked-proof source. No script or proof scaffold is retained.

| Exact command | Observed outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass; selected `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 `4.15.2`; clean build completed successfully, 171 jobs, 98.65 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass; same Z3 `4.15.2`; pure tier completed 200 jobs, Z3 tier completed 611 jobs, 175.69 seconds total. Lifecycle tests emitted model-response warnings; `SmtNatMod.lean` emitted Undetermined warnings at lines 37 and 41. Both tiers completed successfully without changing tests or expected results. |
| `git add --intent-to-add docs/finite-fields/m1-large-prime-decision.md && git diff --check && test -s docs/finite-fields/m1-large-prime-decision.md` | Pass, exit 0, no diagnostics; intent-to-add includes the new document in the whitespace check. |

The ticket's `rg -n 'modulus|proof|budget' docs/finite-fields/m1-large-prime-decision.md`
was performed using the repository search tool with the same pattern and path.
Pass: matches include the exact modulus, immutable proof source, and explicit
compilation/resource budget.

### Remaining work and limitations

- Full Lean 4.24.0 proof replay, minimal dependency-closure port, axiom audit,
  actual resource measurements, and native-admission integration are FFM-12
  work. Until those pass, M1 compatibility/admission is not accepted.
- The actual upstream proof can be supplied at the immutable path above; there
  is no unresolved search for a proof supplier. The unresolved issue is its
  bounded M1 port, not just predicate adaptation.
- No reference repository was cloned or built, and no new dependency downloaded
  into this project. No full transitive audit or newer-toolchain run is claimed.
- Existing PROJECT gates validate the existing core and pure/Z3 tiers, not
  this unimplemented fixture, cvc5 finite-field profiles, or reconstruction.
  No default-environment `lake test` or historical assumed-law probe was run.
