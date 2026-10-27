# FFM-07: Fin baseline on the current base

## Scope and revisions

This is a selective adaptation, not a merge of the historical optimizer or test
layout. Numeric modulus recognition and full applied-type opaque dispatch do
**not** add native finite-field support. `Fin n` remains unsupported as a
quantified SMT sort, and `Fin.div` remains truncating natural-number division.

Inputs observed on 2026-10-27:

| Input | Revision / identity |
| --- | --- |
| Reviewed concurrency base | `a69c5c266864a90064884519a5d208f5321cf379` |
| Public integration tip read through GitHub's commits API | `e36bc55bddd9d17c5287779b83b7436883cba6b5` |
| Supplied local synthetic root | `f4f0d8b9add5a811fa2c06ecdb0b11b35d2ce3a0` |
| Integration tip and supplied root tree | Both `9895513fcd5b5262d79d5c3e1f6a8c0b4c333c5c` |
| Lean | 4.24.0, `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Linux arm64 |
| Lake | `5.0.0-src+797c613` |
| PROJECT Z3 | 4.15.2, `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3` |
| Default Z3, version inspection only | 5.1.0, `ca39e58c525c5b03c2484f118ade2b92fae31215` |
| Installed cvc5 used for supplementary execution | 1.4.1, revision `2b2e844`, `/opt/cvc5-Linux-arm64-static-gpl/bin/cvc5`; `cocoa: yes` |

Tree identity is not local ancestry. The stack owns integration publication.
The [execution](m1-execution-decision.md) and
[toolchain](m1-toolchain-decision.md) parent decisions are retained unchanged.

### Pinned historical inputs: read, not rerun

- [FF-01 helper at 724e32c3](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/Blaster/Optimize/Basic.lean),
  the specified unchanged copy of the helper introduced at `075fc92393730e05957ab6cc3064b41004663099`.
- [Historical environment at 075fc923](https://github.com/input-output-hk/lean-blaster/blob/075fc92393730e05957ab6cc3064b41004663099/Blaster/Optimize/Env/Types.lean):
  top-level `natModulusCache`, `HashMap PtrExpr Nat`, and hashcons-dependent keys.
- [Interface regressions](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/TestsSolver/FiniteFieldInterfaces.lean),
  [Fin baseline](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/TestsSolver/SmtFinBaseline.lean),
  and [cvc5 counterpart](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/TestsCvc5/Cvc5FinBaseline.lean).
- [Original baseline document at d95b6bd0](https://github.com/input-output-hk/lean-blaster/blob/d95b6bd0e22b0f2d4fa3f0a5eb71dc6ad29cb669/docs/finite-fields/baseline-fin.md),
  compared with its [724e32c3 copy](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/docs/finite-fields/baseline-fin.md).

The original document reports historical base
`ab82a3cb647cbdecc198202244622554e2464e4d`, assurance Z3 5.1.0 and merged-branch
cvc5 1.4.1 with CoCoA. Its later copy changes ownership from
`Tests/Smt/SmtFinBaseline.lean` to `TestsSolver/SmtFinBaseline.lean`, not the
baseline observations. Division by zero was added after that historical base
run. Those reports are imported provenance, **not executions in this job**.

## Newly executed current-base observations

The first current-base run exposed a compatibility gap: the four true closed
`Fin` equalities reduced their values but retained distinct proof terms, leaving
constructor equalities such as `⟨0, …⟩ = ⟨0, …⟩` and reporting `Undetermined`.
The false field-division claim already reduced to `False`. Expectations were
not weakened. The minimal related correction in `OptimizeEq.lean` ignores
constructor proof parameters according to existing `ParamInfo.isProp` metadata
and consumes both successful structural-comparison results in `optimizeEq`.
All non-proof arguments still participate in its existing comparison lattice.
No historical optimizer infrastructure or unrelated rewrite was imported.

After that correction, every guard in the adapted pure Fin baseline passed:

| Goal | Mode | Observed result |
| --- | --- | --- |
| `∀ a b c : Fin 7, a * (b + c) = a * b + a * c` | `only-smt-lib` | Rejected: `Inductive datatype with instance parameters not supported: \`Fin` |
| Same quantified identity | `only-optimize`, expected result 2 | Expected Undetermined |
| `∀ a : Fin 7, a * a ≠ 2` | `only-smt-lib` | Same translation rejection; no counterexample |
| `∀ a b : Fin 7, a / b * b = a` | `only-smt-lib` | Same translation rejection |
| `(3 : Fin 7) * 5 + 2 = 3` | `only-optimize` | Valid; optimized to `True` |
| `(1 : Fin 7) / 2 = 0` | `only-optimize` | Valid; optimized to `True` |
| `(6 : Fin 7) / 2 = 3` | `only-optimize` | Valid; optimized to `True` |
| `(3 : Fin 7) / 0 = 0` | `only-optimize` | Valid; optimized to `True` |
| `(1 : Fin 7) / 2 = 4` | `only-optimize`, expected result 1 | Expected Falsified; optimized to `False` |

`Fin` has a value parameter `n : Nat`; the existing inductive translator rejects
that parameter. Passing the complete applied type to opaque dispatch preserves
it for future indexed-sort recognition; this ticket does not admit it.
The six existing opaque sorts retain their bare-head keys and original behavior:
Bool, Empty, Int, Nat, PEmpty and String.

`Fin.div` divides representatives using `Nat.div`, including `x / 0 = 0`.
GF(7) instead has `1 / 2 = 4`, since `2 * 4 = 1` modulo 7. The false guard above
prevents confusing these meanings. No field inverse or field sort is introduced.

## Modulus interface

`getNatModulus?` runs in the environment already initialized by `Optimize.main`.
It uses `optEnv.modulusCache : Std.HashMap Lean.Expr Nat`, initialized through
the existing default environment. It neither initializes the optimizer again nor
uses `mkExpr` as a hashcons substitute: here `mkExpr` consults rewrite results.

Direct Nat literals return without modulus-cache insertion. Successful closed
nonliteral results are stored under their original structural expressions;
failed recognition is not stored. Accepted numeric cases include zero, one,
composites, reducible aliases, elaborated numerals, the supported `OfNat`
projection and the large value `2 ^ 381 - 19`. These values are not primality,
field-admission or proof certificates. Optimizer errors propagate.

Guards reject non-Nat values, free variables, metavariables and loose bound
variables. Open `n - n` is rejected before optimization can make it zero.
Assignment alone does not make a metavariable input eligible; a caller's explicit
`instantiateMVars` produces a closed expression that can be recognized.
Tests also exercise repeated/distinct keys, opaque uncomputable Nat values,
cache preservation across environment updates, and unsafe-definition errors.
Lean's `mkNatLit` builds an elaborated `OfNat` application; literal-cache tests
therefore use `mkRawNatLit`, with an independent elaborated-numeral case.

## Test ownership and reproduction

| File | Imports and owner |
| --- | --- |
| `Tests/FiniteField/Interfaces.lean` | Imports `Tests.Pure`; numeric/cache/open-input and opaque-dispatch interfaces |
| `Tests/FiniteField/FinBaseline.lean` | Imports `Tests.Pure`; solver-independent Fin baseline |
| `ff-tests/OrdinaryCvc5Baseline.lean` | Imports only `Blaster`; standalone ordinary-arithmetic cvc5 baseline |

Only the individual imports of the two new pure modules are appended to
`Tests/FixedIssues.lean`. The existing backend aggregate reaches them there.
`make test-pure` still builds the pre-existing `Tests.Pure`; the two new pure
files are additionally checked directly. The standalone file is not imported
into `Tests`, and needs no child Lake package or new target.

From the repository root, after building Blaster and `Tests.Pure`:

```sh
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/Interfaces.lean
env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS lake env lean Tests/FiniteField/FinBaseline.lean
BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=120 BLASTER_STRICT_CVC5_RESULTS=1 lake env lean ff-tests/OrdinaryCvc5Baseline.lean
```

All three commands exited 0 after the correction. The cvc5 file preserved the
two quantified Fin rejections, closed `1 / 2 = 0`, and bounded-Nat distributivity
modulo 7. It contains no native FF operation or CoCoA-specific query.

**Uncompleted acceptance check:** that cvc5 execution used the installed
GPL/CoCoA binary, not ordinary non-CoCoA cvc5. Version/configuration inspection
and installation/staging searches found no non-CoCoA executable. Successful
ordinary arithmetic on a CoCoA-enabled binary does not establish execution
without CoCoA. A separately provisioned non-CoCoA binary, or scoped owner
approval to acquire one, is required to run the same command with its `bin`
directory first on PATH. No solver installation, pin or CI configuration was
changed to hide this distinction.

See [the ticket report](ffm-07-ticket-report.md) for exact PROJECT checks,
smoke evidence, initial failures and remaining validation limits. No native FF
solving, checked primality, new trust axiom, proof reconstruction, child-package
harness or remote CI execution is claimed here.

The final validation refresh again passed both direct pure files, both exact
PROJECT checks (including `make test-pure` and `make test-z3`), and the standalone
file on the installed GPL/CoCoA binary. Fresh stdin smoke runs reproduced the
cache, truncating-division and ordinary integer-query observations. The
[ticket report's final validation refresh](ffm-07-ticket-report.md#final-validation-refresh)
records the commands and timings separately from the initial implementation
run. The required execution without CoCoA remains outstanding.
