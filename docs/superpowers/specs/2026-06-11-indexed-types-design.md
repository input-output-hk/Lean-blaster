# Indexed Types Support — Design

**Date:** 2026-06-11
**Status:** Approved design, pre-implementation
**Scope:** `BitVec n`, `Fin n`, `SMTArray α`, `UInt8/16/32/64`, `Int8/16/32/64`, `USize/ISize`, `Vector α n`

## Goal

Extend lean-blaster's Lean → SMT-Lib V2 translation to support indexed type
families. Today the translator only handles non-parameterized opaque types
(`Bool`, `Int`, `Nat`, `String`, `Empty`, `PEmpty`); any indexed type fails.

This is a from-scratch implementation on current `main` (post `Solver` →
`Blaster` rename), using per-type hooks consistent with the existing
codebase patterns. Prior exploratory branches
(`feat/bitvec-claudeAdded-support`, `feat/EVM`) are *not* merged or ported;
they may be consulted only as a record of semantic pitfalls.

## Non-Goals

- Dynamic indices: `BitVec n` with variable `n`, `Fin a.size`,
  `Vector α n` with variable `n` — all rejected with actionable errors.
- `toNat` / `toInt` conversions between BitVec-family and Int-family sorts
  (would require Z3-specific `bv2int`/`int2bv`; deserves its own design).
- Higher-order array/vector ops (`map`, `foldl`, `zipWith`, …).
- Precise `Array.size` modeling (Vector covers the static-length case).

## Architecture

Four integration seams; every indexed type plugs into each:

1. **Type translation** — `Blaster/Smt/Translate/Quantifier.lean`.
   One `translate<X>Type` per family, intercepted in `translateTypeAux`
   *before* the `translateOpaqueType` fallback. Intercept order
   (most-specific head first): `Vector` → `Array` → `UInt*/Int*/USize/ISize`
   → `Fin` → `BitVec`.
2. **Operation translation** — `Blaster/Smt/Translate/Application.lean`.
   One `translate<X>Op?` per family, dispatched from the application
   translator. Implicit args (widths, bounds, proofs) are filtered by the
   existing `createAppN` machinery.
3. **Literal recognition** — `Blaster/Smt/Translate.lean` and
   `Blaster/Optimize/Expr.lean`: detect whnf value forms and emit SMT
   literals directly.
4. **Optimization layer** — `Blaster/Optimize/`: register all ops in
   `Opaque.lean` (prevent unfolding into `Fin`/`Array` internals); one
   rewriting module per family for constant folding and identities, hooked
   into `OptimizeApp.lean`.

**Sort/qualifier pattern:** every instantiation with *literal* indices gets
a monomorphized SMT sort. An `@is<Sort>` qualifier is added only when the
SMT carrier is wider than the Lean type (Fin, qualified element sorts);
exact carriers (BitVec, UInt) need none.

**Soundness policy:** every gap is either (a) a translation error naming
the construct and the supported alternative, or (b) a documented
over-approximation in the safe direction — spurious counterexamples
possible, false proofs never.

## Phasing

Each phase lands green and is independently mergeable.

| Phase | Content |
|---|---|
| 1 | `BitVec n`: sort, literals, full op set, division-semantics wrappers |
| 2 | `Fin n` (static bound) + `SMTArray α` |
| 3 | `UInt*/Int*/USize/ISize` as erased views over BitVec; configurable USize width |
| 4 | `Vector α n`: static-length arrays with faithful pointwise equality |

---

## Phase 1 — `BitVec n`

**Sort.** `BitVec n` (`n` literal) → built-in indexed sort `(_ BitVec n)`;
cache entry only, no `define-sort`, no qualifier (exact carrier).
Variable `n` → error.

**Literals.** Recognize `BitVec.ofFin w (Fin.mk v _)` (whnf form) and
`BitVec.ofNat w v` (value mod `2^w`) → `(_ bvV w)`.

**Operation table** (width args dropped automatically):

| Category | Lean | SMT |
|---|---|---|
| Arith | `add, sub, mul` | `bvadd, bvsub, bvmul` |
| Division | `udiv, sdiv, smod, srem` | per-width `define-fun` wrappers |
| | `umod` | `bvurem` (semantics already agree) |
| Bitwise | `and, or, xor, not, neg` | `bvand, bvor, bvxor, bvnot, bvneg` |
| Compare | `ult, ule, slt, sle` (+ `<`/`≤` instances) | `bvult, bvule, bvslt, bvsle` |
| Structure | `++`, `extractLsb hi lo`, `extractLsb' s l` | `concat`, `(_ extract hi lo)` (literal indices) |
| Width | `zeroExtend`/`setWidth` (grow), `signExtend` | `(_ zero_extend k)`, `(_ sign_extend k)`, `k = newW − oldW` |
| | `setWidth` (shrink) | `(_ extract (newW−1) 0)` |
| Rotate | `rotateLeft k`, `rotateRight k` (literal `k`) | `(_ rotate_left k)`, `(_ rotate_right k)` |

**Shifts**, by shift-amount type:
- Literal `Nat` `s` → constant second operand `(_ bvs w)` to
  `bvshl/bvlshr/bvashr`. Lean and SMT agree shifts ≥ width yield 0
  (sign-fill for `ashr`) — no wrapper.
- `BitVec w` amount → direct `bvshl/bvlshr/bvashr`.
- Variable `Nat` shift or rotate amount → error (no faithful fixed-width
  encoding of an unbounded symbolic `Nat`); message suggests the
  BitVec-amount form.

**Division wrappers** (the one real semantic trap): Lean `x.udiv 0 = 0`,
`x.sdiv 0 = 0`; SMT `bvudiv x 0 = allOnes`, `bvsdiv x 0 = ±1`. Per-width
lazy `define-fun`, e.g.

```smt
(define-fun udiv_8 ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
  (ite (= y (_ bv0 8)) (_ bv0 8) (bvudiv x y)))
```

Same pattern for `sdiv`, `smod`, `srem`.

**Soundness constraints.**
- `BitVec` must NOT be added to `relationalCompatibleTypes` — those
  rewriting rules assume order laws violated by wrap-around arithmetic.
- Optimizer folding must match Lean exactly: mod `2^w` everywhere; signed
  ops via two's complement.

**Optimizer.** `Blaster/Optimize/Rewriting/OptimizeBitVec.lean`:
literal-literal folding for all ops; identities (`x &&& 0 = 0`,
`x ||| 0 = x`, `x ^^^ x = 0`, shift-by-0, `x * 1`, …). All op names
registered in `Opaque.lean`.

---

## Phase 2 — `Fin n` and `SMTArray α`

### `Fin n` (static bound)

- **Sort:** `Fin n` (`n` literal) → `(define-sort Fin_n () Int)` with
  qualifier `(and (<= 0 x) (< x n))` on quantified variables — same scheme
  as `Nat` over `Int`. `Fin 0`: qualifier is `false` (uninhabited; ∀ over
  it vacuously true). Non-literal bound → error pointing at `SMTArray`.
- **Ops:** `Fin.val`, `Fin.mk` → identity. Arithmetic is modular:
  `Fin.add a b` → `(mod (+ a b) n)` etc., with literal `n`. Comparisons →
  Int comparisons (sound: `Fin` order is the inherited Int order; no
  wrap-around representation issues).
- `Fin n` MAY participate in Int-relational reasoning (unlike BitVec): the
  carrier is a genuine Int sub-range with inherited order.

### `SMTArray α`

**Purpose:** `Array.get` demands `Fin a.size` (dynamic bound, rejected).
`SMTArray` is a verification-friendly array API with `Nat` indexing.

**Library surface** — new file `Blaster/SmtArray.lean`:

```lean
abbrev SMTArray (α : Type u) := Array α
def SMTArray.get [Inhabited α] (a : SMTArray α) (i : Nat) : α := a.getD i default
def SMTArray.set (a : SMTArray α) (i : Nat) (v : α) : SMTArray α := a.setIfInBounds i v
```

Zero runtime cost; total; no `Fin`.

**Translation.**
- Type: `Array α` → `(Array Int σ_α)`; element sort translated through the
  normal pipeline (composes with all other families).
- `SMTArray.get a i` → `(select a i)`; `SMTArray.set a i v` →
  `(store a i v)`. Both registered opaque (never unfolded).
- Element qualifier (when present) lifted pointwise:
  `(forall ((i Int)) (@isElem (select a i)))`.
- Concrete literals `#[a, b, c]` with concrete spine and literal elements →
  `store` chains; otherwise an uninterpreted constant.

**Documented limitations.**
- No size/length modeling; SMT arrays are total over `Int`. Lean's `getD`
  returns `default` out of bounds; SMT `select` returns an unconstrained
  in-sort value. Over-approximation in the safe direction (claims
  depending on OOB `default` values yield spurious counterexamples, never
  false proofs).
- Equality at `SMTArray` type stays SMT-extensional (over-approximate);
  faithful equality is Vector's job.

---

## Phase 3 — `UInt8/16/32/64`, `Int8/16/32/64`, `USize/ISize`

**Representation:** all are Lean structures over BitVec (`UInt8` wraps
`BitVec 8`; `Int8` wraps `UInt8`; `ISize` wraps `USize`). The wrappers are
**erased**: all twelve types → the underlying `(_ BitVec w)`. No new
sorts, no qualifiers.

**Wrapper erasure:** constructors/projections (`UInt8.mk`, `.toBitVec`,
`.ofBitVec`, `Int8.toUInt8`, `.ofUInt8`, …) → identity. Literals
(`UInt8.ofNat 5` and whnf `UInt8.mk (BitVec.ofFin …)`) → `(_ bv5 8)`.

**Ops** delegate to the Phase-1 table:
- `add/sub/mul/and/or/xor/not/neg/shifts` → identical SMT ops for signed
  and unsigned (two's complement).
- `UInt*.div/mod` → `udiv` wrapper / `bvurem` (Lean div-by-zero = 0
  matches the wrapper).
- `Int*.div/mod` → `sdiv`/`smod` wrappers.
  **Implementation-phase verification task:** confirm per-op which BitVec
  primitive each `Int*` op unfolds to in the current toolchain (T-division
  vs F-division naming has shifted across Lean versions).
- Comparisons: `UInt*` → `bvult/bvule`; `Int*` → `bvslt/bvsle`.
- Conversions: widening unsigned → `(_ zero_extend k)`; widening signed →
  `(_ sign_extend k)`; narrowing → `(_ extract (w−1) 0)`; same-width
  reinterpretation (`UInt8.toInt8`) → identity. `toNat`/`toInt` → error
  (non-goal).

**USize/ISize width:** Lean option `blaster.usizeWidth : Nat := 64`,
validated ∈ {32, 64}, read once into the translation env. The chosen
width is recorded in the query log. Caveat (documented): a discharged
goal certifies the property for that width only; platform-generic code
should be checked at both widths.

**Optimizer:** folding for literal UInt/Int arithmetic (own module or
extension of `OptimizeBitVec.lean`), without round-tripping through
BitVec terms.

**Known limitations (Phase 3).**

- **Negative `USize`/`ISize` literals** (e.g. `(-1 : ISize)`) are not
  supported. They elaborate through `BitVec.ofNat System.Platform.numBits v`
  whose width argument is the opaque platform projection
  `System.Platform.getNumBits ()` — never a `Nat` literal — so
  `translatePlatformBvLit?` does not recognize the form. Positive
  `USize`/`ISize` literals (e.g. `(42 : USize)`) and all fixed-width
  negative literals (e.g. `(-5 : Int8)`) work correctly. Fails safe:
  produces a clean "non-literal width" error rather than a wrong translation.
- **`toNat`/`toInt`/`toFin` on BitVec-family values** produce an actionable
  error: "conversion out of the fixed-width domain … is not supported (see
  Non-Goals); reason over the fixed-width value directly". This covers
  `BitVec.toNat`, `BitVec.toInt`, and `BitVec.toFin` when they appear as
  the head of a top-level application. Note: `BitVec.toNat` used internally
  as a shift-amount expression (e.g. `x <<< y` with `y : BitVec w`) is
  consumed by `translateBitVecShift` before this check and continues to work.

---

## Phase 4 — `Vector α n`

**Representation:** `Vector α n` (Lean core: `Array α` + size proof) with
literal `n` → same sort as `SMTArray α`, i.e. `(Array Int σ_α)`, but with
the length statically known to the translator. Non-literal `n` → error.

**Ops.**
- `Vector.get v i` (`i : Fin n`) → `(select v i)`; `Fin n` has a literal
  bound here, so Phase 2 supplies the index sort + range qualifier.
- `v[i]` / `getElem` (`i : Nat` + proof) → `(select v i)`, proof dropped.
- `Vector.set v i x` → `(store v i x)`.
- `Vector.push v x` → `(store v n x)` (legal because `n` is literal).
- `Vector.replicate n x` → `((as const (Array Int σ)) x)` (Z3 const array).
- `Vector.mk` / `.toArray` → **clean error** (see Known Limitations below).
- Literal `#v[a, b, c]` → folded by the optimizer to a constant array;
  equality and falsification both work correctly (e.g. `#v[1,2,3] = #v[1,2,4]`
  → ❌ Falsified). `store` chain translation is not needed.
- `map/foldl/zipWith/…` → non-goal; these unfold during optimization and
  transitively hit the `Vector.mk` error (no separate arm needed).
  `append` → deferred.

**Equality (the key nuance).** Lean equality on `Vector α n` is
element-wise over `[0, n)`; SMT array equality is extensional over all of
`Int` — extensional translation would wrongly distinguish Lean-equal
vectors. Equality at a Vector type is therefore intercepted and translated
**pointwise**: an unrolled conjunction
`(and (= (select v 0) (select w 0)) …)` for `n ≤ 16`, a bounded `forall`
otherwise. Faithful in both directions.

**Known Limitations (Phase 4).**

- **`Vector.mk` and `.toArray` are clean errors.** The original spec planned
  these as identity (drops to `SMTArray` semantics). This was superseded by
  Phase 2, which made raw `Array α` an opaque SMT datatype with a distinct
  sort from `Vector α n`'s `(Array Int σ)`. A `Vector.mk`/`.toArray` round-trip
  would cross incompatible encodings. Both are now rejected with an actionable
  error: `"concrete Vector construction/unwrapping … not supported (crosses the
  array-theory and opaque-Array encodings); use Vector get/set/push/replicate"`.
  Two interception points: `translateVectorUnsupported?` in `translateApp`
  (for `Vector.mk`/`Vector.toArray` as `Expr.const`) and a guard in
  `translateProj` (for `v.toArray` dot-notation, which elaborates as `Expr.proj`).

- **`BEq` (`==`) not supported.** `v == w` unfolds to `Vector.toArray` and
  hits the above error. Use propositional `=` instead, which IS faithful
  (intercepted and translated pointwise as above).

- **Higher-order ops (`map`, `foldl`, `zipWith`, …) not supported.** These
  unfold during optimization and transitively trigger the `Vector.mk` clean
  error. The message is `"concrete Vector construction/unwrapping (Vector.mk)
  is not supported"` — the Vector.map arm would be dead (pre-unfolded), so
  no separate arm exists. Documented here for user awareness.

- **`#v[…]` literals with non-constant elements are not supported.** Pure
  literal vectors (e.g. `#v[1,2,3] : Vector Int 3`) fold correctly. A `#v[]`
  containing free variables does not have a `store`-chain translator and hits
  the `Vector.mk` error.

**Qualifier:** for qualified element sorts:
`(forall ((i Int)) (=> (and (<= 0 i) (< i n)) (@isElem (select v i))))`.

---

## Error Handling

Every unsupported construct produces a specific error naming the construct
and the supported alternative:

| Construct | Error guidance |
|---|---|
| `BitVec n`, variable `n` | not supported; use a literal width |
| Variable `Nat` shift/rotate amount | use a BitVec shift amount |
| `Fin` with dynamic bound (`Fin a.size`) | use `SMTArray` |
| `toNat`/`toInt`/`toFin` on BitVec family | unsupported (see Non-Goals); reason over the fixed-width value directly |
| Negative `USize`/`ISize` literal (e.g. `(-1 : ISize)`) | non-literal platform width; use `Int64`/`Int32` for negative signed literals |
| `Vector α n`, variable `n` | use `SMTArray` |
| `Vector.mk` / `Vector.toArray` | crosses array-theory and opaque-Array encodings; use `get`/`set`/`push`/`replicate` on symbolic Vector variables |
| Higher-order Vector ops (`map`, `foldl`, …) | non-goal; unfold to `Vector.mk` error transitively |
| `v == w` (`BEq`) on Vector | unfolds to `Vector.toArray`; use propositional `=` instead |

## Testing

One suite per phase under `Tests/Smt/`, mirroring repo structure; every
phase also re-runs the full existing suite as a regression gate.

- `SmtBitVec/`: literals; each op category; div-by-zero edge cases
  (`x.udiv 0 = 0` provable); shift ≥ width; extract/extend/rotate;
  **negative tests** for wrap-around facts that would be wrongly provable
  if BitVec leaked into the relational rules.
- `SmtFin/`: range qualifier (`∀ x : Fin 5, x.val < 5` provable); modular
  add; `Fin 0` vacuity.
- `SmtArray/`: read-over-write axioms; composition with BitVec/UInt
  elements; literal-array store chains.
- `SmtUInt/`: per-width smoke tests; signed vs unsigned division;
  cross-width conversions; USize at both width settings.
- `SmtVector/`: get/set/push; pointwise equality (provable and refutable
  directions); replicate. `Vector.mk`/`.toArray`/`BEq`/HO-ops all produce
  clean errors (not committed as test cases — error-triggering `#blaster`
  fails the build).
