# Sound `SMTArray` Model (Spec 1 of 4)

**Date:** 2026-06-17
**Branch:** `feat/indexed-types`
**Status:** Approved (design)

## Background

While investigating a raw-`Array` test (`tests/Smt/SmtUInt/Memory.lean`) we found a
**soundness bug**: blaster proves Lean-false theorems about `SMTArray`.

```lean
-- FALSE in Lean (counterexample: a = ⟨#[]⟩, i = 0, v = 99 → default = 99),
-- but blaster reports "✅ Valid":
theorem t (a : SMTArray UInt32) (i : Nat) (v : UInt32) : (a.set i v).get i = v
```

Root cause: `SMTArray`'s Lean semantics are **bounds-checked**

```lean
SMTArray.get a i = a.toArray.getD i default      -- out of bounds → `default`
SMTArray.set a i v = ⟨a.toArray.setIfInBounds i v⟩ -- out of bounds → no-op (array unchanged)
```

but the translator maps `get`/`set` to **unconditional** SMT array-theory `select`/`store`
(`Blaster/Smt/Translate/Application.lean:414-415`, via `getOpaqueSmtEquivFun`).
The model has no notion of size, so it treats every access as in-bounds.

### Blast radius (committed tests that pass via the unsound path)

False-in-Lean but currently expected to be `Valid`:

- `Tests/Smt/SmtArray/SmtArrayOps.lean:9`  — `(a.set i v).get i = v`
- `Tests/Smt/SmtArray/SmtArrayOps.lean:13` — `((a.set i v).set i w).get i = w`
- `Tests/Smt/SmtArray/SmtArrayOps.lean:15` — BitVec 8 variant of `:9`
- `Tests/Smt/SmtArray/SmtArrayQualifier.lean:28` — same shape as `:9`

Sound and unaffected: `SmtArrayOps:11` (`i ≠ j → (a.set i v).get j = a.get j`),
`:17` (cex), `:28`-Ops (cex). `Vector` is **sound** already — its `set` carries a proof
`i < n` and the length lives in the type, so every access is in-bounds and the total-array
model matches.

(`tests/` and `Tests/` are the same files on this case-insensitive filesystem.)

## Scope

This is **Spec 1 of 4** (decomposition agreed with user):

1. **(this spec)** Faithful `SMTArray` model (size + out-of-bounds + default) → fixes the
   soundness bug and the 4 false tests.
2. Raw `Array` op support (`get!`/`set!`/`size`) onto the same model.
3. Structure proof-field → SMT assumption (so invariants like `cells.size = 200` are usable).
4. Fix `Memory.lean` + make the motivating test prove end-to-end.

Specs 2–4 are **out of scope here.** This spec must not regress `Vector`.

## Design

### Representation — datatype pair (Decision 1)

Represent each distinct `SMTArray α` as a **monomorphic SMT datatype**, one per element
sort `σ` (mirrors the existing per-σ fresh-id qualifier pattern in `translateArrayType`):

```
(declare-datatype @SmtArr_v ((@smtarr_v (@data_v (Array Int σ)) (@size_v Int))))
```

- Sort of `SMTArray α` becomes `@SmtArr_v` (was `(Array Int σ)`).
- `@data_v` : the underlying total array `(Array Int σ)`.
- `@size_v` : the array's size, an `Int`.

Size travels **with the value**, so it threads correctly through `ite`, quantified array
variables, function results, and equality — the reason side-companion / uninterpreted-function
alternatives were rejected (they cannot answer "what is the size of `ite c a b`?").

Datatypes are already emitted by the codebase (`declare-datatype` for custom structures) and
the logic is `ALL`, so this is feasible.

### Qualifier (`@isArray_v`)

The qualifier for a quantified `SMTArray` variable `x` becomes:

```
(define-fun @isArray_v ((@x @SmtArr_v)) Bool
  (and (>= (@size_v @x) 0)
       (forall ((@i Int)) (@isElem (select (@data_v @x) @i)))))
```

- `(>= (@size_v @x) 0)` — sizes are non-negative.
- The element-qualifier lift is preserved (unchanged soundness requirement), now reading
  through `@data_v`.

### Operations (Decision 1, cont.)

`get`/`set` stop being direct symbol mappings and become a **custom translator**
(`translateSMTArrayOp?`) emitting bounds-aware terms:

```
get a i  →  (ite (and (<= 0 i) (< i (@size_v a)))
                 (select (@data_v a) i)
                 DFLT_σ)

set a i v → (@smtarr_v
              (ite (and (<= 0 i) (< i (@size_v a)))
                   (store (@data_v a) i v)
                   (@data_v a))
              (@size_v a))                 -- size preserved (matches setIfInBounds)

size a   →  (@size_v a)
```

`SMTArray.set`'s index is a `Nat` (≥ 0 by type), so the `(<= 0 i)` guard is always true for
real terms; it is emitted for faithfulness and is cheap for Z3.

### Out-of-bounds value `DFLT_σ` (Decision 2)

Declare one **unconstrained constant per element sort**:

```
(declare-const @dflt_σ σ)
(assert (@isElem @dflt_σ))     -- must satisfy the element qualifier
```

- **Sound:** over-approximates Lean's specific `default` (Lean's `default` is one admissible
  value of `@dflt_σ`); SMT-valid ⇒ Lean-valid.
- The `(@isElem @dflt_σ)` assertion keeps `SMTArray Nat`-style element qualifiers intact
  (oob value stays ≥ 0), avoiding the previously-fixed element-qualifier-lift trap.
- Computing the **exact** Lean `default` is **deferred** — an incompleteness (only matters for
  proving theorems that read the exact default value out of bounds), not an unsoundness.

### `SMTArray.size`

Add to `Blaster/SmtArray.lean`:

```lean
def SMTArray.size (a : SMTArray α) : Nat := a.toArray.size
```

Translated to `(@size_v a)`. Registered as opaque in `Blaster/Optimize/Opaque.lean` (alongside
`SMTArray.get`/`SMTArray.set`).

## Test changes (Decision 3)

For each false-but-Valid test, provide **two** corrected forms:

- **Positive (proves):** add an explicit in-bounds hypothesis, e.g.
  `∀ a i v, i < a.size → (a.set i v).get i = v` — demonstrates the array theory still works in
  the sound case.
- **Negative (cex):** keep the unguarded statement, now expected `(solve-result: 1)` /
  countermodel — demonstrates blaster correctly rejects the false form.

Concretely affects `SmtArrayOps.lean:9/13/15` and `SmtArrayQualifier.lean:28`.
`:11`, `:17`, `:28`-Ops are already sound and stay as-is.

## Files touched

- `Blaster/SmtArray.lean` — add `SMTArray.size`.
- `Blaster/Smt/Term.lean` — datatype constructor/selector symbols (`@smtarr`, `@data`, `@size`),
  `@dflt` constant helper, possibly an `smtArrSort`/datatype helper.
- `Blaster/Smt/Env.lean` — declare the per-σ datatype + `@dflt` constant + its qualifier assertion.
- `Blaster/Smt/Translate/Quantifier.lean` — `translateArrayType` emits the datatype + new qualifier
  (`@size ≥ 0` + element lift through `@data`). **Do not touch `translateVectorType`.**
- `Blaster/Smt/Translate/Application.lean` — replace the `SMTArray.get`/`set` symbol mappings with a
  bounds-aware `translateSMTArrayOp?`; add `SMTArray.size`.
- `Blaster/Optimize/Opaque.lean` — register `SMTArray.size`.
- `Tests/Smt/SmtArray/SmtArrayOps.lean`, `SmtArrayQualifier.lean` — corrected positive + cex forms.

## Testing strategy

1. **Regression (soundness):** the 4 false statements now report `(solve-result: 1)` / cex.
2. **Positive:** bounds-guarded versions of all 4 prove `Valid`.
3. **Preserved-sound:** `SmtArrayOps:11`, `:17`, `:28`-Ops unchanged and still pass.
4. **Vector unaffected:** full `SmtVector` / `Tests` suite green (no `translateVectorType` change).
5. **No Z3 errors:** datatype + `@dflt` declarations are well-formed under `ALL` and emitted once
   per element sort (no duplicate `declare-datatype`/`declare-const`).

## Non-goals

- Raw `Array` support (Spec 2).
- Structure proof-field invariant extraction (Spec 3).
- The end-to-end `Memory.lean` proof (Spec 4).
- Exact Lean `default` value for oob reads (faithful counterexamples) — deferred.
- Any change to `Vector` semantics or representation.
