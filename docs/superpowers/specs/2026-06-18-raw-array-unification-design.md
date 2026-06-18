# Raw `Array` Unification (Spec 2 of 4)

**Date:** 2026-06-18
**Branch:** `feat/indexed-types`
**Status:** Approved (design)
**Builds on:** Spec 1 (`2026-06-17-sound-smtarray-model-design.md`) — the sound `SMTArray` datatype-pair model.

## Goal

Make raw `Array α` support symbolic `get!`/`set!`/`size` by routing it to the **same**
datatype-pair SMT model Spec 1 built for `SMTArray` — so `tests/Smt/SmtUInt/Memory.lean`
(symbolic `Array MemoryCell` field, indexed via `a[i.val]!` / `a.set! i v`) becomes
translatable, and `Array`/`SMTArray` share one sound encoding.

This is the "full unification" path (user-chosen over the minimal selective-routing
alternative): ALL raw `Array α` reaching SMT uses the array-theory datatype-pair sort.

## Background (verified)

- Raw `Array α` currently falls through `translateTypeAux` → `translateNonOpaqueType`
  (generic inductive datatype `Array.mk : List α → Array α`). Symbolic indexing fails
  because `a[i]!` (elaborates to polymorphic `getElem!`) is unfolded by the **translator**
  to `Array.get` carrying `Fin a.size`, and `a.size` → `List.length` via `List.rec` →
  `translateFinType: Fin with non-literal bound` error. (This is the error that started
  the whole task.)
- `SMTArray.get`/`.set`/`.size` are **definitionally** `Array.get!`/`set!`/`size`
  (`Blaster/SmtArray.lean`). So the bounds-aware terms `translateSMTArrayOp?` already
  builds (Spec 1) are exactly what raw `Array` ops need — no new SMT semantics.
- Concrete arrays/ByteArrays are **reduced by the optimizer before SMT**: a probe of
  `(l1 != l2) = true` over concrete `ByteArray` lists emitted **zero** array SMT.
  `Issue3` (3×), `Issue11`, `Issue16` are all green today and do not push raw `Array`
  through the SMT array path. (`only-optimize: 1` on Issue2/Issue4 means they never
  translate to SMT at all.)
- There is **no** `getElem` normalization in the codebase today.
- Logic is `ALL`; datatypes already emitted (Spec 1).

## Decomposition

### Spec 2a — symbolic routing (banks the `Memory.lean` goal)

1. **Type routing.** In `translateTypeAux` (`Blaster/Smt/Translate/Quantifier.lean:1503+`),
   add an arm so `Expr.const ``Array _` routes to `translateArrayType` (the Spec-1
   datatype-pair path), exactly as `Blaster.SMTArray` does. `translateArrayType` already
   reads the element type via `t.appArg!`, which is `α` for both `SMTArray α` and `Array α`
   — so it generalizes with no structural change. `Array Int` and `SMTArray Int` get
   **distinct** cache entries / datatypes (distinct Lean types, distinct Expr keys) — correct;
   they are not interchangeable, and `SMTArray.ofArray`/`.toArray` crossing is already an error.
   **Must run AFTER** the `Blaster.SMTArray`/`Vector` arms (those are more specific) and
   BEFORE `translateNonOpaqueType` (the old opaque-datatype fallback).

2. **`getElem!` normalization (approach A — the crux).** Add an optimizer rewrite
   (mirroring the `Nat.beq → ==` normalization in `Blaster/Optimize/Rewriting/OptimizeNat.lean`,
   gated on `normalizeFunCall`): when the container of `getElem!`/`getElem?`/`getElem` has
   type `Array _`, rewrite to the Array-named op:
   - `getElem! a i _` (Array) → `Array.get! a i`
   - `getElem? a i`   (Array) → `Array.get? a i`
   - `getElem a i h`  (Array) → `Array.get a ⟨i, h⟩` is the Fin-indexed total get; for SMT
     it maps to an in-bounds `select` (proof dropped). **2a scope:** handle `getElem!`
     (the `Memory.lean` read); `getElem`/`getElem?` only if they appear — otherwise defer.
   The rewrite fires ONLY for `Array` containers; `List`/other `getElem!` is untouched and
   continues through its existing path.

3. **Opacify the Array-named ops** so the translator does not unfold them to `Fin a.size`.
   Add to `opaqueFuns` in `Blaster/Optimize/Opaque.lean` (next to `SMTArray.get`/`set`/`size`):
   `Array.get!`, `Array.getD`, `Array.set!`, `Array.setIfInBounds`, `Array.size`
   (and `Array.get?` if used by the normalization). These are Array-specific → safe.

4. **Intercept in `translateApp`.** Add `translateRawArrayOp?` (returns `Option SmtTerm`),
   dispatched alongside `translateSMTArrayOp?`, reusing the SAME term-building helpers
   (`smtSelectorApp`/`smtArrCtorApp`/the `inBounds` predicate/`@dflt`). It obtains the
   `Array α` type via `inferTypeEnv` of the array argument (cache-key match, as in Spec 1)
   and emits:
   - `Array.get! a i` / `Array.getD a i d` → `(ite (inBounds a i) (select (data a) i) D)`
     where `D` = `@dfltSMTArray_v` for `get!`, or the **translated explicit default `d`** for `getD`.
   - `Array.set! a i v` / `Array.setIfInBounds a i v` → `(mk (ite (inBounds a i) (store (data a) i v) (data a)) (size a))` (size preserved).
   - `Array.size a` → `(size a)`.
   Exact argument layouts (implicit `α`/instance args included via `withApp`) are resolved
   against elaborated forms during implementation (the implementer must confirm each op's
   arg positions, as in Spec 1 Task 2).

5. **Tests.** Add `Tests/Smt/SmtArray/SmtRawArray.lean` mirroring the `SMTArray` op tests
   but on raw `Array`:
   - cex: `∀ (a : Array Int) (i : Nat) (v : Int), (a.set! i v)[i]! = v` → countermodel.
   - positive: `∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.set! i v)[i]! = v` → Valid.
   - `Array.getD` default-on-oob: `∀ (a : Array Int) (i : Nat) (d : Int), a.size ≤ i → a.getD i d = d` → Valid (uses the explicit `d`).

6. **Full regression gate.** Run `lake test`. Issue3/11/16, the `SmtArray`/`SmtVector`
   suites, and everything else must stay green (pre-existing `SmtFinOps:13` excepted).
   **A green suite proves the optimizer reduces all concretes before SMT** (the load-bearing
   assumption) — measured against the real tests, not a probe. Any regression names exactly
   which concrete reaches SMT → scopes 2b.

### Spec 2b — concrete `Array.mk`/literal store-chains (conditional)

Only built if 2a's suite run shows a concrete `Array` reaching SMT (e.g. a concrete array
indexed symbolically, compared to a symbolic one, or nested in a symbolic structure that
survives optimization). Encode concrete construction as a store-chain over the datatype pair:
- `#[a,b,c]` / `Array.mk [a,b,c]` / `List.toArray [a,b,c]` →
  `(mk (store (store (store @dflt 0 a) 1 b) 2 c) 3)` (size = literal length).
- `Array.empty` / `#[]` → `(mk @dflt 0)`; `Array.push a x` → `(mk (store (data a) (size a) x) (+ (size a) 1))`.
Elements are translated as `Expr`s (no kernel `String.toList`/`toUTF8` evaluation → the
Lean 4.24 kernel-`Char` bug is not triggered). If 2a's suite is fully green with no concrete
reaching SMT, **2b is empty (YAGNI)** and we record that.

## Files touched (2a)

- `Blaster/Smt/Translate/Quantifier.lean` — `translateTypeAux` `Array` arm → `translateArrayType`.
- `Blaster/Optimize/Rewriting/` (new or existing rewrite module) — `getElem!`-on-`Array` → `Array.get!` normalization; dispatch hook.
- `Blaster/Optimize/Opaque.lean` — opacify `Array.get!`/`getD`/`set!`/`setIfInBounds`/`size`.
- `Blaster/Smt/Translate/Application.lean` — `translateRawArrayOp?` + dispatch.
- `Tests/Smt/SmtArray/SmtRawArray.lean` — new tests.

## Non-goals

- The `Memory.lean` end-to-end proof (needs Spec 3 structure-invariant extraction + Spec 4).
- Structure proof-field → SMT assumption (Spec 3).
- Removing `SMTArray` (it remains; raw `Array` now shares its model).
- `Vector` changes (already sound).
- 2b unless 2a's suite run proves a concrete reaches SMT.

## Risks

- **`getElem!` normalization must fire only for `Array`** — a too-broad rule would reroute
  `List`/other indexing. Gate strictly on container type. (Tests: Issue suite + any List tests.)
- **Memory note caveat:** the memory records that routing raw `Array` to array-theory once
  broke `Issue3` (concrete `Array.mk` → unmapped constant → Z3 crash). The 2a suite run is
  the authoritative check; if `Issue3` regresses, 2b (store-chains) is required, not optional.
- Cache-key match between type routing (writer) and `translateRawArrayOp?` (reader) — same
  `inferTypeEnv`-of-array-arg invariant as Spec 1; document it.
