# Indexed Types Phase 4 — Vector Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Translate `Vector α n` (literal `n`) as a static-length array reusing the SMTArray sort `(Array Int σ_α)` + the Fin index machinery, with **faithful pointwise equality** (the soundness-critical piece).

**Architecture:** `Vector α n` (Lean core: `structure { toArray : Array α, size_toArray : toArray.size = n }`) is a structure — survives `resolveTypeAbbrev` like SMTArray/UInt. Map it to the SMT array sort `(Array Int σ_α)` with the length statically known. `get`/`set`/`push`/`replicate` → `select`/`store`/const-array. The one genuinely new piece is **equality**: Lean's `Vector` equality is element-wise over `[0,n)`, but SMT array equality is extensional over all `Int` — using SMT `=` is UNSOUND in hypothesis position (it assumes more than Lean gives). So Vector equality is intercepted and translated as a pointwise conjunction/bounded-forall. Spec: `docs/superpowers/specs/2026-06-11-indexed-types-design.md` (Phase 4).

**Tech Stack:** Lean 4 (v4.24.0), Z3 ≥ 4.15.2, lake. **Branch:** `feat/indexed-types` (continues after Phase 3).

---

## Context for the implementer (verified against Lean 4.24 + current code)

- Build: `lake build Blaster`. One test file: `lake env lean Tests/Smt/SmtVector/<File>.lean`. Full: `LEAN_NUM_THREADS=5 lake test`. Read `✅`/`❌` lines, not the exit code. `(gen-cex: 0) (solve-result: 1)` → `✅ Expected Falsified`.
- ⚠️ Trivially-true props fold to `True`. ⚠️ `` ``Foo `` literals don't compile for nonexistent constants — discover real names in Step 2 of each task. ⚠️ After each task `git status` shows ONLY pre-existing `Tests/Smt/SmtNat/SmtNatMod.lean`; `git add` only named files; delete scratch.

### Vector representation (verified via `#print`)
`structure Vector (α) (n : Nat) where mk :: (toArray : Array α) (size_toArray : toArray.size = n)`. Two fields (Array + a Prop proof). Ops:
- `Vector.get : Vector α n → Fin n → α` (index is `Fin n` — literal n, composes with Phase 2 Fin support)
- `Vector.set : Vector α n → (i : Nat) → α → autoParam (i < n) → Vector α n`
- `Vector.push : Vector α n → α → Vector α (n+1)`
- `Vector.replicate : (n : Nat) → α → Vector α n`
- `Vector.mk : Array α → (proof) → Vector α n`; `Vector.toArray : Vector α n → Array α`
- `v[i]` → `getElem` with a bounds proof.

### Reuse from earlier phases
- **SMTArray (Phase 2):** `translateArrayType` in Quantifier.lean maps `SMTArray α` → `(Array Int σ)` with **pointwise element-qualifier lift** `(forall i, @isElem (select x i))`. Vector reuses this sort + qualifier shape (the element-qualifier lift is the SAME soundness mechanism). `selectSmt`/`storeSmt`/`storeSymbol`/`selectSymbol` in Term.lean; `SMTArray.get`/`.set` → select/store arms in `translateOpaqueFun`. The `SMTArray.ofArray`/`.toArray` CLEAN-ERROR precedent (`translateSMTArrayCtor?` in Application.lean) — Vector.mk/.toArray follow it.
- **Fin (Phase 2):** `Fin n` (literal) → `Fin_n` Int-aliased sort + `0≤x<n` qualifier; `Fin.val`/`Fin.mk` identity. `Vector.get`'s `Fin n` index translates via this.
- **Equality dispatch:** `translateEq?` in `translateApp`'s where-block (Application.lean ~1255) handles `@Eq`. Vector equality is intercepted here (or just before). `isUIntFamilyName`/`uintWidth?` helper style in Optimize/Expr.lean for type-head predicates.

### ⚠️ Forced spec deviation (from the Phase-2 SMTArray decision)
The spec says `Vector.mk`/`.toArray` → identity. That assumed the original "raw `Array` → SMT array" design. Phase 2 made raw `Array α` stay an OPAQUE DATATYPE (distinct sort) and only `SMTArray` (a structure) map to SMT array theory. So `Vector.toArray : Vector α n → Array α` crosses from the SMT-array sort to the opaque-datatype-Array sort — NOT identity. Treat `Vector.mk`/`.toArray` as CLEAN ERRORS (like `SMTArray.ofArray`/`.toArray`), and document the deviation. (A user who wants array ops should use `SMTArray`.)

## File structure

| File | Responsibility |
|---|---|
| `Blaster/Smt/Translate/Quantifier.lean` (modify) | `translateVectorType` (→ Array Int σ + elem-qualifier lift) + hook |
| `Blaster/Smt/Term.lean` (modify, maybe) | `constArraySmt` builder `((as const (Array Int σ)) x)` for replicate |
| `Blaster/Optimize/Opaque.lean` (modify) | register Vector ops opaque |
| `Blaster/Smt/Translate/Application.lean` (modify) | `translateVectorOp?` (get/set/push/replicate/getElem); pointwise `Eq`/`BEq` interception; mk/toArray/HO-op errors |
| `Tests/Smt/SmtVector/*.lean` (create) + registration | test suites |

---

## Task 1: Vector type translation

**Files:** `Blaster/Smt/Translate/Quantifier.lean`; create `Tests/Smt/SmtVector/SmtVectorSort.lean`.

- [ ] **Step 1: Write the failing test**
```lean
import Blaster

namespace Test.SmtVectorSort

/-! # Vector sort translation -/

#blaster [∀ (v : Vector Int 3), v = v]

#blaster [∀ (v : Vector (BitVec 8) 4), v = v]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (v w : Vector Int 3), v = w]
```

- [ ] **Step 2: Run, record error.** Confirm `Vector` reaches the inductive-datatype path. Note arg order: `Vector α n` = `Expr.app (Expr.app (Expr.const ``Vector) α) n` — element type is the FIRST explicit arg, length the SECOND.

- [ ] **Step 3: `translateVectorType` + hook** (`Quantifier.lean`, near `translateArrayType`). Reuse the SMTArray sort + element-qualifier-lift logic (factor a shared helper if clean, else mirror it). Element type = `Vector`'s first arg; require literal `n` (second arg, whnf'd — error otherwise). Cache on the full `Vector α n` expr; per-instance unique qualifier name (`mkFreshId`, like SMTArray). The qualifier lifts the element qualifier pointwise; OPTIONALLY bound it to `[0,n)` per the spec (`(forall i, (0≤i ∧ i<n) → @isElem (select v i))`) since n is known — but the simpler all-Int lift (as SMTArray does) is also sound. Choose one; note which.
```lean
/-- Translate `Vector α n` (literal n) to the SMT array sort `(Array Int σ_α)`,
    reusing the SMTArray element-qualifier lift. Non-literal n → error. -/
def translateVectorType (typeTranslator : Expr → TranslateEnvT SortExpr) (t : Expr) : TranslateEnvT SortExpr := do
  ... (mirror translateArrayType; elemType := t.getAppArgs[0]!; require literal n from getAppArgs[1]!) ...
```
Hook in `translateTypeAux`: `| Expr.const ``Vector _ => translateVectorType (λ a => translateTypeAux termTranslator a) t`.

- [ ] **Step 4: Run, pass.** 2 ✅ Valid + 1 ✅ Expected Falsified. Add a non-literal-`n` error check (scratch): `#blaster [∀ (n : Nat) (v w : Vector Int n), v = w → w = v]` → error mentioning non-literal length. Delete scratch.

- [ ] **Step 4b: Smoke-test pre-existing uses (cheap insurance).** Claiming a type head has broken pre-existing tests twice (Array→Issue3, UInt32→Char/BEqString). Vector is unlikely to be embedded elsewhere, but confirm STILL green before stacking later tasks: `lake env lean Tests/Optimize/OptimizeBEq/BEqString.lean` (all Success), `lake env lean Tests/FixedIssues/Issue3.lean` (3 Valid). Record. If either breaks, settle it now.

- [ ] **Step 5: Commit** `feat(vector): translate Vector α n type to SMT array sort`.

NOTE: equality `v = w` here uses SMT extensional `=` for now (Task 3 makes it pointwise). The Task-1 tests are reflexive (`v = v`, always fine) and a falsification (`v = w` — extensional ≠ is fine to falsify). So Task 1 is correct standalone; Task 3 fixes the soundness-critical hypothesis-position case.

---

## Task 2: get / set / push / replicate / getElem

**Files:** `Blaster/Optimize/Opaque.lean`, `Blaster/Smt/Translate/Application.lean`, maybe `Blaster/Smt/Term.lean` (const-array builder); create `Tests/Smt/SmtVector/SmtVectorOps.lean`.

- [ ] **Step 1: Write the failing test**
```lean
import Blaster

namespace Test.SmtVectorOps

/-! # Vector get/set/push/replicate -/

-- read-over-write same index (Fin index)
#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get 0 = x]

-- read-over-write different index
#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get 1 = v.get 1]

-- getElem (Nat index + proof)
#blaster [∀ (v : Vector Int 5) (x : Int), (v.set 2 x)[2] = x]

-- push extends; the pushed element is readable at index n
#blaster [∀ (v : Vector Int 3) (x : Int), (v.push x).get 3 = x]

-- replicate: every element equals the fill value
#blaster [∀ (x : Int) (i : Fin 4), (Vector.replicate 4 x).get i = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (v : Vector Int 5) (x : Int), (v.set 0 x).get 1 = x]
```
(Adjust phrasings that don't elaborate — e.g. `(v.push x).get 3` needs the `Fin 4` literal `3`; `v[2]` getElem needs a provable bound. Note any change.)

- [ ] **Step 2: Run, record surviving constants + arg layouts** for `Vector.get` (Fin index), `Vector.set` (Nat index + autoParam proof), `Vector.push`, `Vector.replicate`, `getElem`/`Vector.getElem`. Note that `Vector.get`'s `Fin n` index translates via Phase 2 (Fin.val identity → Int).

- [ ] **Step 3: Register opaque** (observed names): `Vector.get`, `Vector.set`, `Vector.push`, `Vector.replicate`, the getElem form.

- [ ] **Step 4: Add `translateVectorOp?`** (`translateApp` where-block):
  - `Vector.get v i` → `(select v (translate i))` — `i : Fin n` translates to its Int value (Phase 2). args drop implicits.
  - `v[i]` / getElem → `(select v (translate i))`, bounds proof dropped.
  - `Vector.set v i x [proof]` → `(store v (translate i) (translate x))`, proof dropped.
  - `Vector.push v x` → `(store v (translate n) (translate x))` where `n` is the literal length from the Vector's type (read from the type of `v` / the implicit n arg; must be literal). Emits a store at index n.
  - `Vector.replicate n x` → a constant array `((as const (Array Int σ)) x)`. Add a `constArraySmt (sort : SortExpr) (x : SmtTerm)` builder in Term.lean emitting `((as const sort) x)` (check the existing `asArraySmt`/`underSymbol` idiom for how indexed/`as` identifiers render; `(as const (Array Int σ))` is an `as`-qualified identifier applied to `x`). σ is the array sort of the result type.
  Reuse `selectSmt`/`storeSmt`. For get/set, prefer routing through `getOpaqueSmtEquivFun f selectSymbol`/`storeSymbol` + `createAppN` IF the implicit/proof args filter cleanly (as SMTArray did); the `Fin` index and `autoParam` proof may need the custom arm instead — verify and choose.

- [ ] **Step 5: Run, pass.** 5 ✅ Valid + 1 ✅ Expected Falsified. Composition check: `Vector (BitVec 8) n` get/set (element qualifier composes).

- [ ] **Step 6: Commit** `feat(vector): get/set/push/replicate/getElem to array theory`.

---

## Task 3: Pointwise equality (FAITHFULNESS/COMPLETENESS — full two-stage review)

Lean `Vector α n` equality is element-wise over `[0,n)`. SMT array `=` is extensional over ALL `Int`. **This is an incompleteness, not an unsoundness** (worked out carefully — read this before implementing):

- Every Vector op in scope (`get`/`getElem` on `Fin n`, `set` with `i<n`, `push` clobbering index n, `replicate`) observes ONLY indices in `[0,n)`. Call any such observation `Q`.
- **Hypothesis position** (`∀ v w, v = w → Q`): given a pointwise counterexample (v,w agreeing on `[0,n)`, differing outside, with ¬Q), set `w := v` outside `[0,n)` — this changes nothing Q observes (Q only reads `[0,n)`), yielding an *extensional* counterexample with the same ¬Q. So extensional and pointwise give the SAME validity. **No false proof here.**
- **Conclusion position** (`∀ v w, P(v,w) → v = w`): pointwise → Valid when P forces agreement on `[0,n)`; extensional → **Falsified** with a spurious counterexample differing OUTSIDE `[0,n)`. Extensional reports a *true* theorem as Falsified — incompleteness (the spec's "wrongly distinguish Lean-equal vectors").

So pointwise equality restores FAITHFULNESS/COMPLETENESS (proves true equalities that extensional spuriously refutes); it is sound either way but spec-mandated for faithfulness. Implement it regardless.

**Files:** `Blaster/Smt/Translate/Application.lean`; create `Tests/Smt/SmtVector/SmtVectorEq.lean`.

- [ ] **Step 1: Write the failing test.** The load-bearing case is the **conclusion-position extensionality test** (Valid under pointwise, Falsified under extensional — the genuine discriminator):
```lean
import Blaster

namespace Test.SmtVectorEq

/-! # Vector pointwise equality (faithful over [0,n)) -/

-- reflexive
#blaster [∀ (v : Vector Int 3), v = v]

-- congruence: equal vectors agree at every index
#blaster [∀ (v w : Vector Int 3), v = w → v.get 0 = w.get 0]

-- THE DISCRIMINATOR: agreeing at ALL (literal) indices ⇒ equal (n=2).
-- Valid under pointwise eq; FALSIFIED under extensional eq (spurious cex
-- differing at some index ≥ 2). This is what proves the interception works.
#blaster [∀ (v w : Vector Int 2), v.get 0 = w.get 0 → v.get 1 = w.get 1 → v = w]

-- agreeing at index 0 ONLY must NOT prove equality (index 1 can differ) →
-- Falsified under BOTH pointwise and extensional (NOT a discriminator, but a
-- correctness sanity check that eq isn't degenerately true).
#blaster (gen-cex: 0) (solve-result: 1) [∀ (v w : Vector Int 2), v.get 0 = w.get 0 → v = w]
```

- [ ] **Step 2: Run, observe — confirm the discriminator empirically.** Without interception, `v = w` translates to SMT extensional `=`. Run the suite and CHECK: the discriminator (agree-at-0-AND-1 ⇒ v=w, n=2) should come back **Falsified under the current extensional `=`** (spurious out-of-range cex) — that empirically confirms both the defect and that pointwise will fix it (Step 4 flips it to Valid). The reflexive/congruence tests pass under both. The agree-at-0-only test Falsifies under both (sanity, not discriminator). Do NOT hunt a hypothesis-position false proof — per the analysis above none exists; if you think you found one, STOP and surface it for reconciliation (it would mean the analysis is wrong).

- [ ] **Step 3: Intercept Vector equality.** In `translateEq?` (and the `BEq.beq` path / `translateRelational?` for `BEq`), detect when the equated type is `Vector α n` (literal n): emit pointwise
  `(and (= (select v 0) (select w 0)) … (= (select v (n-1)) (select w (n-1))))` for `n ≤ 16`;
  for `n > 16`, a bounded `forall ((i Int)) (=> (and (<= 0 i) (< i n)) (= (select v i) (select w i)))`.
  `n = 0` → `true` (empty vectors trivially equal). Read n from the `Eq`'s type argument (args[0] for `@Eq α a b`). Translate v, w to their array terms, then build the conjunction with `selectSmt v #[natLitSmt k]`.

- [ ] **Step 4: Run, pass.** After interception: reflexive ✅ Valid, congruence ✅ Valid, **the discriminator (agree-at-0-AND-1 ⇒ v=w, n=2) flips to ✅ Valid** (was Falsified under extensional — this is the proof pointwise works), and agree-at-0-only ✅ Expected Falsified. Add an n>16 test to exercise the bounded-forall branch (e.g. `∀ (v w : Vector Int 20), (∀ i : Fin 20, v.get i = w.get i) → v = w` → Valid) and an n=0 test (`∀ (v w : Vector Int 0), v = w` → Valid, empty vectors trivially equal).

- [ ] **Step 5: Commit** `feat(vector): pointwise equality (faithful over [0,n))`.

---

## Task 4: mk/toArray/literals/HO-op errors + registration + regression

**Files:** `Blaster/Smt/Translate/Application.lean` (clean errors); create `Tests/Smt/SmtVector/SmtVectorErr.lean`, `Tests/Smt/SmtVector.lean`; modify `Tests/Smt.lean`.

- [ ] **Step 1: Clean errors for unsupported constructs.** Add a `translateVectorUnsupported?` arm (mirror `translateSMTArrayCtor?`) that throws actionable errors for:
  - `Vector.mk` / `Vector.toArray` → "concrete Vector construction/unwrapping ({n}) is not supported (crosses the array-theory / opaque-Array encodings); use Vector ops (get/set/push/replicate) on symbolic Vector variables" (the forced spec deviation — see plan header).
  - `Vector.map`/`Vector.foldl`/`Vector.zipWith`/etc. (the HO ops that reach translation) → "higher-order Vector op ({n}) is not supported (Non-Goal)". (Only add the ones that actually reach translation — discover in Step 2; many may be recursive defs that error elsewhere already.)
  - `#v[...]` literals → for now, a clean error OR a store-chain over a const-array base if cheap (spec prefers store-chains; if deferring, error cleanly and document). Discover the `#v[...]` elaborated form first.

- [ ] **Step 2: Write the error/limitation test** `Tests/Smt/SmtVector/SmtVectorErr.lean` — use `(solve-result: ...)` only for things that translate; for unsupported constructs, there's no `#blaster` assertion that passes (they error at elaboration/translation). Instead, document the limitations in comments and include any constructs that DO have defined safe behavior. If a clean error can't be asserted via `#blaster`, write a comment citing the spec Non-Goal and verify the error manually (scratch, delete). Do NOT leave a `#blaster` that errors in a committed test file (it would fail the suite). 

- [ ] **Step 3: Register the suite.** Create `Tests/Smt/SmtVector.lean` importing `SmtVectorEq`, `SmtVectorOps`, `SmtVectorSort` (alphabetical; add SmtVectorErr only if it contains passing `#blaster`s). Add `import Tests.Smt.SmtVector` to `Tests/Smt.lean` (alphabetical).

- [ ] **Step 3b: Case-collision check (macOS).** The repo has both a lowercase `tests/` dir and the uppercase `Tests/` lib, and new test files have landed under the wrong case before (Phase 2 needed a stash/amend dance). After creating the SmtVector tree, confirm the new files are git-tracked under UPPERCASE `Tests/`: `git ls-files | grep -i smtvector` must show `Tests/Smt/SmtVector/...` (capital T). If any appears as lowercase `tests/...`, re-add with the correct case before committing.

- [ ] **Step 4: Full regression.** `lake build Blaster && LEAN_NUM_THREADS=5 lake test` — zero `❌`/`error:`. All prior suites (BitVec/Fin/SMTArray/UInt/Int/Nat/Issue3/BEqString) stay green.

- [ ] **Step 5: Stale-comment sweep + commit.** Update the spec's Phase-4 section to reflect the `Vector.mk`/`.toArray` clean-error deviation (was "identity").
```bash
git add <changed files>
git commit -m "feat(vector): clean errors for mk/toArray/HO-ops; register SmtVector suite"
```

---

## Self-review checklist (after writing, before execution)

- Spec Phase 4 coverage: Vector→array sort ✅ T1; non-literal n → error ✅ T1; get (Fin)/getElem/set/push/replicate ✅ T2; **pointwise equality** (n≤16 unroll, n>16 bounded-forall, n=0 → true) ✅ T3; element-qualifier lift ✅ T1; mk/toArray → clean error (deviation from spec "identity", forced by Phase-2 raw-Array decision — documented) ✅ T4; HO ops → error ✅ T4; `#v[...]` literals → store-chains or documented error ✅ T4.
- Soundness: the equality discriminator (`agree at index 0 only ⇏ equal`, n=2) MUST be Falsified (T3) — proves pointwise, not extensional, not single-index. Element-qualifier composition with BitVec/Fin elements.
- Reuse: Vector shares SMTArray's sort + qualifier-lift and Fin's index translation — verify no duplication beyond what's clean; factor a shared array-sort helper if T1 finds it natural.

## Out of scope / deferred
`Vector.append` (encodable as n stores; revisit on demand); `#v[...]` store-chains if deferred to a clean error; higher-order ops (map/foldl/zipWith) — all documented Non-Goals. This is the LAST phase of the indexed-types spec.


