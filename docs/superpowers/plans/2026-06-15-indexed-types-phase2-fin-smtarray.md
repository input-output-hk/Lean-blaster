# Indexed Types Phase 2 — Fin + SMTArray Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Translate `Fin n` (literal bound) to an Int-aliased `Fin_n` SMT sort with a `0 ≤ x < n` range qualifier, and provide a Nat-indexed `SMTArray α` mapping to the SMT array theory (`select`/`store`).

**Architecture:** Same four seams as Phase 1 (type translation in `Quantifier.lean`, op translation in `Application.lean`, opacification in `Optimize/Opaque.lean`, optional folding in `Optimize/`). Fin mirrors the existing `Nat`-over-`Int` qualifier scheme; SMTArray adds a tiny runtime library plus array-theory translation. Spec: `docs/superpowers/specs/2026-06-11-indexed-types-design.md` (Phase 2 section).

**Tech Stack:** Lean 4 (toolchain v4.24.0), Z3 ≥ 4.15.2, lake.

**Branch:** `feat/indexed-types` (continues after BitVec Phase 1, head ~16b3cea).

---

## Context for the implementer (carried over from Phase 1)

- Build: `lake build Blaster`. Run one test file: `lake env lean Tests/Smt/SmtFin/<File>.lean`. Full suite: `LEAN_NUM_THREADS=5 lake test`.
- A test is `#blaster [<prop>]`. Default expects **Valid** (`✅ Valid`); a wrong result logs `❌` but the file still compiles — **read the log lines, not the exit code**. Expected-counterexample tests: `#blaster (gen-cex: 0) (solve-result: 1) [...]` → `✅ Expected Falsified`. Optimizer-only: `#blaster (only-optimize: 1) [...]` must fold to `True`.
- ⚠️ **Trivially-true props fold to `True` before translation** and prove nothing about the translator — always use props that exercise the feature (e.g. with a quantified variable and a real constraint).
- ⚠️ **Double-backtick name literals (`` ``Foo.bar ``) do not compile for nonexistent constants.** Discover real Lean 4.24 constant names empirically in each task's Step 2 (run the failing test, read which constant the error names) BEFORE writing the match arms. Never guess a name.
- ⚠️ **Subagents have repeatedly left scratch probe edits in test files.** After each task run `git status` and confirm only the intended files changed; `git checkout --` any scratch.
- **Pre-existing uncommitted file:** `Tests/Smt/SmtNat/SmtNatMod.lean` has an unrelated working-tree modification. Do NOT commit, revert, or touch it. `git add` only the files each task names.

### Key integration points (verified against current code)

- **Type translation** — `Blaster/Smt/Translate/Quantifier.lean`. `translateTypeAux` (~line 1300) dispatches on `t.getAppFn`; the `BitVec` hook is `| Expr.const ``BitVec _ => translateBitVecType t` placed before the generic `| Expr.const ..` arm (which calls `translateOpaqueType` then `translateNonOpaqueType`). Add `Fin` and `Array` arms alongside it. **Intercept order matters** (spec): the eventual full order is Vector → Array → UInt/Int → Fin → BitVec; for this phase, `Array` and `Fin` arms are independent heads so order among them is irrelevant, but place them with the `BitVec` arm.
- **Qualifier template** — `defineNatSort` (`Blaster/Smt/Env.lean:359`): `defineSort natSymbol none intSort` then `defineFun isNatSym #[(psym, natSort)] boolSort (leqSmt zeroSym xId)`. `translateNatType` (`Quantifier.lean:1218`) is the cache+define wrapper. Fin mirrors both **but with a non-trivial qualifier** `(and (<= 0 x) (< x n))`, unlike BitVec's trivial `true`.
- The qualifier is applied to quantified variables automatically: `createPredQualifierApp` → `getPredicateDeclaration` looks the type up in `indTypeInstCache`, so caching `Fin n` → `{instName := @isFin_n, instSort := Fin_n}` is all that's needed for `∀ x : Fin n` to get `(@isFin_n x)` as a premise.
- **Op translation** — `Blaster/Smt/Translate/Application.lean`: `translateOpaqueFun` (~line 305) maps names to symbols (`getOpaqueSmtEquivFun f sym`); `fullyAppliedConst` (~line 19) gates which names route there. For identity/custom ops, a dedicated `translateXOp?` in `translateApp`'s where-block (like `translateBitVecShift?`) is the pattern. `createAppN`/`createAppNAux` filter implicit + instance args automatically.
- **Term/sort builders** — `Blaster/Smt/Term.lean`: `arraySort (args : Array SortExpr)` exists (line 63); `selectSymbol`/`selectSmt` exist (205/391); **`storeSymbol`/`storeSmt` do NOT exist — add them.** `intSort`, `natLitSmt`, `leqSmt`, `ltSmt`, `andSmt`, `modSmt`, `addSmt`, `mkReservedSymbol`, `defineSort`, `defineFun`, `definePredQualifier` all exist.
- `isNatValue? : Expr → Option Nat` (`Optimize/Expr.lean:290`) for literal bounds. `isBitVecType` helper precedent (`Optimize/Expr.lean`) for head-const type checks.
- `opaqueFuns` (`Optimize/Opaque.lean`) currently has the BitVec group; no Fin/Array entries.

## File structure (whole phase)

| File | Responsibility |
|---|---|
| `Blaster/Smt/Term.lean` (modify) | `finSymbol n`/`finSort n`; `storeSymbol`/`storeSmt` |
| `Blaster/Smt/Env.lean` (modify) | `defineFinSort n` (alias + range qualifier) |
| `Blaster/Smt/Translate/Quantifier.lean` (modify) | `translateFinType`, `translateArrayType` + hooks |
| `Blaster/Smt/Translate/Application.lean` (modify) | `translateFinOp?` (val/mk/arith), `translateSMTArrayOp?` (get/set) |
| `Blaster/Optimize/Opaque.lean` (modify) | register Fin + SMTArray ops opaque |
| `Blaster/SmtArray.lean` (create) | `SMTArray` abbrev + `.get`/`.set` |
| `Blaster.lean` (modify) | `import Blaster.SmtArray` |
| `Tests/Smt/SmtFin/*.lean`, `Tests/Smt/SmtArray/*.lean` (create) | test suites |
| `Tests/Smt/SmtFin.lean`, `Tests/Smt/SmtArray.lean`, `Tests/Smt.lean` (create/modify) | suite registration |

---

## Task 1: Fin sort + range qualifier

**Files:** `Blaster/Smt/Term.lean`, `Blaster/Smt/Env.lean`, `Blaster/Smt/Translate/Quantifier.lean`; create `Tests/Smt/SmtFin/SmtFinSort.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtFinSort

/-! # Test cases to validate Fin sort + range qualifier -/

-- range qualifier: every Fin 5 value is in [0,5)
#blaster [∀ (x : Fin 5), x.val < 5]

#blaster [∀ (x : Fin 5), 0 ≤ x.val]

-- Fin 0 is uninhabited → ∀ is vacuously true
#blaster [∀ (x : Fin 0), x.val = 99]

-- out of range must be Falsifiable
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Fin 5), x.val < 4]
```

- [ ] **Step 2: Run to verify failure** — `lake build Blaster && lake env lean Tests/Smt/SmtFin/SmtFinSort.lean`. Record the error (likely the `Fin` type reaching `translateNonOpaqueType` / "instance parameters not supported", and/or `Fin.val` unhandled). **Note the surviving form of `Fin.val`** (constant name / projection) — Task 2 needs it; for Task 1 the qualifier tests may need `Fin.val` working, so if `x.val` blocks Task 1, see Step 5 note.

- [ ] **Step 3: Add `finSymbol`/`finSort` to `Blaster/Smt/Term.lean`** (next to `bitvecSymbol`/`bitvecSort`):

```lean
/-! Smt Fin symbol/sort for bound `n`: `Fin_n`, an alias of Int constrained
    by the `@isFin_n` qualifier `(and (<= 0 x) (< x n))`. -/
def finSymbol (n : Nat) : SmtSymbol := mkReservedSymbol s!"Fin_{n}"

def finSort (n : Nat) : SortExpr := .SymbolSort (finSymbol n)
```

- [ ] **Step 4: Add `defineFinSort` to `Blaster/Smt/Env.lean`** (after `defineNatSort`, mirroring it; the qualifier is the range predicate):

```lean
/-- Define the Fin_n sort (alias of Int) and its qualifier predicate
     `(define-fun @isFin_n ((@x Fin_n)) Bool (and (<= 0 @x) (< @x n)))`.
    For n = 0 the predicate is `false` (Fin 0 is uninhabited).
    Assume `isFinSym := @isFin_n`. -/
def defineFinSort (isFinSym : SmtSymbol) (n : Nat) : TranslateEnvT Unit := do
  defineSort (finSymbol n) none intSort
  let psym := mkReservedSymbol "@x"
  let xId := smtSimpleVarId psym
  let body := if n == 0 then falseSmt
              else andSmt (leqSmt (natLitSmt 0) xId) (ltSmt xId (natLitSmt n))
  defineFun isFinSym #[(psym, finSort n)] boolSort body
```

- [ ] **Step 5: Add `translateFinType` + hook in `Quantifier.lean`** (mirror `translateBitVecType`; place the def before `translateOpaqueType`):

```lean
/-- Translate `Fin n` (literal `n` only) to the `Fin_n` Int-aliased sort with
    range qualifier. Non-literal bound → error pointing at SMTArray.
    Assume `t := Expr.app (Expr.const ``Fin _) boundArg`. -/
def translateFinType (t : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? t with
 | some decl => return decl.instSort
 | none =>
    let some n := isNatValue? t.appArg!
      | throwEnvError "translateFinType: Fin with non-literal bound is not supported (got {reprStr t.appArg!}); use SMTArray for dynamically-sized indexing"
    let decl ← updateIndInstCache t (finSymbol n) (finSort n) (isReservedSymbol := true)
    defineFinSort decl.instName n
    return decl.instSort
```

In `translateTypeAux`, add alongside the `BitVec` arm:
```lean
   | Expr.const ``Fin _ => translateFinType t
```
(If Step 2 showed the bound arrives as a non-literal `OfNat`/`proj` form rather than a raw `Expr.lit` — as Char-derived BitVec widths did in Phase 1 — whnf `t.appArg!` before `isNatValue?`, matching the `translateBitVecType` width handling. Record what you observe.)

- [ ] **Step 6: Run to verify pass.** Expect 3 `✅ Valid` + 1 `✅ Expected Falsified`. If `x.val` blocks these tests (Fin.val unhandled), Task 1 and Task 2 are coupled — implement the `Fin.val → identity` arm from Task 2 Step 4 now and note that you pulled it forward. (`Fin.val` is almost certainly needed for *any* Fin proposition, so this is expected; prefer to land Task 1+2 together if so.)

- [ ] **Step 7: Manually verify the non-literal-bound error** (scratch, non-trivial prop so it doesn't fold):
```lean
#blaster [∀ (n : Nat) (x y : Fin (n+1)), x.val = y.val → x = y]
```
Expect the "non-literal bound" error. Delete the scratch.

- [ ] **Step 8: Commit**
```bash
git add Blaster/Smt/Term.lean Blaster/Smt/Env.lean Blaster/Smt/Translate/Quantifier.lean Tests/Smt/SmtFin/SmtFinSort.lean
git commit -m "feat(fin): translate Fin n to Int-aliased Fin_n sort with range qualifier"
```

---

## Task 2: Fin.val / Fin.mk identity + comparisons

`Fin n`'s SMT carrier *is* `Int`, so `Fin.val` (Fin→Nat) and `Fin.mk` (Nat+proof→Fin) are both the identity at the SMT level. Comparisons need no special handling: `Fin` is NOT made opaque-relational, so `<`/`≤` unfold to `Fin.val`-based Int comparisons (sound — `Fin` order is the inherited Int order). This is the key difference from BitVec.

**Files:** `Blaster/Optimize/Opaque.lean`, `Blaster/Smt/Translate/Application.lean`; create `Tests/Smt/SmtFin/SmtFinOps.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtFinOps

/-! # Test cases to validate Fin.val/Fin.mk identity + comparisons -/

#blaster [∀ (x y : Fin 5), x.val = y.val → x = y]

#blaster [∀ (x : Fin 5), (⟨0, by decide⟩ : Fin 5).val = 0]

#blaster [∀ (x y : Fin 8), x < y → x.val < y.val]

#blaster [∀ (x y : Fin 8), x ≤ y ∨ y ≤ x]

-- mk then val round-trips
#blaster [∀ (h : (3:Nat) < 5), (Fin.mk 3 h).val = 3]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), x.val = y.val]
```

- [ ] **Step 2: Run to verify failure.** Record the EXACT surviving constants for `Fin.val` and `Fin.mk` (projection vs `Fin.val` const; `Fin.mk` vs anonymous-ctor). They may already be partly handled if Task 1 pulled `Fin.val` forward — in that case test the remaining gaps. Also observe how `x < y` unfolds (expect `Fin.lt`/`Nat.lt` on `.val`s — confirm it bottoms out in already-supported Int/Nat comparison once `Fin.val` is identity).

- [ ] **Step 3: Register opaque** (`Opaque.lean`, the observed names):

```lean
    -- Fin: val/mk are identity at SMT level (Fin_n is an Int alias)
    ``Fin.val,
    ``Fin.mk,
```

- [ ] **Step 4: Add `translateFinOp?` to `translateApp`'s where-block** (`Application.lean`, dispatched in the `Expr.const n _` chain near `translateBitVecShift?`):

```lean
/-- Fin.val / Fin.mk are the identity at the SMT level (Fin_n aliases Int):
    translate the carried value directly. `Fin.val a` → translate `a`;
    `Fin.mk v _` → translate `v` (the proof arg is dropped). -/
    translateFinOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Fin.val =>
          -- args: #[bound(implicit), a]  → translate a
          if h : args.size ≥ 1 then return some (← termTranslator args[args.size - 1]!)
          else return none
      | ``Fin.mk =>
          -- args: #[bound(implicit), v, proof] → translate v
          if h : args.size ≥ 2 then return some (← termTranslator args[1]!)
          else return none
      | _ => return none
```
ADAPT arg indices to the layout observed in Step 2 (use `#check @Fin.val`/`@Fin.mk`; `Fin.val : {n} → Fin n → Nat` so `a` is the last arg; `Fin.mk : {n} → (val:Nat) → val<n → Fin n` so `v` is index 1, proof index 2). If `Fin.val` surfaces as an `Expr.proj` rather than a const application, handle it in `translateProj` (Application.lean ~1301) instead — record which.

- [ ] **Step 5: Run to verify pass.** 5 `✅ Valid` + 1 `✅ Expected Falsified`. Regression: SmtFinSort (3+1).

- [ ] **Step 6: Commit**
```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtFin/SmtFinOps.lean
git commit -m "feat(fin): Fin.val/Fin.mk identity translation; comparisons via Int order"
```

---

## Task 3: Fin modular arithmetic

`Fin.add/sub/mul` on `Fin n` are **modular** (`(a + b) % n`). Map to `(mod (op a b) n)` with literal `n`. ⚠️ Scope guard: if Step 2 reveals these unfold into `Fin.mk (... % n) (proof)` that already bottoms out in supported ops once `Fin.mk` is identity and `%`/`+` are Nat ops, then **no new code may be needed** — verify empirically and, if so, just add tests and note it. Only add explicit translation if the ops survive as named `Fin.add` constants reaching translation unhandled.

**Files:** `Blaster/Optimize/Opaque.lean` (maybe), `Blaster/Smt/Translate/Application.lean` (maybe); create `Tests/Smt/SmtFin/SmtFinArith.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtFinArith

/-! # Test cases to validate Fin modular arithmetic -/

-- 3 + 4 = 7 ≡ 2 (mod 5)
#blaster [(⟨3, by decide⟩ + ⟨4, by decide⟩ : Fin 5) = ⟨2, by decide⟩]

#blaster [∀ (x : Fin 5), x + ⟨0, by decide⟩ = x]

-- modular wrap keeps result in range
#blaster [∀ (x y : Fin 5), (x + y).val < 5]

#blaster [∀ (x y : Fin 7), x * y = y * x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Fin 5), (x + y).val = x.val + y.val]
```

- [ ] **Step 2: Run to verify failure / observe.** Record what `+`/`*` on `Fin` unfold to. **Decision point:**
  - (A) If they bottom out in supported ops after `Fin.mk`/`Fin.val` identity (likely — `Fin.add` is `⟨(a.val + b.val) % n, _⟩`), most tests may already pass. Record which pass; the `(x+y).val < 5` and falsified tests are the real check that modular semantics are faithful.
  - (B) If a named `Fin.add`/`Fin.mul`/`Fin.sub`/`HAdd`-instance constant survives unhandled, register it opaque and add a `translateFinArith` that emits `modSmt (addSmt a b) (natLitSmt n)` — extracting literal `n` from the implicit bound arg (error if non-literal), mirroring `translateBitVecShift`'s structure.

- [ ] **Step 3–5: Implement per the Step 2 decision** (code only if path B). If path A, this task is tests-only.

- [ ] **Step 6: Run to verify pass.** 4 `✅ Valid` + 1 `✅ Expected Falsified`. Regression: SmtFinSort, SmtFinOps.

- [ ] **Step 7: Commit**
```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtFin/SmtFinArith.lean
git commit -m "feat(fin): modular arithmetic (Fin.add/sub/mul)"
```
(If path A: commit only the test file with message `test(fin): modular arithmetic via Fin.mk/val identity`.)

---

## Task 4: SMTArray library + store builders

**Files:** create `Blaster/SmtArray.lean`; modify `Blaster.lean`, `Blaster/Smt/Term.lean`.

- [ ] **Step 1: Create `Blaster/SmtArray.lean`** (verify `getD`/`setIfInBounds` exist in 4.24 with these signatures via `#check Array.getD`/`#check Array.setIfInBounds`; adapt if the names differ):

```lean
/-! # SMTArray — a Nat-indexed array API friendly to SMT translation.

`Array.get` requires a `Fin a.size` index (a dynamically-sized bound the
translator cannot model). `SMTArray` exposes total `Nat`-indexed `get`/`set`
so user code never produces `Fin a.size`. It is `Array` at runtime (zero cost)
and translates to the SMT array theory (`select`/`store`). -/

namespace Blaster

abbrev SMTArray (α : Type u) := Array α

/-- Total Nat-indexed read; out-of-bounds yields `default`. -/
def SMTArray.get [Inhabited α] (a : SMTArray α) (i : Nat) : α := a.getD i default

/-- Total Nat-indexed write; out-of-bounds is a no-op. -/
def SMTArray.set (a : SMTArray α) (i : Nat) (v : α) : SMTArray α := a.setIfInBounds i v

end Blaster
```

- [ ] **Step 2: Wire the import.** Add `import Blaster.SmtArray` to `Blaster.lean` (alongside the other `import Blaster.*`). Run `lake build Blaster` — must succeed (this confirms the library compiles before any translation work).

- [ ] **Step 3: Add `storeSymbol`/`storeSmt` to `Blaster/Smt/Term.lean`** (next to `selectSymbol`/`selectSmt` at ~line 205/391):

```lean
/-! store Smt symbol (array theory). -/
def storeSymbol : SmtSymbol := mkReservedSymbol "store"
```
and near `selectSmt`:
```lean
/-! Create a store Smt application `(store a i v)`. -/
def storeSmt (a i v : SmtTerm) : SmtTerm := mkSimpleSmtAppN storeSymbol #[a, i, v]
```

- [ ] **Step 4: Commit**
```bash
git add Blaster/SmtArray.lean Blaster.lean Blaster/Smt/Term.lean
git commit -m "feat(smtarray): SMTArray library + store term builders"
```

---

## Task 5: SMTArray type translation

`Array α` (hence `SMTArray α`, an abbrev) → `(Array Int σ_α)`, with the element-sort qualifier lifted pointwise.

**Files:** `Blaster/Smt/Translate/Quantifier.lean`; create `Tests/Smt/SmtArray/SmtArraySort.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtArraySort

open Blaster

/-! # Test cases to validate SMTArray sort translation -/

-- two arrays equal at SMT-extensional level
#blaster [∀ (a b : SMTArray Int), a = b → b = a]

#blaster [∀ (a : SMTArray (BitVec 8)), a = a]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : SMTArray Int), a = b]
```

- [ ] **Step 2: Run to verify failure.** `SMTArray` is an abbrev for `Array`; after `removeTypeAbbrev` the head is `Array`. Confirm the error mentions `Array` (the inductive-datatype path). Record whether the element type α arrives as expected.

- [ ] **Step 3: Add `translateArrayType` + hook** (`Quantifier.lean`, near `translateBitVecType`):

```lean
/-- Translate `Array α` (and its abbrev `SMTArray α`) to the SMT array sort
    `(Array Int σ_α)`, where `σ_α` is the translated element sort.
    Assume `t := Expr.app (Expr.const ``Array _) elemType`. -/
def translateArrayType
    (termTranslator : Expr → TranslateEnvT SmtTerm)
    (t : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? t with
 | some decl => return decl.instSort
 | none =>
    let elemType := t.appArg!
    let elemSort ← translateTypeAux termTranslator elemType
    let sort := arraySort #[intSort, elemSort]
    -- cache; qualifier is trivial at the array level (element qualifier is
    -- lifted at select sites — see Task 6 / documented limitation)
    discard <| updateIndInstCache t (mkReservedSymbol s!"Array") sort (isReservedSymbol := true)
    definePredQualifier (mkReservedSymbol "@isSMTArray") #[sort] (some true)
    return sort
```
ADAPT: the cache key must be the full `Array α` expr so distinct element types get distinct entries — but the `instName`/qualifier symbol must be UNIQUE per element sort to avoid `define-fun` redefinition (Phase 1 lesson: Z3 errors on duplicate `@is…`). Mirror how `updateIndInstCache` derives names; if a single `@isSMTArray` collides across element types, derive the qualifier name from the element sort (e.g. include a counter via `mkFreshId`, as the abstract-type machinery does). **Verify with a test file containing both `SMTArray Int` and `SMTArray (BitVec 8)` in the same query.** Also confirm `translateTypeAux` is in scope / mutually recursive here (it is `partial def`; `translateArrayType` may need to be in the same mutual block or take `translateTypeAux` as the passed `termTranslator`-style param — match how `translateNonOpaqueType` receives its recursive translator).

In `translateTypeAux`, add:
```lean
   | Expr.const ``Array _ => translateArrayType termTranslator t
```

- [ ] **Step 4: Run to verify pass.** 2 `✅ Valid` + 1 `✅ Expected Falsified`. Add a mixed-element regression test (`SMTArray Int` + `SMTArray (BitVec 8)` in one prop) and confirm no Z3 duplicate-sort/`define-fun` error.

- [ ] **Step 5: Commit**
```bash
git add Blaster/Smt/Translate/Quantifier.lean Tests/Smt/SmtArray/SmtArraySort.lean
git commit -m "feat(smtarray): translate Array/SMTArray type to (Array Int elem) sort"
```

---

## Task 6: SMTArray.get / SMTArray.set → select / store

**Files:** `Blaster/Optimize/Opaque.lean`, `Blaster/Smt/Translate/Application.lean`; create `Tests/Smt/SmtArray/SmtArrayOps.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtArrayOps

open Blaster

/-! # Test cases to validate SMTArray get/set (array theory) -/

-- read-over-write, same index
#blaster [∀ (a : SMTArray Int) (i : Nat) (v : Int), (a.set i v).get i = v]

-- read-over-write, different index
#blaster [∀ (a : SMTArray Int) (i j : Nat) (v : Int), i ≠ j → (a.set i v).get j = a.get j]

-- set then set same index overwrites
#blaster [∀ (a : SMTArray Int) (i : Nat) (v w : Int), ((a.set i v).set i w).get i = w]

-- composes with BitVec elements
#blaster [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), (a.set i v).get i = v]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i j : Nat) (v : Int), (a.set i v).get j = v]
```

- [ ] **Step 2: Run to verify failure.** `SMTArray.get`/`SMTArray.set` are defs; with them un-opaque the optimizer unfolds into `Array.getD`/`setIfInBounds` internals (and likely `Fin`/`Option` machinery). Record the surviving constants. Note `SMTArray.get` has an `[Inhabited α]` instance arg that `createAppN` must filter.

- [ ] **Step 3: Register opaque** (`Opaque.lean`):
```lean
    -- SMTArray Nat-indexed get/set → SMT array theory select/store
    ``Blaster.SMTArray.get,
    ``Blaster.SMTArray.set,
```
(`import Blaster.SmtArray` may be needed at the top of `Opaque.lean` for the `` `` `` name literals to resolve — add if the build complains.)

- [ ] **Step 4: Map get/set through the `createAppN` path** (`Application.lean`; `import Blaster.SmtArray` at top if the `` `` `` literals don't resolve).

The PRIMARY approach (mirrors every Phase 1 binary op): route through `getOpaqueSmtEquivFun f <symbol>` + `createAppN`, which already filters the implicit `α` and the `[Inhabited]` instance arg and emits `(symbol explicit-args…)`. `SMTArray.get a i` → `(select a i)` and `SMTArray.set a i v` → `(store a i v)` are exactly `select`/`store` applied to the explicit args in order, so add arms to `translateOpaqueFun`:
```lean
  | ``Blaster.SMTArray.get => getOpaqueSmtEquivFun f selectSymbol
  | ``Blaster.SMTArray.set => getOpaqueSmtEquivFun f storeSymbol
```
and the two names to `fullyAppliedConst`.

VERIFY the operand order createAppN produces matches SMT array theory: `select` is `(select array index)`, `store` is `(store array index value)` — i.e. the explicit args of `SMTArray.get`/`.set` are already `(a, i)` / `(a, i, v)` in that order, so no reordering is needed. Dump the SMT (`only-smt-lib`/dump option) for one get and one set to confirm `(select $a $i)` / `(store $a $i $v)`. If `createAppN`'s arity/HOF handling mis-fires on the `[Inhabited]` instance arg (it shouldn't — instance args are filtered like other implicits), fall back to a dedicated `translateSMTArrayOp?` in the where-block that translates the explicit args and calls `selectSmt`/`storeSmt` directly — and report why the standard path didn't work.

- [ ] **Step 5: Run to verify pass.** 4 `✅ Valid` + 1 `✅ Expected Falsified`. The read-over-write tests exercise the array theory axioms end to end.

- [ ] **Step 6: Commit**
```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtArray/SmtArrayOps.lean
git commit -m "feat(smtarray): SMTArray.get/set to array-theory select/store"
```

---

## Task 7: Suite registration + documented limitations + full regression

**Files:** create `Tests/Smt/SmtFin.lean`, `Tests/Smt/SmtArray.lean`; modify `Tests/Smt.lean`.

- [ ] **Step 1: Register suites.**
`Tests/Smt/SmtFin.lean`:
```lean
import Tests.Smt.SmtFin.SmtFinArith
import Tests.Smt.SmtFin.SmtFinOps
import Tests.Smt.SmtFin.SmtFinSort
```
`Tests/Smt/SmtArray.lean`:
```lean
import Tests.Smt.SmtArray.SmtArrayOps
import Tests.Smt.SmtArray.SmtArraySort
```
`Tests/Smt.lean`: add `import Tests.Smt.SmtArray` and `import Tests.Smt.SmtFin` (alphabetical — after `SmtBitVec`, before others as ordering dictates).

- [ ] **Step 2: Documented-limitation regression tests.** Append to `Tests/Smt/SmtArray/SmtArrayOps.lean` a test pinning the over-approximation direction (OOB / extensional equality): a property that depends on `default` at an OOB index should be **Undetermined or Falsified, never wrongly Valid**. Add a comment citing the spec's "Documented limitations". If you cannot construct a clean test for this, write a comment explaining why and cite the spec — do NOT silently skip.

- [ ] **Step 3: Full regression.** `lake build Blaster && LEAN_NUM_THREADS=5 lake test` (generous timeout — several minutes). Scan for ANY `❌`/`error:`. The two known pre-existing failures from before this branch (if still present: none — Phase 1 left the suite fully green) must not regress; BitVec suites (Sort/Lit/Arith/Compare/Div/Shift/Structure/Fold) must stay green. Per-file Fin/Array counts as written above.

- [ ] **Step 4: Stale-comment / TODO check.** Grep changed files for leftover `Fin`/`Array` TODOs that are now done; update the spec/Quantifier doc comments if they still say these are unsupported.

- [ ] **Step 5: Commit**
```bash
git add Tests/Smt/SmtFin.lean Tests/Smt/SmtArray.lean Tests/Smt.lean Tests/Smt/SmtArray/SmtArrayOps.lean
git commit -m "test(fin,smtarray): register suites; OOB/extensional limitation guards"
```

---

## Self-review checklist (run after writing, before execution)

- Spec Phase 2 coverage: Fin sort+qualifier ✅ T1; Fin 0 vacuity ✅ T1; Fin.val/mk identity ✅ T2; comparisons via Int order ✅ T2; modular arithmetic ✅ T3; non-literal bound → error ✅ T1; SMTArray library ✅ T4; Array→(Array Int σ) ✅ T5; element-sort composition ✅ T5/T6; get/set→select/store ✅ T6; OOB/extensional over-approximation documented + guarded ✅ T7.
- Deferred to later (note, don't implement): concrete `#[a,b,c]` literal → store-chains (spec calls this an enhancement; current behavior = uninterpreted constant, acceptable); `Array.size`/length reasoning (Vector's job, Phase 4); faithful `SMTArray` equality (Vector's job).
- Known uncertainty resolved by discovery steps: exact 4.24 constant names/AST for `Fin.val`/`Fin.mk`/Fin arithmetic and `Array.getD`/`SMTArray.*`; whether Fin arithmetic needs explicit translation (Task 3 path A vs B); cache-name uniqueness for per-element-type array qualifiers (Task 5 Step 3).

## Out of scope (Phase 3+)

`UInt8/16/32/64`, `Int8/16/32/64`, `USize/ISize` (Phase 3 — thin BitVec views, reuse Phase 1 machinery); `Vector α n` (Phase 4 — static-length arrays with faithful pointwise equality). Each gets its own plan.


