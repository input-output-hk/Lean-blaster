# Indexed Types Phase 3 — UInt/Int Families Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Translate `UInt8/16/32/64`, `Int8/16/32/64`, and `USize/ISize` as thin views over `BitVec w`, reusing the Phase-1 BitVec machinery. `USize`/`ISize` width is configurable (`usize-width: 32|64`, default 64).

**Architecture:** All twelve types are (nested) single-field structures over `BitVec w` (e.g. `UInt8 = { toBitVec : BitVec 8 }`, `Int8 = { toUInt8 : UInt8 }`). Like `SMTArray` (Phase 2), structures survive `resolveTypeAbbrev`, so we intercept each type head and map it to `bitvecSort w`. The wrappers (`toBitVec`/`ofBitVec`/`toUInt8`/…) are **identity at the SMT level** (UInt8 and BitVec 8 share the sort `(_ BitVec 8)`), and Lean's UInt/Int ops unfold to BitVec-layer ops on the `.toBitVec` field — so once the type erases and wrappers are identity, most operations reduce to the already-implemented BitVec translation. Spec: `docs/superpowers/specs/2026-06-11-indexed-types-design.md` (Phase 3).

**Tech Stack:** Lean 4 (v4.24.0), Z3 ≥ 4.15.2, lake. **Branch:** `feat/indexed-types` (continues after Phase 2).

---

## Context for the implementer (verified against Lean 4.24 + current code)

- Build: `lake build Blaster`. One test file: `lake env lean Tests/Smt/SmtUInt/<File>.lean`. Full suite: `LEAN_NUM_THREADS=5 lake test`. Read the `✅`/`❌` log lines, not the exit code. `(gen-cex: 0) (solve-result: 1)` → expects `✅ Expected Falsified`.
- ⚠️ Trivially-true props fold to `True` before translation. ⚠️ `` ``Foo `` name literals don't compile for nonexistent constants — discover real names in each task's Step 2 before writing match arms. ⚠️ After each task `git status` must show ONLY the pre-existing `Tests/Smt/SmtNat/SmtNatMod.lean`; `git add` only named files; delete scratch.

### The twelve types (verified via `#print`)

| Lean type | representation | SMT sort |
|---|---|---|
| `UInt8/16/32/64` | `structure { toBitVec : BitVec w }`, ctor `UIntW.ofBitVec` | `(_ BitVec w)` |
| `USize` | `structure { toBitVec : BitVec System.Platform.numBits }` | `(_ BitVec usizeWidth)` (config, default 64) |
| `Int8/16/32/64` | `structure { toUIntW : UIntW }`, ctor `IntW.ofUIntW` (private) | `(_ BitVec w)` |
| `ISize` | `structure { toUSize : USize }` | `(_ BitVec usizeWidth)` |

Examples (from `#print`): `UInt8.add a b = { toBitVec := a.toBitVec + b.toBitVec }`; `UInt8.lt a b = a.toBitVec < b.toBitVec` (unsigned BitVec `<`); `Int8.lt a b = a.toBitVec.slt b.toBitVec = true` (signed). So UInt/Int ops unfold to BitVec ops on the field — **once the wrappers are identity and the type maps to `bitvecSort w`, these should translate via the existing Phase-1 BitVec arms (path A).** Each op task's Step 2 confirms this empirically.

### Phase-1 BitVec machinery to reuse
- `bitvecSort w`, `bitvecLitSmt v w`, `isBitVecValue?` (Optimize/Expr.lean), `isBitVecType` (Optimize/Expr.lean).
- BitVec ops already mapped in `translateOpaqueFun`/`fullyAppliedConst`: `bvadd/bvsub/bvmul/bvneg/bvand/bvor/bvxor/bvnot`, `bvult/bvule/bvslt/bvsle`, div wrappers, shifts (`translateBitVecShift`), extend/extract (`translateBitVecIndexed`).
- Type-hook precedent: `translateBitVecType`/`translateFinType`/`translateArrayType` in Quantifier.lean `translateTypeAux` (the `| Expr.const ``X _ => ...` arms ~line 1395). Wrapper-identity precedent: `translateFinOp?` (`Fin.val`/`Fin.mk` → translate the carried value). Literal precedent: `isBitVecValue?` + the `translateExpr` hook.
- Option precedent: `BlasterOptions` field (`Blaster/Command/Options.lean`) + `syntax`/parser arm in `Blaster/Command/Syntax.lean` (see `max-depth` at lines 39/54). The translation env reads `(← get).optEnv.options.solverOptions.<field>`.

## File structure

| File | Responsibility |
|---|---|
| `Blaster/Smt/Translate/Quantifier.lean` (modify) | `translateUIntType` (width table) + hooks for the 12 names |
| `Blaster/Optimize/Expr.lean` (modify) | `isUIntValue?`-style literal recognizers; `uintWidth?`/`isUIntType` helpers |
| `Blaster/Optimize/Opaque.lean` (modify) | register wrapper ctors/projections + any surviving ops opaque |
| `Blaster/Smt/Translate/Application.lean` (modify) | `translateUIntOp?` (wrapper identity, conversions); literal emission |
| `Blaster/Command/Options.lean` + `Blaster/Command/Syntax.lean` (modify) | `usizeWidth` option + `usize-width:` syntax |
| `Tests/Smt/SmtUInt/*.lean`, `Tests/Smt/SmtInt/*.lean` (create) + registration | test suites |

---

## Task 1: Type translation (12 types → BitVec sort) + width table

**Files:** `Blaster/Optimize/Expr.lean` (width helper), `Blaster/Smt/Translate/Quantifier.lean`; create `Tests/Smt/SmtUInt/SmtUIntSort.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtUIntSort

/-! # Test cases to validate UInt/Int sort translation -/

#blaster [∀ (x y : UInt8), x = y → y = x]

#blaster [∀ (x : UInt32) (y : UInt64), x = x ∧ y = y]

#blaster [∀ (x y : Int8), x = y → y = x]

#blaster [∀ (x : USize), x = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : UInt8), x = y]
```

- [ ] **Step 2: Run, record error** (`lake build Blaster && lake env lean Tests/Smt/SmtUInt/SmtUIntSort.lean`). Confirm each type reaches the inductive-datatype path (structures aren't intercepted yet). Note how `USize`'s width field appears (`System.Platform.numBits`).

- [ ] **Step 3: Width helper in `Blaster/Optimize/Expr.lean`**

```lean
/-- Map a UInt/Int family type-head name to its BitVec width. `USize`/`ISize`
    return `none` here (their width is configuration-dependent — resolved by the
    caller against the `usizeWidth` option). -/
def uintWidth? : Name → Option Nat
  | ``UInt8  | ``Int8  => some 8
  | ``UInt16 | ``Int16 => some 16
  | ``UInt32 | ``Int32 => some 32
  | ``UInt64 | ``Int64 => some 64
  | _ => none

/-- `true` if `e`'s head is one of the twelve UInt/Int family types. -/
def isUIntFamilyType (e : Expr) : Bool :=
  match e.getAppFn with
  | Expr.const n _ => (uintWidth? n).isSome || n == ``USize || n == ``ISize
  | _ => false
```

- [ ] **Step 4: `translateUIntType` + hooks in `Quantifier.lean`** (mirror `translateBitVecType`; the SMT sort is exact so the qualifier is trivially `true`). `USize`/`ISize` width comes from the option (default 64 — for Task 1 hardcode 64 and wire the option in Task 6, leaving a `-- TODO(Task 6): read usizeWidth option` marker):

```lean
/-- Translate a UInt/Int family type to its underlying `(_ BitVec w)` sort
    (the wrappers are erased — UInt8 and BitVec 8 share the SMT sort).
    Assume `t.getAppFn = Expr.const n _` with n a UInt/Int family name. -/
def translateUIntType (t : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? t with
 | some decl => return decl.instSort
 | none =>
    let Expr.const n _ := t.getAppFn
      | throwEnvError "translateUIntType: name expression expected but got {reprStr t}"
    let w ← match uintWidth? n with
      | some w => pure w
      | none => pure 64  -- USize/ISize; TODO(Task 6): read usizeWidth option
    -- Derive the qualifier name from the TYPE name (@isUInt8, @isInt8, @isUSize, …),
    -- NOT from the width. `bitvecSymbol w` would make UInt8, Int8, and raw BitVec 8 all
    -- want `@isBitVec_8` → duplicate define-fun → Z3 error when ≥2 appear in one query.
    -- The sort `bitvecSort w` is built-in (no define-sort), so only the predicate name
    -- must be unique; distinct names fully resolve it.
    let decl ← updateIndInstCache t (mkReservedSymbol s!"{n}") (bitvecSort w) (isReservedSymbol := true)
    definePredQualifier decl.instName #[bitvecSort w] (some true)
    return decl.instSort
```
Add hooks alongside the BitVec/Fin/Array arms in `translateTypeAux`:
```lean
   | Expr.const ``UInt8 _  | Expr.const ``UInt16 _ | Expr.const ``UInt32 _
   | Expr.const ``UInt64 _ | Expr.const ``USize _
   | Expr.const ``Int8 _   | Expr.const ``Int16 _  | Expr.const ``Int32 _
   | Expr.const ``Int64 _  | Expr.const ``ISize _ => translateUIntType t
```
The per-type-name instName (above) is what prevents the **three-way collision** at width 8: `UInt8`, `Int8`, AND raw `BitVec 8` all map to sort `(_ BitVec 8)`, so a width-derived `@isBitVec_8` name would duplicate-define whenever any two appear together. Per-type names (`@isUInt8`/`@isInt8`/`@isBitVec_8`) are distinct and each resolves the (built-in, define-sort-free) sort.

- [ ] **Step 5: Run, pass.** 4 ✅ Valid + 1 ✅ Expected Falsified. Add regression queries mixing types of the same width in ONE prop and confirm no Z3 redefinition: `∀ (a : UInt8) (b : Int8) (c : BitVec 8), a = a ∧ b = b ∧ c = c`.

- [ ] **Step 5b: Char/String smoke test (CRITICAL — UInt32 interception touches Char).** `Char = structure { val : UInt32 }`, so claiming `UInt32` changes how every Char value/comparison translates — the exact Issue3-class trap, and Phase 1 already ate a Char/String regression from UInt32/BitVec changes. Before stacking later tasks, run and confirm STILL green: `lake env lean Tests/Optimize/OptimizeBEq/BEqString.lean` (all ✅ Success), `lake env lean Tests/FixedIssues/Issue3.lean` (3 ✅ Valid), and the String suite (`Tests/Smt/Smt*` containing String/Char props — find via grep). If any break, settle the UInt32-vs-Char strategy NOW (e.g. ensure Char still routes correctly), not after six tasks of accumulation. Record results in the report.

- [ ] **Step 6: Commit** `feat(uint): translate UInt/Int family types to underlying BitVec sorts`.

---

## Task 2: Wrapper erasure + literals

The structure projections/constructors are identity at the SMT level (same `(_ BitVec w)` sort on both sides). Literals `UIntW.ofNat n` / `IntW.ofNat n` → `(_ bv(n mod 2^w) w)`.

**Files:** `Blaster/Optimize/Opaque.lean`, `Blaster/Optimize/Expr.lean`, `Blaster/Smt/Translate/Application.lean`; create `Tests/Smt/SmtUInt/SmtUIntLit.lean`.

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtUIntLit

#blaster [∀ (x : UInt8), x = 254 → x ≠ 255]

#blaster [∀ (x : UInt8), x = 5 → x.toBitVec = 5#8]

#blaster [(5 : UInt8).toBitVec = 5#8]

-- ofNat wraps mod 2^w
#blaster [(256 : UInt8) = 0]

#blaster [∀ (x : Int8), x = 5 → x ≠ 6]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x ≠ 200]
```
(`(254 : UInt8)` etc. elaborate via `OfNat`/`UInt8.ofNat`. If a phrasing doesn't elaborate, adjust and note it.)

- [ ] **Step 2: Run, record the EXACT surviving constants** for: the literal form (`UInt8.ofNat`? `OfNat.ofNat`? the structure-ctor `UInt8.ofBitVec (BitVec.ofNat ...)`?), and the wrapper projections/ctors (`UInt8.toBitVec`, `UInt8.ofBitVec`, `Int8.toUInt8`, `Int8.ofUInt8`, and any composite `Int8.toBitVec`). Record what `x.toBitVec` (for symbolic `x : UInt8`) becomes — projection const vs `Expr.proj`.

- [ ] **Step 3: Register opaque** (`Opaque.lean`, observed names). Likely set:
```lean
    -- UInt/Int wrappers: identity at SMT level (UIntW and BitVec w share the sort)
    ``UInt8.toBitVec, ``UInt8.ofBitVec, /- …16/32/64/USize… -/
    ``Int8.toUInt8, /- IntW.ofUIntW is private — see Step 2 for the usable name -/
    -- literal constructors
    ``UInt8.ofNat, /- …per width… -/
```
ADAPT to observed names. `IntW.ofUIntW` is a PRIVATE constructor — check whether it surfaces (anonymous-ctor `⟨⟩`/`IntW.mk`) and register the form that actually appears.

- [ ] **Step 4: Literal recognizer + wrapper-identity** (`Expr.lean` + `Application.lean`).
  - Recognizer (fixed-width): add `isUIntValue? (e : Expr) : Option (Nat × Nat)` returning `(width, value mod 2^w)` for the observed UInt8–64/Int8–64 literal form(s), reusing `isBitVecValue?` on the inner `BitVec.ofNat w v` field where the width literal is present. Hook into `translateExpr` (next to the `isBitVecValue?` hook) emitting `bitvecLitSmt v w`.
  - ⚠️ **USize/ISize literals need their own owner (advisor catch).** `USize`'s field is `BitVec System.Platform.numBits`, which does NOT reduce to a literal width, so a pure `isUIntValue?` returns `none` for USize literals and they'd silently fail. The width must come from the configured `usizeWidth` — which a pure function can't read. So recognize USize/ISize literals in a MONADIC context (a `translateUSizeLit?` arm in `translateApp` / the translateExpr path where the env is available): match the USize/ISize literal form (record it in Step 2), read `w := (← get).optEnv.options.solverOptions.usizeWidth` (Task 1 hardcodes 64 until Task 6 wires the option), and emit `bitvecLitSmt (v mod 2^w) w`. Add a USize-literal test here (not only in Task 6), e.g. `#blaster [(5 : USize).toBitVec.toNat = 5]` or an equality that exercises the literal.
  - Wrapper-identity: extend/add a `translateUIntOp?` in `translateApp`'s where-block mapping each wrapper projection/ctor to "translate the carried argument" (identity), exactly like `translateFinOp?`. `UInt8.toBitVec x` → translate `x`; `UInt8.ofBitVec b` → translate `b`; `Int8.toUInt8 x` → translate `x`; etc. If `.toBitVec` surfaces as `Expr.proj`, handle in `translateProj`.

- [ ] **Step 5: Run, pass.** 5 ✅ Valid + 1 ✅ Expected Falsified. Regression: SmtUIntSort, one BitVec suite.

- [ ] **Step 6: Commit** `feat(uint): wrapper erasure (identity ctors/projections) + literals`.

---

## Task 3: Arithmetic, bitwise, shifts, comparisons (discovery-first)

Lean's UInt/Int ops unfold to BitVec ops on `.toBitVec`. With Task 1 (type) + Task 2 (wrapper identity) done, these likely translate via the existing Phase-1 BitVec arms (PATH A — tests-only). Only add code if a named `UIntW.add`/`IntW.lt`/etc. constant survives to translation unhandled (PATH B).

**Files:** maybe `Opaque.lean`/`Application.lean`; create `Tests/Smt/SmtUInt/SmtUIntArith.lean`, `Tests/Smt/SmtInt/SmtIntArith.lean`.

- [ ] **Step 1: Write the failing tests** (`SmtUIntArith.lean`):
```lean
import Blaster
namespace Test.SmtUIntArith

#blaster [∀ (x y : UInt8), x + y = y + x]
#blaster [∀ (x : UInt8), x + 0 = x]
#blaster [∀ (x : UInt8), x + 255 = x - 1]          -- wrap-around
#blaster [∀ (x y : UInt8), x &&& y = y &&& x]
#blaster [∀ (x : UInt8), x ^^^ x = 0]
#blaster [∀ (x y : UInt8), x < y → ¬ (y < x)]      -- unsigned <
#blaster [∀ (x : UInt8), x ≤ 255]
#blaster [∀ (x : UInt8), x <<< 1 = x * 2]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : UInt8), x + y = x]
-- soundness: UInt is unsigned, no wrap-around order law
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x ≤ x + 1]
```
(`SmtIntArith.lean`): signed-comparison focus:
```lean
import Blaster
namespace Test.SmtIntArith

#blaster [∀ (x y : Int8), x + y = y + x]
#blaster [(127 : Int8) + 1 < (0 : Int8)]           -- signed overflow wraps to negative
#blaster [∀ (x y : Int8), x < y → ¬ (y < x)]       -- signed <
#blaster [(-1 : Int8) < (0 : Int8)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int8), x ≤ x + 1]
```

- [ ] **Step 2: Run, OBSERVE the path.** Record whether each op unfolds to a BitVec op (→ Valid already, path A) or a named UInt/Int op survives unhandled (path B). The signed/unsigned distinction is the key check: `UInt8.lt` must reach `bvult`, `Int8.lt` must reach `bvslt` (via `.toBitVec.slt`). If `Int8`'s `< ` does NOT reach `bvslt` (e.g. compares via `toUInt8` without the slt), that's a real bug to fix in path B.

- [ ] **Step 3–5: per path.** Path A → ensure all tests genuinely pass (read every line; the signed `Int8` and wrap-around soundness guards are the load-bearing ones). Path B → register the surviving op opaque + map to the correct BitVec arm (unsigned vs signed), using observed names.

- [ ] **Step 6: Commit** `feat(uint,int): arithmetic/bitwise/shift/comparison ops` (or `test(...)` if path A).

---

## Task 4: Division and modulo (discovery-first)

`UIntW.div/mod` → unsigned BitVec div (the Phase-1 `udiv` per-width wrapper / `bvurem`); `IntW.div/mod` → signed (`sdiv` wrapper / `bvsmod`/`bvsrem`). Lean UInt div-by-zero = 0 (matches the udiv wrapper). Likely path A if they unfold to the BitVec div ops; verify the signed case maps to the SIGNED wrapper.

**Files:** maybe `Opaque.lean`/`Application.lean`; create `Tests/Smt/SmtUInt/SmtUIntDiv.lean`, `Tests/Smt/SmtInt/SmtIntDiv.lean`.

- [ ] **Step 1: Write the failing tests** (`SmtUIntDiv.lean`):
```lean
import Blaster
namespace Test.SmtUIntDiv
#blaster [∀ (x : UInt8), x / 0 = 0]
#blaster [∀ (x : UInt8), x % 0 = x]
#blaster [∀ (x : UInt8), x / 1 = x]
#blaster [∀ (x y : UInt8), y ≠ 0 → x % y < y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x / 0 = 255]
```
(`SmtIntDiv.lean`): signed division semantics — VERIFY Lean's `Int8.div` rounding (T-division) against the chosen BitVec wrapper FIRST with `#print Int8.div` and concrete `#eval` before relying on it:
```lean
import Blaster
namespace Test.SmtIntDiv
#blaster [∀ (x : Int8), x / 1 = x]
#blaster [((-6 : Int8)) / 2 = -3]
#blaster [∀ (x : Int8), x / 0 = 0]
```

- [ ] **Step 2: Run, observe path; verify the signed wrapper is used for Int.** Record `#print Int8.div`'s BitVec op and confirm the SMT result matches a concrete `#eval Int8` cross-check (the signed div-by-zero and rounding are the trap — Phase 1 wrapped `sdiv` for Lean's `x/0=0`).

- [ ] **Step 3–5: per path** (names observed; unsigned→udiv-wrapper/bvurem, signed→sdiv-wrapper/bvsmod/bvsrem).

- [ ] **Step 6: Commit** `feat(uint,int): division/modulo via BitVec div wrappers`.

---

## Task 5: Cross-width conversions

`UInt8.toUInt32` (widen, zero-extend), `UInt32.toUInt8` (narrow, extract), `Int8.toInt16` (sign-extend), same-width reinterpret (`UInt8.toInt8`/`Int8.toUInt8`) identity. `toNat`/`toInt` → error (Non-Goal). Reuse Phase-1 `translateBitVecIndexed`'s `zero_extend`/`sign_extend`/`extract` builders.

**Files:** `Blaster/Optimize/Opaque.lean`, `Blaster/Smt/Translate/Application.lean`; create `Tests/Smt/SmtUInt/SmtUIntConv.lean`.

- [ ] **Step 1: Write the failing test**
```lean
import Blaster
namespace Test.SmtUIntConv

#blaster [∀ (x : UInt8), x.toUInt32.toUInt8 = x]            -- widen then narrow round-trips
#blaster [∀ (x : UInt8), x.toUInt32 ≤ 255]                  -- zero-extended ≤ 255
#blaster [(255 : UInt8).toUInt32 = 255]                     -- zero-extend, no sign
#blaster [(255 : UInt8).toInt8 = -1]                        -- same-width reinterpret
#blaster [((-1 : Int8)).toInt16 = -1]                       -- sign-extend keeps value
#blaster [(0xABCD : UInt32).toUInt8 = 0xCD]                 -- narrow = low byte
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : UInt8), x.toUInt32 = 256]
```

- [ ] **Step 2: Run, record the conversion constant names + arg layouts** (`UInt8.toUInt32`, `UInt32.toUInt8`, `Int8.toInt16`, `UInt8.toInt8`, …). Confirm whether each unfolds to a BitVec `setWidth`/`signExtend`/`toBitVec`-reinterpret (path A) or survives as a named conversion (path B).

- [ ] **Step 3: Register opaque + translate** (path B). Add a `translateUIntConv?` mapping:
  - widen unsigned `UIntm.toUIntn` (m<n) → `(_ zero_extend (n-m))`
  - widen signed `Intm.toIntn` (m<n) → `(_ sign_extend (n-m))`
  - narrow `UIntn.toUIntm`/`Intn.toIntm` (n>m) → `(_ extract (m-1) 0)`
  - same-width reinterpret (`UInt8.toInt8`, `Int8.toUInt8`, etc.) → identity
  reusing `bvzeroExtendSymbol`/`bvsignExtendSymbol`/`bvextractSymbol` from Phase 1. Widths come from the source/target type names via `uintWidth?` (USize/ISize via the option). Each takes one explicit arg (the value); translate it and wrap.
  - `UIntW.toNat`/`IntW.toInt`/`UIntW.toUSize`-cross-config and similar → `throwEnvError` (Non-Goal: see spec). Be careful to distinguish reinterpret (same width, OK) from toNat/toInt (cross-theory, error).

- [ ] **Step 4: Run, pass.** 6 ✅ Valid + 1 ✅ Expected Falsified. Verify `toNat` errors cleanly (scratch: `#blaster [∀ (x : UInt8), x.toNat ≥ 0]` → error, delete).

- [ ] **Step 5: Commit** `feat(uint,int): cross-width conversions (zero/sign-extend, extract)`.

---

## Task 6: USize/ISize configurable width option + registration + regression

**Files:** `Blaster/Command/Options.lean`, `Blaster/Command/Syntax.lean`, `Blaster/Smt/Translate/Quantifier.lean`; create `Tests/Smt/SmtUInt.lean`, `Tests/Smt/SmtInt.lean`; modify `Tests/Smt.lean`; create `Tests/Smt/SmtUInt/SmtUSizeWidth.lean`.

- [ ] **Step 1: Add the option.** In `Blaster/Command/Options.lean` `BlasterOptions`, add `usizeWidth : Nat := 64`. In `Blaster/Command/Syntax.lean`, add (mirroring `max-depth` at lines 39/54):
  - `syntax "(usize-width:" num ")" : solveOption`
  - parser arm: `| `(solveOption| (usize-width: $n:num)) => return { sOpts with usizeWidth := n.getNat }`
  - Validate ∈ {32, 64} (error otherwise) at parse or first use.

- [ ] **Step 2: Wire into `translateUIntType`.** Replace the Task-1 hardcoded `pure 64` for USize/ISize with `pure (← get).optEnv.options.solverOptions.usizeWidth` (resolve the exact accessor path; default 64). Remove the `TODO(Task 6)` marker.

- [ ] **Step 3: Test both widths** (`SmtUSizeWidth.lean`):
```lean
import Blaster
namespace Test.SmtUSizeWidth

-- default width 64
#blaster [∀ (x : USize), x = x]
#blaster [(0 : USize) = 0]

-- explicit 32-bit: 2^32 wraps to 0
#blaster (usize-width: 32) [(4294967296 : USize) = 0]

-- at 64-bit that same literal is NOT 0
#blaster (gen-cex: 0) (solve-result: 1) [(4294967296 : USize) = 0]
```
Verify the chosen width changes the translation (the 32 vs 64 tests give opposite results). If USize literals don't reach SMT cleanly, record and adjust.

- [ ] **Step 4: Register suites.** `Tests/Smt/SmtUInt.lean` (alphabetical imports of SmtUIntArith/Conv/Div/Lit/Sort/USizeWidth), `Tests/Smt/SmtInt.lean` (SmtIntArith/Div), add both to `Tests/Smt.lean` alphabetically.

- [ ] **Step 5: Full regression.** `lake build Blaster && LEAN_NUM_THREADS=5 lake test` — zero `❌`/`error:`. All prior suites (BitVec, Fin, SMTArray, Nat, …) + Issue3 stay green.

- [ ] **Step 6: Commit** `feat(usize): configurable usize-width option; register UInt/Int suites`.

---

## Self-review checklist (after writing, before execution)

- Spec Phase 3 coverage: 12 types → BitVec sort ✅ T1; wrapper erasure ✅ T2; literals ✅ T2; arith/bitwise/shift ✅ T3; unsigned vs signed comparison ✅ T3; division (unsigned/signed) ✅ T4; cross-width conversions (zero/sign-extend, extract, reinterpret) ✅ T5; `toNat`/`toInt` → error ✅ T5; USize/ISize configurable width (default 64, ∈{32,64}) ✅ T1+T6.
- Soundness guards: wrap-around order-law violations Falsified (T3); signed vs unsigned correctness (Int8.lt→slt, T3); div-by-zero (T4); USize width actually affects results (T6).
- Discovery-driven: exact 4.24 constant names/forms for wrappers, literals, ops, and conversions — every op task's Step 2 records them before the mapping. Path A (unfold-to-BitVec) is expected for arith/compare/div; conversions are most likely path B.
- Cache-name collision (T1 Step 4): UInt8 and BitVec 8 must not emit duplicate `@isBitVec_8`.

## Out of scope (Phase 4)

`Vector α n` — static-length arrays with faithful pointwise equality; reuses the SMTArray sort + Fin index machinery. Its own plan.


