# Indexed Types Phase 1 — BitVec Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Translate `BitVec n` (literal `n`) propositions to SMT `(_ BitVec n)` queries: sort, literals, full operation set, and division-semantics wrappers.

**Architecture:** Per-type hooks at the four seams (type translation in `Quantifier.lean`, op translation in `Application.lean`, literal recognition in `Translate.lean`/`Optimize/Expr.lean`, opacification + folding in `Optimize/`). Spec: `docs/superpowers/specs/2026-06-11-indexed-types-design.md`.

**Tech Stack:** Lean 4 (toolchain v4.24.0), Z3 ≥ 4.15.2, lake.

**Branch:** `feat/indexed-types`.

---

## Context for a zero-context engineer

- Build: `make build_blaster` (or `lake build Blaster`). Run one test file: `lake env lean Tests/Smt/SmtBitVec/<File>.lean`. Full suite: `LEAN_NUM_THREADS=5 lake test`.
- A test is a `#blaster [<proposition>]` command. Default expectation is **Valid** (logs `✅ Valid`; a wrong result logs `❌` and the file still compiles — read the output!). For expected-counterexample tests use `#blaster (gen-cex: 0) (solve-result: 1) [...]` (logs `✅ Expected Falsified`).
- Pipeline: `#blaster` elaborates the prop → `Optimize.main` rewrites it (unfolds every definition NOT in `Blaster/Optimize/Opaque.lean:opaqueFuns`) → `translateExpr` (Blaster/Smt/Translate.lean) emits SMT → Z3 `check-sat` on the negation (`unsat` = Valid).
- **Why opacification matters:** if `BitVec.add` is not in `opaqueFuns`, the optimizer unfolds it into `BitVec.ofFin`/`Fin` internals and translation fails on those. Every op we translate must be registered opaque FIRST.
- Key dispatch points you will touch:
  - `Blaster/Smt/Translate/Quantifier.lean:1277` `translateTypeAux` — type → sort. `e := t.getAppFn`; opaque (non-parameterized) types go through `translateOpaqueType` (line 1263). Parameterized `BitVec n` must be intercepted BEFORE it, using the full app `t`.
  - `Blaster/Smt/Translate/Application.lean:305` `translateOpaqueFun` — maps an opaque function name to an SMT identifier. Called from `translateFullyApplied?` (line 1162), which requires the name in `fullyAppliedConst` (line 19) and **exact arity** `pInfo.paramsInfo.size == args.size` (implicit width arg counts!).
  - `createAppN` (Application.lean:529) drops implicit args automatically — the width never reaches the SMT term.
  - `Blaster/Smt/Translate.lean:18-20` — literal hooks (`isIntValue?` etc.) run before everything else.
  - Caches: `indTypeInstCache` (type expr → `IndTypeDeclaration`, see `updateIndInstCache` Quantifier.lean:176; the qualifier predicate machinery `createPredQualifierApp` looks types up here), `funInstCache` (fn expr → SMT ident, see `getOpaqueSmtEquivFun` Application.lean:277).
- Lean 4.24 core facts (VERIFY in Step 1 of each op task — the failure message of the first test run names the constant that actually survives optimization):
  - `5#8` ≡ `BitVec.ofNat 8 5`; kernel-normalized literal form is `BitVec.ofFin w (Fin.mk (2^w) v proof)` (same shape as `isUInt32Value?`, `Blaster/Optimize/Expr.lean:301`).
  - `x < y` elaborates to `LT.lt _ instLTBitVec x y`; since `BitVec ∉ relationalCompatibleTypes`, `isOpaqueRelational` (Optimize/Env.lean:1202) returns false and the instance unfolds to `BitVec.lt` (Prop). Similarly `≤` → `BitVec.le`, `/` → `BitVec.udiv`, `%` → `BitVec.umod`, `+` → `BitVec.add`, `&&&` → `BitVec.and`, `<<<` → `BitVec.shiftLeft`, `++` → `BitVec.append`.
- **Soundness rule (do not violate):** never add `BitVec` to `relationalCompatibleTypes` (`Blaster/Optimize/Opaque.lean:74`) — the relational rewrite rules assume order laws that wrap-around arithmetic breaks. Task 9 adds regression tests guarding this.
- SMT syntax helpers live in `Blaster/Smt/Term.lean` (symbols/builders) over the AST in `Blaster/Smt/Syntax.lean`. Indexed identifiers like `(_ extract 7 0)` are emitted via `mkReservedSymbol` containing the raw string — `SmtSymbol.toString` prints `ReservedSymbol` verbatim (Syntax.lean:168), so `mkSmtAppN (.SimpleIdent (mkReservedSymbol "(_ extract 7 0)")) #[x]` renders `((_ extract 7 0) x)`.

## File structure (whole phase)

| File | Responsibility |
|---|---|
| `Blaster/Smt/Term.lean` (modify) | BitVec sort/op symbols + term builders |
| `Blaster/Smt/Env.lean` (modify) | Per-width `define-fun` division wrappers |
| `Blaster/Smt/Translate/Quantifier.lean` (modify) | `translateBitVecType` + intercept in `translateTypeAux` |
| `Blaster/Smt/Translate/Application.lean` (modify) | Op-name → SMT mapping, shift/extract/extend/rotate/div translation |
| `Blaster/Smt/Translate.lean` (modify) | BitVec literal hook in `translateExpr` |
| `Blaster/Optimize/Expr.lean` (modify) | `isBitVecValue?` recognizer |
| `Blaster/Optimize/Env.lean` (modify) | `mkBitVecLitExpr` |
| `Blaster/Optimize/Opaque.lean` (modify) | Register all BitVec ops opaque |
| `Blaster/Optimize/Rewriting/OptimizeBitVec.lean` (create) | Constant folding + identity rules |
| `Blaster/Optimize/Rewriting/OptimizeApp.lean` (modify) | Dispatch `optimizeBitVec?` |
| `Tests/Smt/SmtBitVec.lean` (create) + `Tests/Smt/SmtBitVec/*.lean` (create) | Test suites |
| `Tests/Smt.lean` (modify) | Register suite |

---

### Task 1: BitVec sort translation (type hook + qualifier)

**Files:**
- Modify: `Blaster/Smt/Term.lean` (after `pemptySort`, ~line 82)
- Modify: `Blaster/Smt/Translate/Quantifier.lean` (new fn before `translateOpaqueType` ~line 1259; hook in `translateTypeAux` ~line 1283)
- Create: `Tests/Smt/SmtBitVec/SmtBitVecSort.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecSort

/-! # Test cases to validate BitVec sort translation -/

#blaster [∀ (x y : BitVec 8), x = y → y = x]

#blaster [∀ (x : BitVec 8) (y : BitVec 16), x = x ∧ y = y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x = y]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecSort.lean`
Expected: error mentioning `translateNonOpaqueType`/`translateOpaqueType` or `BitVec` (the type head reaches the inductive-translation path and fails).

- [ ] **Step 3: Add sort builders to `Blaster/Smt/Term.lean`**

Replace the TODO at line 84 (`-- TODO: add other sort once supported, e.g., BitVec, ...`) with:

```lean
/-! Smt BitVec symbol for width `w`, i.e., the indexed sort `(_ BitVec w)`
    rendered via a reserved symbol. -/
def bitvecSymbol (w : Nat) : SmtSymbol := mkReservedSymbol s!"BitVec_{w}"

/-! Smt BitVec Sort `(_ BitVec w)` (builtin indexed sort). -/
def bitvecSort (w : Nat) : SortExpr :=
  paramSort (mkReservedSymbol "_")
    #[.SymbolSort (mkReservedSymbol "BitVec"), .SymbolSort (mkReservedSymbol s!"{w}")]

-- TODO: add other sort once supported, e.g., Unicode (for char), Seq, etc
```

(`bitvecSymbol` is only the *name* used for the `@isBitVec_8` qualifier predicate; the sort itself is the `ParamSort`, which `SortExpr.toString` renders as `(_ BitVec 8)`.)

- [ ] **Step 4: Add `translateBitVecType` + hook in `Quantifier.lean`**

Insert immediately before `translateOpaqueType` (~line 1259):

```lean
/-- Translate `BitVec w` (literal `w` only) to the builtin Smt sort `(_ BitVec w)`.
    A trivial predicate qualifier `@isBitVec_{w}` is defined (the Smt sort is exact).
    An error is triggered when the width is not a Nat literal.
    Assume `t := Expr.app (Expr.const ``BitVec _) widthArg`.
-/
def translateBitVecType (t : Expr) : TranslateEnvT SortExpr := do
 match (← get).smtEnv.indTypeInstCache.get? t with
 | some decl => return decl.instSort
 | none =>
    let some w := isNatValue? t.appArg!
      | throwEnvError "translateBitVecType: BitVec with non-literal width is not supported, got {reprStr t.appArg!}"
    let decl ← updateIndInstCache t (bitvecSymbol w) (bitvecSort w) (isReservedSymbol := true)
    definePredQualifier decl.instName #[bitvecSort w] (some true)
    return decl.instSort
```

In `translateTypeAux`, change the `Expr.const ..` branch (line 1283-1287) to intercept the parameterized type before the opaque path:

```lean
   | Expr.const ``BitVec _ => translateBitVecType t
   | Expr.const .. =>
      if let some r ← translateOpaqueType e then return r
      translateNonOpaqueType e t.getAppArgs
        (λ a b => translateTypeAux termTranslator a b)
        termTranslator topts
```

Also update the stale doc comment at line 1261 (`TODO: update function when opacifying other Lean inductive types (e.g., BitVector, Char, etc).` → drop `BitVector,`).

- [ ] **Step 5: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecSort.lean`
Expected: two `✅ Valid`, one `✅ Expected Falsified`, no errors.
If the non-literal-width guard fires on `8`: the width arg is not yet a raw `Expr.lit` at type-translation time — extend the guard to `let some w := isNatValue? (← whnfD t.appArg!)` (add `open Lean Meta` import is already present) and note what form was observed in the commit message.

- [ ] **Step 6: Manually verify the error path**

Run a scratch check (do not commit):
```lean
#blaster [∀ (n : Nat) (x : BitVec n), x = x]
```
Expected: error `translateBitVecType: BitVec with non-literal width is not supported ...`.

- [ ] **Step 7: Commit**

```bash
git add Blaster/Smt/Term.lean Blaster/Smt/Translate/Quantifier.lean Tests/Smt/SmtBitVec/SmtBitVecSort.lean
git commit -m "feat(bitvec): translate BitVec n type to SMT (_ BitVec n) sort"
```

---

### Task 2: BitVec literals

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean` (add `BitVec.ofNat`)
- Modify: `Blaster/Optimize/Expr.lean` (add `isBitVecValue?` after `isUInt32Value?` ~line 314)
- Modify: `Blaster/Smt/Term.lean` (add `bitvecLitSmt`)
- Modify: `Blaster/Smt/Translate.lean` (literal hook, line 21)
- Create: `Tests/Smt/SmtBitVec/SmtBitVecLit.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecLit

/-! # Test cases to validate BitVec literal translation -/

#blaster [∀ (x : BitVec 8), x = 254#8 → x ≠ 255#8]

#blaster [∀ (x : BitVec 8), x = 5#8 → x = 5#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≠ 200#8]

-- ofNat wraps modulo 2^w
#blaster [∀ (x : BitVec 8), x = 256#8 → x = 0#8]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecLit.lean`
Expected: error from the optimizer or translator naming `BitVec.ofNat`, `BitVec.ofFin` or `Fin.mk`. **Record which constant appears** — it tells you which literal form survives optimization.

- [ ] **Step 3: Register `BitVec.ofNat` opaque**

In `Blaster/Optimize/Opaque.lean`, extend `opaqueFuns` (before the `-- String operators` group):

```lean
    -- BitVec literal constructor (kept opaque so `5#8` survives optimization;
    -- recognized by isBitVecValue? and emitted as an Smt literal)
    ``BitVec.ofNat,
```

- [ ] **Step 4: Add `isBitVecValue?` to `Blaster/Optimize/Expr.lean`**

After `isUInt32Value?` (~line 314):

```lean
/-- Determine if `e` is a `BitVec` literal expression, i.e., either
     - `BitVec.ofNat w v` (opaque form, value taken modulo 2^w); or
     - `BitVec.ofFin w (Fin.mk s v isLt)` (kernel-normalized form)
    with `w`, `v` Nat literals, and return `some (w, v % 2^w)`.
    Otherwise return `none`.
-/
def isBitVecValue? (e : Expr) : Option (Nat × Nat) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``BitVec.ofNat _)
      (Expr.lit (Literal.natVal w))) (Expr.lit (Literal.natVal v)) =>
      some (w, v % (2 ^ w))
  | Expr.app (Expr.app (Expr.const ``BitVec.ofFin _)
      (Expr.lit (Literal.natVal w))) fn =>
      match fn with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Fin.mk _) _)
          (Expr.lit (Literal.natVal v))) _ => some (w, v % (2 ^ w))
      | _ => none
  | _ => none
```

- [ ] **Step 5: Add `bitvecLitSmt` to `Blaster/Smt/Term.lean`** (next to `natLitSmt`, ~line 400)

```lean
/-! Convert a BitVec literal of value `v` and width `w` to its Smt
    representation `(_ bv{v} w)`. -/
def bitvecLitSmt (v : Nat) (w : Nat) : SmtTerm :=
  mkSimpleSmtAppN underSymbol
    #[.SmtIdent (.SimpleIdent (mkReservedSymbol s!"bv{v}")), .NumTerm w]
```

- [ ] **Step 6: Hook into `translateExpr`** (`Blaster/Smt/Translate.lean`, replace lines 20-21)

```lean
    if let some s := isStrValue? e then return strLitSmt s
    if let some (w, v) := isBitVecValue? e then return bitvecLitSmt v w
    -- TODO: consider other sort once supported (e.g., Char, etc)
```

- [ ] **Step 7: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecLit.lean`
Expected: three `✅ Valid`, one `✅ Expected Falsified`. If failure names a different literal shape (e.g. `OfNat.ofNat` not unfolded), extend `isBitVecValue?` with the observed pattern and re-run.

- [ ] **Step 8: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Optimize/Expr.lean Blaster/Smt/Term.lean Blaster/Smt/Translate.lean Tests/Smt/SmtBitVec/SmtBitVecLit.lean
git commit -m "feat(bitvec): recognize BitVec literals and emit (_ bvV w) terms"
```

---

### Task 3: Arithmetic and bitwise operations

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean`
- Modify: `Blaster/Smt/Term.lean` (op symbols, after `bitvecLitSmt`)
- Modify: `Blaster/Smt/Translate/Application.lean` (`fullyAppliedConst` line 19; `translateOpaqueFun` line 305)
- Create: `Tests/Smt/SmtBitVec/SmtBitVecArith.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecArith

/-! # Test cases to validate BitVec arithmetic/bitwise semantics -/

#blaster [∀ (x y : BitVec 8), x + y = y + x]

#blaster [∀ (x y z : BitVec 8), (x + y) + z = x + (y + z)]

#blaster [∀ (x : BitVec 8), x + 0#8 = x]

-- wrap-around: adding 255 is subtracting 1 mod 2^8
#blaster [∀ (x : BitVec 8), x + 255#8 = x - 1#8]

#blaster [∀ (x : BitVec 8), x - x = 0#8]

#blaster [∀ (x : BitVec 8), -x = 0#8 - x]

#blaster [∀ (x y : BitVec 8), x * y = y * x]

-- de Morgan
#blaster [∀ (x y : BitVec 8), ~~~(x &&& y) = ~~~x ||| ~~~y]

#blaster [∀ (x : BitVec 8), x ^^^ x = 0#8]

#blaster [∀ (x : BitVec 8), x &&& 255#8 = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x + y = x]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecArith.lean`
Expected: optimizer unfolds `BitVec.add` (not yet opaque) and translation errors on `BitVec.ofFin`/`Fin` internals or `toNat`. Record the constants named — they confirm the op names to register (`HAdd` unfolds to `BitVec.add`, `~~~` to `BitVec.not`, `^^^` to `BitVec.xor`, etc.).

- [ ] **Step 3: Register ops opaque** (`Blaster/Optimize/Opaque.lean`, extend the BitVec group from Task 2)

```lean
    -- BitVec operators (arith is modulo 2^w; ofNat kept opaque for literals)
    ``BitVec.ofNat,
    ``BitVec.add,
    ``BitVec.sub,
    ``BitVec.mul,
    ``BitVec.neg,
    ``BitVec.and,
    ``BitVec.or,
    ``BitVec.xor,
    ``BitVec.not,
```

- [ ] **Step 4: Add SMT symbols** (`Blaster/Smt/Term.lean`, after `bitvecLitSmt`)

```lean
/-! ## BitVec Smt operator symbols (QF_BV theory). -/

def bvaddSymbol : SmtSymbol := mkReservedSymbol "bvadd"
def bvsubSymbol : SmtSymbol := mkReservedSymbol "bvsub"
def bvmulSymbol : SmtSymbol := mkReservedSymbol "bvmul"
def bvnegSymbol : SmtSymbol := mkReservedSymbol "bvneg"
def bvandSymbol : SmtSymbol := mkReservedSymbol "bvand"
def bvorSymbol  : SmtSymbol := mkReservedSymbol "bvor"
def bvxorSymbol : SmtSymbol := mkReservedSymbol "bvxor"
def bvnotSymbol : SmtSymbol := mkReservedSymbol "bvnot"
```

- [ ] **Step 5: Map names in `translateOpaqueFun`** (`Application.lean`, add before the catch-all `| _ =>`)

```lean
  | ``BitVec.add => getOpaqueSmtEquivFun f bvaddSymbol
  | ``BitVec.sub => getOpaqueSmtEquivFun f bvsubSymbol
  | ``BitVec.mul => getOpaqueSmtEquivFun f bvmulSymbol
  | ``BitVec.neg => getOpaqueSmtEquivFun f bvnegSymbol
  | ``BitVec.and => getOpaqueSmtEquivFun f bvandSymbol
  | ``BitVec.or  => getOpaqueSmtEquivFun f bvorSymbol
  | ``BitVec.xor => getOpaqueSmtEquivFun f bvxorSymbol
  | ``BitVec.not => getOpaqueSmtEquivFun f bvnotSymbol
```

And add the same eight names to `fullyAppliedConst` (line 19, after the `Nat.pow` entry):

```lean
    ``BitVec.add,
    ``BitVec.sub,
    ``BitVec.mul,
    ``BitVec.neg,
    ``BitVec.and,
    ``BitVec.or,
    ``BitVec.xor,
    ``BitVec.not,
```

(`createAppN` drops the implicit width argument automatically — `BitVec.add : {n} → BitVec n → BitVec n → BitVec n` arrives with `args.size == 3 == pInfo.paramsInfo.size`, and only the two explicit args are translated.)

- [ ] **Step 6: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecArith.lean`
Expected: ten `✅ Valid`, one `✅ Expected Falsified`. If an op still unfolds, the recorded constant from Step 2 differs from the registered one — adjust `opaqueFuns`/`translateOpaqueFun`/`fullyAppliedConst` to the observed name (all three lists must agree).

- [ ] **Step 7: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Term.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtBitVec/SmtBitVecArith.lean
git commit -m "feat(bitvec): translate arithmetic and bitwise ops to QF_BV"
```

---

### Task 4: Comparisons (unsigned + signed)

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean`
- Modify: `Blaster/Smt/Term.lean`
- Modify: `Blaster/Smt/Translate/Application.lean`
- Create: `Tests/Smt/SmtBitVec/SmtBitVecCompare.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecCompare

/-! # Test cases to validate BitVec comparison semantics -/

#blaster [∀ (x y : BitVec 8), x < y → ¬ (y < x)]

#blaster [∀ (x y : BitVec 8), x ≤ y ∨ y ≤ x]

#blaster [∀ (x : BitVec 8), x ≤ 255#8]

#blaster [∀ (x y : BitVec 8), x.ult y → x ≠ y]

-- signed: 255#8 is -1, so slt 0
#blaster [(255#8).slt 0#8 = true]

#blaster [∀ (x y : BitVec 8), x.sle y ∨ y.sle x]

-- CRITICAL soundness guards: wrap-around breaks Int-style order reasoning.
-- These MUST be Falsified; if any reports Valid, BitVec leaked into the
-- relational rewriting rules (see relationalCompatibleTypes).
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x ≤ x + 1#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x < x + 1#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BitVec 8), x < y → x + 1#8 ≤ y + 1#8]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecCompare.lean`
Expected: error after `LT.lt`/`LE.le` instances unfold (BitVec is NOT in `relationalCompatibleTypes`, so `isOpaqueRelational` returns false and the optimizer unfolds the instance). Record what they unfold to — expected `BitVec.lt`/`BitVec.le` (Prop) and `BitVec.ult/ule/slt/sle` (Bool). If they unfold further (into `toNat` comparisons), register the *first* named BitVec constant in the unfold chain instead.

- [ ] **Step 3: Register comparison ops opaque** (`Opaque.lean`, extend BitVec group)

```lean
    ``BitVec.lt,  -- Prop-level <, via instLTBitVec
    ``BitVec.le,  -- Prop-level ≤, via instLEBitVec
    ``BitVec.ult,
    ``BitVec.ule,
    ``BitVec.slt,
    ``BitVec.sle,
```

**Do NOT add `BitVec` to `relationalCompatibleTypes`** (same file, line 74) — wrap-around arithmetic violates the order laws those rules assume.

- [ ] **Step 4: Add symbols** (`Term.lean`)

```lean
def bvultSymbol : SmtSymbol := mkReservedSymbol "bvult"
def bvuleSymbol : SmtSymbol := mkReservedSymbol "bvule"
def bvsltSymbol : SmtSymbol := mkReservedSymbol "bvslt"
def bvsleSymbol : SmtSymbol := mkReservedSymbol "bvsle"
```

- [ ] **Step 5: Map in `translateOpaqueFun` + `fullyAppliedConst`** (`Application.lean`)

```lean
  | ``BitVec.lt
  | ``BitVec.ult => getOpaqueSmtEquivFun f bvultSymbol
  | ``BitVec.le
  | ``BitVec.ule => getOpaqueSmtEquivFun f bvuleSymbol
  | ``BitVec.slt => getOpaqueSmtEquivFun f bvsltSymbol
  | ``BitVec.sle => getOpaqueSmtEquivFun f bvsleSymbol
```

Add all six names to `fullyAppliedConst`.
(Bool-valued `ult` etc. map to the Bool-sorted SMT predicates directly — the existing `= true` normalization in `translateEq?` handles the `Bool`/`Prop` boundary, as for `Nat.ble`.)

- [ ] **Step 6: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecCompare.lean`
Expected: six `✅ Valid`, three `✅ Expected Falsified`. **If any soundness guard reports `❌ Unexpected Valid`, STOP — a rewrite rule is treating BitVec as an ordered ring; find and fix before proceeding.**

- [ ] **Step 7: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Term.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtBitVec/SmtBitVecCompare.lean
git commit -m "feat(bitvec): translate unsigned/signed comparisons with wrap-around soundness guards"
```

---

### Task 5: Division wrappers (udiv/umod/sdiv/smod/srem)

Lean: `x.udiv 0 = 0`, `x.sdiv 0 = 0`, `x.umod 0 = x`, `x.smod 0 = x`, `x.srem 0 = x`. SMT: `bvudiv x 0 = allOnes`, `bvsdiv x 0 = ±1`, `bvurem x 0 = x`, `bvsmod x 0 = x`, `bvsrem x 0 = x`. So `udiv`/`sdiv` need per-width `define-fun` wrappers; the three remainder ops translate directly.

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean`
- Modify: `Blaster/Smt/Term.lean`
- Modify: `Blaster/Smt/Env.lean` (after `defineNatSub`, ~line 382)
- Modify: `Blaster/Smt/Translate/Application.lean`
- Create: `Tests/Smt/SmtBitVec/SmtBitVecDiv.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecDiv

/-! # Test cases to validate BitVec division semantics (Lean: x/0 = 0) -/

#blaster [∀ (x : BitVec 8), x / 0#8 = 0#8]

#blaster [∀ (x : BitVec 8), x % 0#8 = x]

#blaster [∀ (x : BitVec 8), x / 1#8 = x]

#blaster [∀ (x y : BitVec 8), y ≠ 0#8 → x / y ≤ x]

#blaster [∀ (x y : BitVec 8), y ≠ 0#8 → x % y < y]

#blaster [∀ (x : BitVec 8), x.sdiv 0#8 = 0#8]

#blaster [∀ (x : BitVec 8), x.smod 0#8 = x]

#blaster [∀ (x : BitVec 8), x.srem 0#8 = x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x / 0#8 = 255#8]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecDiv.lean`
Expected: error after `/`/`%` instances unfold. Record the constants (expected `BitVec.udiv`, `BitVec.umod`).

- [ ] **Step 3: Register opaque** (`Opaque.lean`, BitVec group)

```lean
    -- Division: Lean x/0 = 0 mismatches SMT bvudiv/bvsdiv — wrapped per width
    ``BitVec.udiv,
    ``BitVec.umod,
    ``BitVec.sdiv,
    ``BitVec.smod,
    ``BitVec.srem,
```

- [ ] **Step 4: Add symbols** (`Term.lean`)

```lean
def bvuremSymbol : SmtSymbol := mkReservedSymbol "bvurem"
def bvsmodSymbol : SmtSymbol := mkReservedSymbol "bvsmod"
def bvsremSymbol : SmtSymbol := mkReservedSymbol "bvsrem"

/-! Per-width wrapper names for division ops whose div-by-zero semantics
    differ between Lean (0) and Smt-Lib (allOnes / ±1).
    NOTE: These functions are defined during translation whenever required.
-/
def bvudivSymbol (w : Nat) : SmtSymbol := mkReservedSymbol s!"@BitVec.udiv_{w}"
def bvsdivSymbol (w : Nat) : SmtSymbol := mkReservedSymbol s!"@BitVec.sdiv_{w}"
```

- [ ] **Step 5: Add wrapper definitions** (`Env.lean`, after `defineNatSub` — same shape as `defineBinFun`, which is `private`, so inline the pattern)

```lean
/-- Define the BitVec.udiv Smt wrapper for width `w`, i.e.,
     @BitVec.udiv_w x y := (ite (= y (_ bv0 w)) (_ bv0 w) (bvudiv x y))
    (Lean division-by-zero yields 0; Smt bvudiv yields allOnes.)
-/
def defineBitVecUDiv (w : Nat) : TranslateEnvT Unit := do
  let xsym := mkReservedSymbol "@x"
  let ysym := mkReservedSymbol "@y"
  let xId := smtSimpleVarId xsym
  let yId := smtSimpleVarId ysym
  let zero := bitvecLitSmt 0 w
  let divApp := mkSimpleSmtAppN (mkReservedSymbol "bvudiv") #[xId, yId]
  let body := iteSmt (eqSmt yId zero) zero divApp
  defineFun (bvudivSymbol w) #[(xsym, bitvecSort w), (ysym, bitvecSort w)] (bitvecSort w) body

/-- Define the BitVec.sdiv Smt wrapper for width `w`, i.e.,
     @BitVec.sdiv_w x y := (ite (= y (_ bv0 w)) (_ bv0 w) (bvsdiv x y))
-/
def defineBitVecSDiv (w : Nat) : TranslateEnvT Unit := do
  let xsym := mkReservedSymbol "@x"
  let ysym := mkReservedSymbol "@y"
  let xId := smtSimpleVarId xsym
  let yId := smtSimpleVarId ysym
  let zero := bitvecLitSmt 0 w
  let divApp := mkSimpleSmtAppN (mkReservedSymbol "bvsdiv") #[xId, yId]
  let body := iteSmt (eqSmt yId zero) zero divApp
  defineFun (bvsdivSymbol w) #[(xsym, bitvecSort w), (ysym, bitvecSort w)] (bitvecSort w) body
```

- [ ] **Step 6: Translate with per-width caching** (`Application.lean`, after `translateInttoNat` ~line 270)

The wrapper is per width, but `translateOpaqueFun` receives only the head const `f`. Key the `funInstCache` on `f` applied to its width argument:

```lean
/-- Translate `BitVec.udiv`/`BitVec.sdiv` to a per-width Smt wrapper
    (Lean div-by-zero = 0, unlike bvudiv/bvsdiv). The wrapper is defined
    lazily once per (op, width) and cached on `f w`.
    An error is triggered when the width is not a Nat literal.
-/
def translateBitVecWrappedDiv (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT SmtQualifiedIdent := do
  if args.size != 3 then
    throwEnvError "translateBitVecWrappedDiv: fully applied {n} expected"
  let some w := isNatValue? args[0]!
    | throwEnvError "translateBitVecWrappedDiv: literal width expected for {n} but got {reprStr args[0]!}"
  let instApp := mkApp f args[0]!
  match (← get).smtEnv.funInstCache.get? instApp with
  | some smtId => return smtId
  | none =>
      if n == ``BitVec.udiv then
        defineBitVecUDiv w
        updateFunInstCache instApp (bvudivSymbol w)
      else
        defineBitVecSDiv w
        updateFunInstCache instApp (bvsdivSymbol w)
```

In `translateOpaqueFun`:

```lean
  | ``BitVec.udiv
  | ``BitVec.sdiv => translateBitVecWrappedDiv f n args
  | ``BitVec.umod => getOpaqueSmtEquivFun f bvuremSymbol
  | ``BitVec.smod => getOpaqueSmtEquivFun f bvsmodSymbol
  | ``BitVec.srem => getOpaqueSmtEquivFun f bvsremSymbol
```

Add all five names to `fullyAppliedConst`.

- [ ] **Step 7: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecDiv.lean`
Expected: eight `✅ Valid`, one `✅ Expected Falsified`.

- [ ] **Step 8: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Term.lean Blaster/Smt/Env.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtBitVec/SmtBitVecDiv.lean
git commit -m "feat(bitvec): division ops with per-width div-by-zero wrappers"
```

---

### Task 6: Shifts

Three cases by shift-amount type: literal `Nat` → constant second operand; `BitVec w` amount → direct; variable `Nat` → error with guidance. Lean and SMT agree that shifts ≥ width yield 0 (sign-fill for `sshiftRight`) — no wrapper needed.

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean`
- Modify: `Blaster/Smt/Term.lean`
- Modify: `Blaster/Smt/Translate/Application.lean` (new translation fn + dispatch in `translateApp`)
- Create: `Tests/Smt/SmtBitVec/SmtBitVecShift.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecShift

/-! # Test cases to validate BitVec shift semantics -/

#blaster [∀ (x : BitVec 8), x <<< 1 = x * 2#8]

#blaster [∀ (x : BitVec 8), x <<< 0 = x]

-- shift ≥ width yields 0 in both Lean and Smt
#blaster [∀ (x : BitVec 8), x <<< 8 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 9 = 0#8]

#blaster [∀ (x : BitVec 8), x >>> 1 ≤ 127#8]

-- BitVec-by-BitVec shifts
#blaster [∀ (x y : BitVec 8), x <<< y = x <<< y]

#blaster [∀ (x : BitVec 8) (y : BitVec 8), 8#8 ≤ y → x <<< y = 0#8]

-- arithmetic shift preserves sign bit
#blaster [(128#8).sshiftRight 1 = 192#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x <<< 1 = x]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecShift.lean`
Expected: errors naming the unfolded shift constants. Record them: expected `BitVec.shiftLeft`/`BitVec.ushiftRight`/`BitVec.sshiftRight` (Nat amount) and `BitVec.shiftLeft'`-style or HShiftLeft-instance forms for the BitVec-by-BitVec case (in 4.24 these route through `BitVec.shiftLeft x (y.toNat)`-shaped definitions — register whatever named constant survives, e.g. `BitVec.instHShiftLeft` unfoldings; adjust the dispatch below to the observed names).

- [ ] **Step 3: Register opaque** (`Opaque.lean`)

```lean
    -- Shifts (Nat amount must be a literal; BitVec amount translates directly)
    ``BitVec.shiftLeft,
    ``BitVec.ushiftRight,
    ``BitVec.sshiftRight,
```

**Plus** the three bv-by-bv shift constants observed in Step 2. ⚠️ Double-backtick name literals (``` ``Name ```) fail to compile if the constant doesn't exist — so you CANNOT write a guessed name and fix later. Identify the real 4.24 names first (run Step 2; or check with `open BitVec in #check @BitVec.sshiftRight'` — likely candidates are `BitVec.shiftLeft'`-style primed names or the `HShiftLeft` instance unfoldings), then add exactly those.

- [ ] **Step 4: Add symbols** (`Term.lean`)

```lean
def bvshlSymbol  : SmtSymbol := mkReservedSymbol "bvshl"
def bvlshrSymbol : SmtSymbol := mkReservedSymbol "bvlshr"
def bvashrSymbol : SmtSymbol := mkReservedSymbol "bvashr"
```

- [ ] **Step 5: Add shift translation** (`Application.lean`)

Shifts cannot go through plain `createAppN`: the Nat-amount form needs its second argument converted to a width-`w` BitVec constant. Add after `translateBitVecWrappedDiv`:

```lean
/-- Translate BitVec shifts. For `BitVec.shiftLeft x (s : Nat)` (and the two
    right shifts), `s` must be a Nat literal and is emitted as `(_ bvS w)`;
    a variable Nat shift amount has no faithful fixed-width encoding and
    triggers an error suggesting the BitVec-amount form. BitVec-by-BitVec
    shifts translate directly.
    Assume `args := #[width, x, s]` (width implicit).
-/
def translateBitVecShift
  (n : Name) (args : Array Expr) (sym : SmtSymbol) (amountIsNat : Bool)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if args.size != 3 then
    throwEnvError "translateBitVecShift: fully applied {n} expected"
  let some w := isNatValue? args[0]!
    | throwEnvError "translateBitVecShift: literal width expected for {n}"
  let sx ← termTranslator args[1]!
  if amountIsNat then
    let some s := isNatValue? args[2]!
      | throwEnvError "translateBitVecShift: literal shift amount expected for {n}; use a `BitVec {w}` shift amount for symbolic shifts"
    return mkSimpleSmtAppN sym #[sx, bitvecLitSmt s w]
  else
    return mkSimpleSmtAppN sym #[sx, ← termTranslator args[2]!]
```

Dispatch in `translateApp` (Application.lean:987): add a `translateBitVecShift?` to the `where` block and call it in the `Expr.const n _` chain right after `translateFullyApplied?`:

```lean
    translateBitVecShift? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``BitVec.shiftLeft   => translateBitVecShift n args bvshlSymbol  true  termTranslator
      | ``BitVec.ushiftRight => translateBitVecShift n args bvlshrSymbol true  termTranslator
      | ``BitVec.sshiftRight => translateBitVecShift n args bvashrSymbol true  termTranslator
      -- plus the three bv-by-bv shift constants observed in Step 2 (see ⚠️ in
      -- Step 3 — must be the real names), each with amountIsNat := false
      | _ => return none
```

(Do NOT add shifts to `fullyAppliedConst` — they bypass `translateOpaqueFun` entirely.)

- [ ] **Step 6: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecShift.lean`
Expected: eight `✅ Valid`, one `✅ Expected Falsified`.

- [ ] **Step 7: Manually verify the variable-Nat-shift error** (scratch, not committed)

```lean
#blaster [∀ (x : BitVec 8) (s : Nat), x <<< s = x <<< s]
```
Expected: error `literal shift amount expected ... use a BitVec 8 shift amount`.

- [ ] **Step 8: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Term.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtBitVec/SmtBitVecShift.lean
git commit -m "feat(bitvec): shifts with literal-Nat and BitVec amounts"
```

---

### Task 7: Structure ops — append, extract, extend, rotate

All use SMT *indexed identifiers* (`(_ extract 7 0)` etc.), emitted as raw `ReservedSymbol` strings (see Context). All numeric indices must be Nat literals.

**Files:**
- Modify: `Blaster/Optimize/Opaque.lean`
- Modify: `Blaster/Smt/Translate/Application.lean`
- Create: `Tests/Smt/SmtBitVec/SmtBitVecStructure.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecStructure

/-! # Test cases to validate BitVec concat/extract/extend/rotate -/

#blaster [∀ (x : BitVec 8), (0#8 ++ x).extractLsb 7 0 = x]

#blaster [(0xAB#8 ++ 0xCD#8 : BitVec 16) = 0xABCD#16]

#blaster [∀ (x : BitVec 8), x.zeroExtend 16 ≤ 255#16]

-- signExtend of a negative value keeps the sign
#blaster [(255#8).signExtend 16 = 0xFFFF#16]

#blaster [(255#8).zeroExtend 16 = 0x00FF#16]

-- setWidth grows (zero-extends) and shrinks (truncates)
#blaster [(255#8).setWidth 16 = 0x00FF#16]

#blaster [(0xABCD#16).setWidth 8 = 0xCD#8]

#blaster [∀ (x : BitVec 8), x.rotateLeft 8 = x]

#blaster [(0x81#8).rotateLeft 1 = 0x03#8]

#blaster [(0x81#8).rotateRight 1 = 0xC0#8]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : BitVec 8), x.rotateLeft 1 = x]
```

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecStructure.lean`
Expected: errors naming `BitVec.append`, `BitVec.extractLsb`, `BitVec.zeroExtend`/`BitVec.setWidth`, `BitVec.signExtend`, `BitVec.rotateLeft`, `BitVec.rotateRight` (in 4.24, `zeroExtend` is an abbrev for `setWidth` — register the surviving name).

- [ ] **Step 3: Register opaque** (`Opaque.lean`)

```lean
    -- Structure ops (all indices must be literals)
    ``BitVec.append,
    ``BitVec.extractLsb,
    ``BitVec.extractLsb',
    ``BitVec.setWidth,    -- zeroExtend is an abbrev for setWidth
    ``BitVec.signExtend,
    ``BitVec.rotateLeft,
    ``BitVec.rotateRight,
```

- [ ] **Step 4: Add translation** (`Application.lean`, after `translateBitVecShift`)

`append` is a plain binary op (two implicit widths, two explicit args) — but `concat` needs no index, so route it through `translateOpaqueFun` with a plain symbol. The rest need literal index extraction and indexed identifiers:

In `Term.lean` style, add to `Term.lean`:

```lean
def bvconcatSymbol : SmtSymbol := mkReservedSymbol "concat"

/-! Indexed Smt identifiers (rendered verbatim as reserved symbols). -/
def bvextractSymbol (hi lo : Nat) : SmtSymbol := mkReservedSymbol s!"(_ extract {hi} {lo})"
def bvzeroExtendSymbol (k : Nat) : SmtSymbol := mkReservedSymbol s!"(_ zero_extend {k})"
def bvsignExtendSymbol (k : Nat) : SmtSymbol := mkReservedSymbol s!"(_ sign_extend {k})"
def bvrotateLeftSymbol (k : Nat) : SmtSymbol := mkReservedSymbol s!"(_ rotate_left {k})"
def bvrotateRightSymbol (k : Nat) : SmtSymbol := mkReservedSymbol s!"(_ rotate_right {k})"
```

In `Application.lean`:

```lean
/-- Translate BitVec structure ops requiring indexed Smt identifiers:
     - extractLsb hi lo x       → ((_ extract hi lo) x)        args := #[w, hi, lo, x]
     - extractLsb' start len x  → ((_ extract (start+len-1) start) x)  args := #[w, start, len, x]
     - setWidth v x  (v ≥ w)    → ((_ zero_extend (v-w)) x)    args := #[w, v, x]
     - setWidth v x  (v < w)    → ((_ extract (v-1) 0) x)
     - signExtend v x (v ≥ w)   → ((_ sign_extend (v-w)) x)
     - signExtend v x (v < w)   → ((_ extract (v-1) 0) x)      (Lean signExtend truncates when shrinking)
     - rotateLeft/Right x k     → ((_ rotate_left k) x)        args := #[w, x, k]
    All indices must be Nat literals; otherwise an error is triggered.
-/
def translateBitVecIndexed?
  (n : Name) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT (Option SmtTerm) := do
  let litArg (i : Nat) : TranslateEnvT Nat := do
    let some v := isNatValue? args[i]!
      | throwEnvError "translateBitVecIndexed: literal argument expected for {n} but got {reprStr args[i]!}"
    pure v
  match n with
  | ``BitVec.extractLsb => do
      let hi ← litArg 1; let lo ← litArg 2
      return some (mkSimpleSmtAppN (bvextractSymbol hi lo) #[← termTranslator args[3]!])
  | ``BitVec.extractLsb' => do
      let start ← litArg 1; let len ← litArg 2
      return some (mkSimpleSmtAppN (bvextractSymbol (start + len - 1) start) #[← termTranslator args[3]!])
  | ``BitVec.setWidth
  | ``BitVec.signExtend => do
      let w ← litArg 0; let v ← litArg 1
      let sx ← termTranslator args[2]!
      if v ≥ w then
        let sym := if n == ``BitVec.signExtend then bvsignExtendSymbol (v - w) else bvzeroExtendSymbol (v - w)
        return some (mkSimpleSmtAppN sym #[sx])
      else
        return some (mkSimpleSmtAppN (bvextractSymbol (v - 1) 0) #[sx])
  | ``BitVec.rotateLeft => do
      let k ← litArg 2
      return some (mkSimpleSmtAppN (bvrotateLeftSymbol k) #[← termTranslator args[1]!])
  | ``BitVec.rotateRight => do
      let k ← litArg 2
      return some (mkSimpleSmtAppN (bvrotateRightSymbol k) #[← termTranslator args[1]!])
  | _ => return none
```

Wire `translateBitVecIndexed?` into the `translateApp` dispatch chain (next to `translateBitVecShift?`). For `append`, add to `translateOpaqueFun` and `fullyAppliedConst`:

```lean
  | ``BitVec.append => getOpaqueSmtEquivFun f bvconcatSymbol
```

**Argument-position caveat:** the `args := #[...]` layouts above are from the 4.24 signatures (`extractLsb (hi lo : Nat) (x : BitVec w)`, `setWidth (v : Nat) (x : BitVec w)`, `rotateLeft (x : BitVec w) (n : Nat)` — note rotate takes `x` first). If Step 2's recorded unfoldings disagree, fix indices to match and note it in the commit.

- [ ] **Step 5: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecStructure.lean`
Expected: ten `✅ Valid`, one `✅ Expected Falsified`. (Lean `rotateLeft` rotates by `k % w`; SMT `(_ rotate_left k)` is also modular — `x.rotateLeft 8 = x` at width 8 checks this agreement.)

- [ ] **Step 6: Commit**

```bash
git add Blaster/Optimize/Opaque.lean Blaster/Smt/Term.lean Blaster/Smt/Translate/Application.lean Tests/Smt/SmtBitVec/SmtBitVecStructure.lean
git commit -m "feat(bitvec): append/extract/extend/rotate via indexed SMT identifiers"
```

---

### Task 8: Optimizer constant folding (`OptimizeBitVec.lean`)

Folding literal-only BitVec applications in the optimizer keeps queries small and lets fully-concrete goals resolve without Z3. Semantics MUST match Lean exactly — fold by evaluating Lean's own `BitVec` ops in meta code.

**Files:**
- Modify: `Blaster/Optimize/Env.lean` (add `mkBitVecLitExpr` after `mkIntLitExpr` ~line 1073)
- Create: `Blaster/Optimize/Rewriting/OptimizeBitVec.lean`
- Modify: `Blaster/Optimize/Rewriting/OptimizeApp.lean` (import + dispatch in `optimizeAppAux` line 61)
- Create: `Tests/Smt/SmtBitVec/SmtBitVecFold.lean`

- [ ] **Step 1: Write the failing test**

```lean
import Blaster

namespace Test.SmtBitVecFold

/-! # Test cases to validate BitVec constant folding (only-optimize: no solver) -/

#blaster (only-optimize: 1) [(200#8 + 100#8 : BitVec 8) = 44#8]

#blaster (only-optimize: 1) [(255#8 &&& 15#8 : BitVec 8) = 15#8]

#blaster (only-optimize: 1) [(~~~0#8 : BitVec 8) = 255#8]

#blaster (only-optimize: 1) [(7#8 * 100#8 : BitVec 8) = 188#8]

#blaster (only-optimize: 1) [(5#8 / 0#8 : BitVec 8) = 0#8]
```

(Check the exact `only-optimize` option key in `Blaster/Command/Options.lean` — it is the option that sets `solverOptions.onlyOptimize`; with it, a goal must fold to `True` to log `✅ Valid`.)

- [ ] **Step 2: Run it to verify it fails**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecFold.lean`
Expected: `⚠️ Undetermined` on each (ops are opaque, nothing folds, no solver runs).

- [ ] **Step 3: Add `mkBitVecLitExpr`** (`Optimize/Env.lean`)

```lean
/-- Create a BitVec literal expression `BitVec.ofNat w (v % 2^w)`.
    NOTE: `BitVec.ofNat` is opaque and recognized by `isBitVecValue?`.
-/
def mkBitVecLitExpr (w v : Nat) : TranslateEnvT Expr :=
  mkExpr (mkApp2 (mkConst ``BitVec.ofNat)
           (mkRawNatLit w) (mkRawNatLit (v % (2 ^ w))))
```

(If `mkRawNatLit` is unavailable in scope, use the same literal-construction helper `mkNatLitExpr` uses at line 1047.)

- [ ] **Step 4: Create `Blaster/Optimize/Rewriting/OptimizeBitVec.lean`**

```lean
import Lean
import Blaster.Optimize.Rewriting.Utils
import Blaster.Optimize.Env

open Lean Meta
namespace Blaster.Optimize

/-- Evaluate a binary BitVec op on literal values using Lean's own BitVec
    semantics (exactness over speed: folding MUST agree with the kernel). -/
private def evalBitVecBinOp (op : Name) (w v1 v2 : Nat) : Option Nat :=
  let x := BitVec.ofNat w v1
  let y := BitVec.ofNat w v2
  match op with
  | ``BitVec.add  => some (x + y).toNat
  | ``BitVec.sub  => some (x - y).toNat
  | ``BitVec.mul  => some (x * y).toNat
  | ``BitVec.and  => some (x &&& y).toNat
  | ``BitVec.or   => some (x ||| y).toNat
  | ``BitVec.xor  => some (x ^^^ y).toNat
  | ``BitVec.udiv => some (x / y).toNat
  | ``BitVec.umod => some (x % y).toNat
  | ``BitVec.sdiv => some (x.sdiv y).toNat
  | ``BitVec.smod => some (x.smod y).toNat
  | ``BitVec.srem => some (x.srem y).toNat
  | _ => none

/-- Apply constant-folding and identity rules on opaque BitVec applications:
     - binop V1 V2          ==> V1 "op" V2   (both literal)
     - BitVec.not V         ==> ~~~V
     - BitVec.neg V         ==> -V
     - x &&& 0 / 0 &&& x    ==> 0
     - x ||| 0 / 0 ||| x    ==> x
     - x ^^^ 0 / 0 ^^^ x    ==> x
     - x + 0 / 0 + x        ==> x
     - x - 0                ==> x
     - x * 1 / 1 * x        ==> x
     - x * 0 / 0 * x        ==> 0
    Return `none` when no rule applies (translation handles the rest).
-/
def optimizeBitVec? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  -- unary ops: args := #[w, x]
  if n == ``BitVec.not || n == ``BitVec.neg then
    let some w := isNatValue? args[0]! | return none
    let some (_, v) := isBitVecValue? args[1]! | return none
    let r := if n == ``BitVec.not then (~~~(BitVec.ofNat w v)).toNat else (-(BitVec.ofNat w v)).toNat
    return some (← mkBitVecLitExpr w r)
  -- binary ops: args := #[w, x, y]
  if args.size != 3 then return none
  let some w := isNatValue? args[0]! | return none
  let v1? := isBitVecValue? args[1]!
  let v2? := isBitVecValue? args[2]!
  match v1?, v2? with
  | some (_, v1), some (_, v2) =>
      match evalBitVecBinOp n w v1 v2 with
      | some r => return some (← mkBitVecLitExpr w r)
      | none => return none
  | _, _ => identityRules n w args v1? v2?

 where
  identityRules (n : Name) (w : Nat) (args : Array Expr)
      (v1? v2? : Option (Nat × Nat)) : TranslateEnvT (Option Expr) := do
    let x := args[1]!
    let y := args[2]!
    let isZero (v? : Option (Nat × Nat)) := v?.map (·.2) == some 0
    let isOne  (v? : Option (Nat × Nat)) := v?.map (·.2) == some 1
    match n with
    | ``BitVec.and =>
        if isZero v1? || isZero v2? then return some (← mkBitVecLitExpr w 0) else return none
    | ``BitVec.or
    | ``BitVec.xor
    | ``BitVec.add =>
        if isZero v1? then return some y
        else if isZero v2? then return some x else return none
    | ``BitVec.sub =>
        if isZero v2? then return some x else return none
    | ``BitVec.mul =>
        if isZero v1? || isZero v2? then return some (← mkBitVecLitExpr w 0)
        else if isOne v1? then return some y
        else if isOne v2? then return some x else return none
    | _ => return none

end Blaster.Optimize
```

- [ ] **Step 5: Dispatch from `optimizeAppAux`** (`OptimizeApp.lean`)

Add `import Blaster.Optimize.Rewriting.OptimizeBitVec` to the imports (line 11 area) and in `optimizeAppAux` after the `optimizeInt?` line (line 69):

```lean
  if let some e ← optimizeBitVec? f args then return e
```

- [ ] **Step 6: Run test to verify it passes**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtBitVec/SmtBitVecFold.lean`
Expected: five `✅ Valid` with no solver involved. Then re-run ALL Task 1-7 suites to confirm folding broke nothing:
`for f in Tests/Smt/SmtBitVec/*.lean; do lake env lean $f || break; done`

- [ ] **Step 7: Commit**

```bash
git add Blaster/Optimize/Env.lean Blaster/Optimize/Rewriting/OptimizeBitVec.lean Blaster/Optimize/Rewriting/OptimizeApp.lean Tests/Smt/SmtBitVec/SmtBitVecFold.lean
git commit -m "feat(bitvec): constant folding and identity rules in optimizer"
```

---

### Task 9: Suite registration, full regression, cleanup

**Files:**
- Create: `Tests/Smt/SmtBitVec.lean`
- Modify: `Tests/Smt.lean`

- [ ] **Step 1: Register the suite**

`Tests/Smt/SmtBitVec.lean`:

```lean
import Tests.Smt.SmtBitVec.SmtBitVecSort
import Tests.Smt.SmtBitVec.SmtBitVecLit
import Tests.Smt.SmtBitVec.SmtBitVecArith
import Tests.Smt.SmtBitVec.SmtBitVecCompare
import Tests.Smt.SmtBitVec.SmtBitVecDiv
import Tests.Smt.SmtBitVec.SmtBitVecShift
import Tests.Smt.SmtBitVec.SmtBitVecStructure
import Tests.Smt.SmtBitVec.SmtBitVecFold
```

`Tests/Smt.lean`: add `import Tests.Smt.SmtBitVec` (alphabetical, after `Benchmarks`).

- [ ] **Step 2: Full regression**

Run: `LEAN_NUM_THREADS=5 lake test`
Expected: entire suite green (pre-existing suites unaffected — scan output for `❌`).

- [ ] **Step 3: Cleanup stale TODOs**

Verify the BitVec mentions in the TODOs at `Blaster/Smt/Term.lean` (was line 84) and `Blaster/Smt/Translate.lean` (was line 21) were updated in Tasks 1-2; update `Blaster/Smt/Translate/Quantifier.lean` doc comment if missed.

- [ ] **Step 4: Commit**

```bash
git add Tests/Smt/SmtBitVec.lean Tests/Smt.lean
git commit -m "test(bitvec): register SmtBitVec suite in test driver"
```

---

## Self-review checklist (run after writing, before execution)

- Spec coverage (Phase 1 section): sort ✅ T1, literals ✅ T2, arith/bitwise ✅ T3, compare ✅ T4, div wrappers ✅ T5, shifts ✅ T6, concat/extract/extend/rotate ✅ T7, folding+opaque registration ✅ T2-T8, soundness guards ✅ T4/T9. `toNat`/`toInt` and variable widths are spec non-goals (error paths verified manually T1/T6).
- Known uncertainty, by design: exact 4.24 constant names for shift/extend unfoldings — every op task's Step 2 records the observed names before the mapping steps consume them. Where a name is a guess it is marked "adjust to observed names".

## Out of scope (later phases)

Phase 2 (`Fin` + `SMTArray`), Phase 3 (`UInt*/Int*/USize`), Phase 4 (`Vector`) get their own plans after this lands — they hook into the same seams and reuse the BitVec sort/op machinery built here.



