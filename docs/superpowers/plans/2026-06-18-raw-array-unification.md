# Raw `Array` Unification (Spec 2a) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make raw `Array α` support symbolic `get!`/`getD`/`set!`/`setIfInBounds`/`size` (incl. `a[i]!`) by routing it to Spec 1's sound datatype-pair SMT model.

**Architecture:** Route the `Array α` *type* to `translateArrayType` (Spec 1's datatype pair); opacify the Array-named ops so the translator won't unfold them to `Fin a.size`; intercept them in `translateApp` reusing Spec 1's `translateSMTArrayOp?` term-building; normalize polymorphic `getElem!`-on-`Array` to `Array.get!` so `a[i]!` funnels through the same path. Concrete `Array.mk` store-chains (Spec 2b) are built ONLY if the full suite shows a concrete reaching SMT.

**Tech Stack:** Lean 4, SMT-LIB 2 (Z3, logic `ALL`), the Blaster translator.

**Spec:** `docs/superpowers/specs/2026-06-18-raw-array-unification-design.md`

---

## Background for the implementer (verified facts)

- Spec 1 made `SMTArray α` an SMT datatype pair `(@mkSMTArray_v (@dataSMTArray_v (Array Int σ)) (@sizeSMTArray_v Int))` with a per-instance out-of-bounds default const `@dfltSMTArray_v`. The type translator is `translateArrayType` (`Blaster/Smt/Translate/Quantifier.lean`); the op translator is `translateSMTArrayOp?` (a `where`-helper of `translateApp` in `Blaster/Smt/Translate/Application.lean`); names come from `smtArrNames v` + the `smtArrNamesCache` (`Blaster/Optimize/Env.lean`). READ all of these before starting.
- `SMTArray.get/set/size` are definitionally `Array.get!/set!/size`, so the SMT terms are identical.
- Op signatures (args as seen via `Expr.withApp`, implicits included):
  - `@Array.get! {α} [Inhabited α] (a) (i)` → `[α, inst, a, i]` (a@2, i@3) — SAME layout as `SMTArray.get`.
  - `@Array.getD {α} (a) (i) (d)` → `[α, a, i, d]` (a@1, i@2, d@3) — has an EXPLICIT default `d`.
  - `@Array.set! {α} (a) (i) (v)` → `[α, a, i, v]` (a@1, i@2, v@3) — SAME layout as `SMTArray.set`.
  - `@Array.setIfInBounds {α} (a) (i) (v)` → `[α, a, i, v]`.
  - `@Array.size {α} (a)` → `[α, a]` (a@1).
  - `@getElem! {coll} {idx} {elem} {valid} [GetElem? …] [Inhabited elem] (collection) (index)` →
    `[collType, idxType, elemType, valid, getElemInst, inhabitedInst, collection, index]` (collection@6, index@7).
- `translateTypeAux` (`Quantifier.lean`, ~`:1503-1518`) dispatches `Expr.const ``Blaster.SMTArray`/`Vector`/`Fin`/`BitVec` arms before a generic `Expr.const ..` arm.
- The optimizer normalizes `Nat.beq → ==` in `optimizeNatBeq` (`Blaster/Optimize/Rewriting/OptimizeNat.lean:317`), dispatched in `optimizeAppAux` (`Blaster/Optimize/Rewriting/OptimizeApp.lean:62-71`). Pattern: `if !(← isOptimizeRecCall) then return mkAppN f b_args; setRestart; return <rewritten>`.
- `opaqueFuns` list with `SMTArray.get/set/size` is in `Blaster/Optimize/Opaque.lean` (~`:140-143`).
- All FixedIssues (Issue3/11/16) are green today and do NOT push raw `Array` through the SMT array path (optimizer reduces concretes first). `only-optimize: 1` (Issue2/4) = no SMT translation at all.

---

## Task 1: Route `Array α` type + intercept named Array ops

After this task, NAMED ops (`a.get! i`, `a.getD i d`, `a.set! i v`, `a.setIfInBounds i v`, `a.size`) work on symbolic `Array`. `a[i]!` (getElem!) is handled in Task 2.

**Files:**
- Modify: `Blaster/Smt/Translate/Quantifier.lean` (`translateTypeAux` — add `Array` arm)
- Modify: `Blaster/Optimize/Opaque.lean` (opacify Array ops)
- Modify: `Blaster/Smt/Translate/Application.lean` (`translateSMTArrayOp?` — add Array arms; ensure dispatched)
- Test: `Tests/Smt/SmtArray/SmtRawArray.lean` (new)

- [ ] **Step 1: Route the `Array α` type to the datatype-pair path**

In `translateTypeAux` (`Quantifier.lean`), add an arm next to the `SMTArray`/`Vector` arms, BEFORE the generic `Expr.const ..` arm:

```lean
   | Expr.const ``Array _ => translateArrayType (λ a => translateTypeAux termTranslator a) t
```

`translateArrayType` reads the element type via `t.appArg!`, which is `α` for `Array α` (same as `SMTArray α`), so no change to `translateArrayType` is needed. `Array Int` and `SMTArray Int` get distinct cache entries (distinct Expr keys) → distinct datatypes; that is correct.

- [ ] **Step 2: Opacify the Array-named ops**

In `Blaster/Optimize/Opaque.lean`, in the list containing `Blaster.SMTArray.get/set/size`, add:

```lean
    ``Array.get!,
    ``Array.getD,
    ``Array.set!,
    ``Array.setIfInBounds,
    ``Array.size,
```

(Match the surrounding comma/indentation style. These are Array-specific → safe to opacify; prevents the translator unfolding them to `Array.get`/`Fin a.size`.)

- [ ] **Step 3: Add Array arms to `translateSMTArrayOp?`**

In `Blaster/Smt/Translate/Application.lean`, extend the existing `translateSMTArrayOp?` to also match the raw-Array ops, reusing its existing helpers (`inBounds`, `smtSelectorApp`, `smtArrCtorApp`, `selectSmt`, `storeSmt`, the cached `names`, `@dfltSMTArray_v`). The array type is obtained via `inferTypeEnv` of the array arg exactly as for SMTArray (cache-key invariant — same as Spec 1). Add to the outer `match n with` head guard and the inner dispatch:

```lean
  | ``Blaster.SMTArray.get | ``Blaster.SMTArray.set | ``Blaster.SMTArray.size
  | ``Array.get! | ``Array.getD | ``Array.set! | ``Array.setIfInBounds | ``Array.size => do
    let arrArgIdx :=
      if n == ``Blaster.SMTArray.get || n == ``Array.get! then 2 else 1
    let arrTy ← inferTypeEnv args[arrArgIdx]!
    let _ ← translateType termTranslator arrTy
    let some names := (← get).smtEnv.smtArrNamesCache.get? arrTy
      | throwEnvError "translateSMTArrayOp?: array names not cached for {reprStr arrTy}"
    let inBounds := fun (a i : SmtTerm) =>
      andSmt (leqSmt (natLitSmt 0) i) (ltSmt i (smtSelectorApp names.sizeSel a))
    match n with
    | ``Blaster.SMTArray.get =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: SMTArray.get expects 4 args, got {args.size}"
        let a ← termTranslator args[2]!; let i ← termTranslator args[3]!
        return some (iteSmt (inBounds a i) (selectSmt (smtSelectorApp names.dataSel a) #[i]) (smtSimpleVarId names.dfltSym))
    | ``Array.get! =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: Array.get! expects 4 args, got {args.size}"
        let a ← termTranslator args[2]!; let i ← termTranslator args[3]!
        return some (iteSmt (inBounds a i) (selectSmt (smtSelectorApp names.dataSel a) #[i]) (smtSimpleVarId names.dfltSym))
    | ``Array.getD =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: Array.getD expects 4 args, got {args.size}"
        let a ← termTranslator args[1]!; let i ← termTranslator args[2]!; let d ← termTranslator args[3]!
        return some (iteSmt (inBounds a i) (selectSmt (smtSelectorApp names.dataSel a) #[i]) d)
    | ``Blaster.SMTArray.set | ``Array.set! | ``Array.setIfInBounds =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: {n} expects 4 args, got {args.size}"
        let a ← termTranslator args[1]!; let i ← termTranslator args[2]!; let v ← termTranslator args[3]!
        let newData := iteSmt (inBounds a i) (storeSmt (smtSelectorApp names.dataSel a) i v) (smtSelectorApp names.dataSel a)
        return some (smtArrCtorApp names.ctorSym newData (smtSelectorApp names.sizeSel a))
    | ``Blaster.SMTArray.size | ``Array.size =>
        if args.size != 2 then throwEnvError "translateSMTArrayOp?: {n} size expects 2 args, got {args.size}"
        let a ← termTranslator args[1]!
        return some (smtSelectorApp names.sizeSel a)
    | _ => return none
  | _ => return none
```

NOTE: This is the EXACT shape of the existing `translateSMTArrayOp?` after Spec 1, with the
`Array.*` constants added. Read the current helper first and merge these arms into it rather
than duplicating; keep its existing `get`/`set`/`size` behavior byte-identical. Confirm the
helper is still dispatched in `translateApp` (it was, before `translateSMTArrayCtor?`). The
`getD` arm uses the EXPLICIT default `d`, not `@dfltSMTArray_v`.

- [ ] **Step 4: Write the named-op tests**

Create `Tests/Smt/SmtArray/SmtRawArray.lean`:

```lean
import Blaster

-- SOUND: out-of-bounds set! is a no-op → unguarded set!/get! is NOT valid
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : Array Int) (i : Nat) (v : Int), (a.set! i v).get! i = v]
-- SOUND positive: in-bounds guard makes it valid
#blaster [∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.set! i v).get! i = v]
-- setIfInBounds, same shape
#blaster [∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.setIfInBounds i v).get! i = v]
-- getD returns the explicit default out of bounds
#blaster [∀ (a : Array Int) (i : Nat) (d : Int), a.size ≤ i → a.getD i d = d]
```

- [ ] **Step 5: Build and run**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtArray/SmtRawArray.lean`
Expected: the unguarded line → `✅ Expected Falsified` (countermodel); the three guarded/getD lines → `✅ Valid`. No `translateFinType`/`Fin a.size`/`unknown constant`/Z3 datatype errors.
If you see the `translateFinType … List.rec` error, the op was unfolded before interception — re-check Step 2 (opacity) and that `translateSMTArrayOp?` is dispatched ahead of the unfolding paths.

- [ ] **Step 6: Commit**

```bash
git add Blaster/Smt/Translate/Quantifier.lean Blaster/Optimize/Opaque.lean \
        Blaster/Smt/Translate/Application.lean Tests/Smt/SmtArray/SmtRawArray.lean
git commit -m "feat(array): route raw Array to datatype-pair model; intercept named ops"
```
End commit body with: `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`

---

## Task 2: Normalize `getElem!`-on-`Array` → `Array.get!` (enables `a[i]!`)

**Files:**
- Modify: `Blaster/Optimize/Rewriting/OptimizeApp.lean` (dispatch a new normalization in `optimizeAppAux`)
- Test: `Tests/Smt/SmtArray/SmtRawArray.lean`

- [ ] **Step 1: Write the failing `a[i]!` test**

Append to `Tests/Smt/SmtArray/SmtRawArray.lean`:

```lean
-- `a[i]!` (getElem!) must funnel to the same sound model
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : Array Int) (i : Nat) (v : Int), (a.set! i v)[i]! = v]
#blaster [∀ (a : Array Int) (i : Nat) (v : Int), i < a.size → (a.set! i v)[i]! = v]
```

- [ ] **Step 2: Run to confirm it fails**

Run: `lake env lean Tests/Smt/SmtArray/SmtRawArray.lean`
Expected: the new `[i]!` lines FAIL (the guarded one errors with the `translateFinType … List.rec` dump, or is Undetermined), because `getElem!` is still unfolded. The Task-1 lines still pass.

- [ ] **Step 3: Add the normalization rule**

In `Blaster/Optimize/Rewriting/OptimizeApp.lean`, add a helper and dispatch it in `optimizeAppAux` (near the `optimizeNat?`/`optimizeBitVec?` dispatch, BEFORE generic unfolding). The rule fires only when the `getElem!` container type is `Array _`:

```lean
/-- Normalize `getElem! a i` to `Array.get! a i` when the container is an `Array`,
    so `a[i]!` funnels through the opacified+intercepted Array op path instead of
    unfolding to `Array.get`/`Fin a.size`. Fires only under `normalizeFunCall`
    (`isOptimizeRecCall`) and only for `Array` containers; `List`/other `getElem!`
    is left untouched. -/
def optimizeArrayGetElem? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const ``getElem! _ := f | return none
  -- args: [collType, idxType, elemType, valid, getElemInst, inhabitedInst, collection, index]
  if args.size < 8 then return none
  let collType := args[0]!
  let Expr.const ``Array _ := collType.getAppFn | return none
  if !(← isOptimizeRecCall) then return none
  setRestart
  -- rebuild as `Array.get! collection index`; mkAppM infers {α}/[Inhabited α]
  return some (← Lean.Meta.mkAppM ``Array.get! #[args[6]!, args[7]!])
```

Dispatch it in `optimizeAppAux` (add near line 69-71, before any path that would unfold `getElem!`):

```lean
  if let some e ← optimizeArrayGetElem? f args then return e
```

NOTES: (a) Confirm `isOptimizeRecCall`/`setRestart` are in scope here (they are used by the neighbouring Nat/BitVec rules — same module imports). (b) If `Lean.Meta.mkAppM` is not the established idiom in this file for rebuilding apps, mirror however `OptimizeNat`/`OptimizeBitVec` construct the normalized call (e.g. a `mk…Op` helper); the requirement is a well-typed `@Array.get! α inst collection index`. (c) Do NOT match `getElem`/`getElem?` here — out of scope for 2a (see spec); only `getElem!`.

- [ ] **Step 4: Build and run**

Run: `lake build Blaster && lake env lean Tests/Smt/SmtArray/SmtRawArray.lean`
Expected: ALL lines green — the `[i]!` unguarded line `✅ Expected Falsified`, the guarded `[i]!` line `✅ Valid`, and all Task-1 lines still pass.

- [ ] **Step 5: Commit**

```bash
git add Blaster/Optimize/Rewriting/OptimizeApp.lean Tests/Smt/SmtArray/SmtRawArray.lean
git commit -m "feat(array): normalize getElem!-on-Array to Array.get! so a[i]! is sound"
```
End commit body with the Co-Authored-By line.

---

## Task 3: Full regression + 2b decision

**Files:** none (verification + a note)

- [ ] **Step 1: Run the full suite**

Run: `lake test` (allow up to 20 min). If too slow/flaky, fall back to: every file under `Tests/Smt/SmtArray/`, `Tests/Smt/SmtVector/`, and `Tests/FixedIssues/Issue3.lean`, `Issue11.lean`, `Issue16.lean`, plus `lake build`.

- [ ] **Step 2: Confirm green except the pre-existing failure**

Expected: everything green EXCEPT `Tests/Smt/SmtFin/SmtFinOps.lean:13` (pre-existing, the `M` in the opening git status; counterexample `x=y=1`). Confirm via `git diff --stat HEAD -- Tests/Smt/SmtFin/SmtFinOps.lean` that this file's change predates this work.

- [ ] **Step 3: Decide on Spec 2b (concrete store-chains)**

- If the suite is fully green (no concrete `Array` reached SMT): **2b is YAGNI.** Record this in the report and STOP — the design's "optimizer reduces concretes" assumption is now proven against the real suite. Do NOT build store-chains speculatively.
- If a test regressed with an "unknown constant" / unmapped `Array.mk` / Z3 datatype error (e.g. `Issue3`): that names the concrete reaching SMT. Report it verbatim and STOP for re-scoping — Spec 2b will be planned separately to encode `Array.mk`/`List.toArray`/`Array.empty`/`Array.push` as store-chains (per the design doc). Do NOT attempt 2b ad hoc.

- [ ] **Step 4: Commit the verification note (if any test files or docs changed); otherwise nothing to commit.**

---

## Self-review notes (addressed)

- **Spec coverage:** type routing → T1.S1; opacify → T1.S2; intercept (reuse Spec-1 terms, `getD` explicit default) → T1.S3; `getElem!` normalization (approach A, Array-gated, `getElem!` only) → T2; full-suite gate + 2b decision → T3. 2b itself is intentionally NOT planned here (conditional, separate plan per design).
- **Placeholder scan:** the two flagged "confirm against live code" spots (arg layouts already given exactly; `mkAppM` vs `mk…Op` idiom) have concrete fallbacks, not placeholders.
- **Type consistency:** reuses Spec-1 names verbatim (`smtArrNamesCache`, `names.{sizeSel,dataSel,ctorSym,dfltSym}`, `inBounds`, `inferTypeEnv`, `iteSmt`/`leqSmt`/`ltSmt`/`andSmt`/`selectSmt`/`storeSmt`/`smtSelectorApp`/`smtArrCtorApp`); arg indices match the verified signatures.
