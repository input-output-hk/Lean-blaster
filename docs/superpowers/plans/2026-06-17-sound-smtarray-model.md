# Sound `SMTArray` Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make blaster's `SMTArray` model faithful to its bounds-checked Lean semantics so it no longer proves Lean-false `set`/`get` theorems.

**Architecture:** Represent `SMTArray α` as a per-element-sort SMT datatype pair `(data : (Array Int σ), size : Int)`. `get`/`set` become bounds-aware (`ite` on `0 ≤ i < size`), out-of-bounds reads return an unconstrained-but-qualifier-satisfying default constant. `Vector` is untouched (already sound).

**Tech Stack:** Lean 4, SMT-LIB 2 (Z3, logic `ALL`), the Blaster translator (`Blaster/Smt/Translate/*`).

**Spec:** `docs/superpowers/specs/2026-06-17-sound-smtarray-model-design.md`

---

## Background for the implementer

- `SMTArray` is defined in `Blaster/SmtArray.lean` as a single-field structure wrapping `Array`.
  `get a i = a.toArray.getD i default` (out of bounds → `default`); `set a i v = ⟨a.toArray.setIfInBounds i v⟩` (out of bounds → no-op).
- Currently `SMTArray α` translates to the SMT sort `(Array Int σ)` (`translateArrayType`, `Blaster/Smt/Translate/Quantifier.lean:1317`), and `get`/`set` map to unconditional `select`/`store` (`Blaster/Smt/Translate/Application.lean:414-415`, listed in the `opaqueFuns` set at `:66-67`). This ignores size → unsound.
- The translator dispatch chain is in `translateApp` (`Application.lean:1207-1237`). `Option SmtTerm` helpers like `translateVectorOp?` (`:1665`) run there *before* the opaque-fun path and can build compound terms. `translateOpaqueFun` (`:352`) only returns a function *identifier* and therefore cannot build an `ite` — that is why `get`/`set` must move to a new `translateSMTArrayOp?` helper.
- Datatype machinery already exists: `SmtDatatypeDecl { params : Option (Array SmtSymbol), ctors : Array SmtConstructorDecl }`, `SmtConstructorDecl = SmtSymbol × Option (Array SmtSelector)`, `SmtSelector = SmtSymbol × SortExpr` (`Blaster/Smt/Syntax.lean:109-115`). `declareDataType (nm : SmtSymbol) (decl : SmtDatatypeDecl)` (`Env.lean:235`), `declareConst (id) (sort)` (`Env.lean:231`), `defineFun (nm) (args : SortedVars) (rt) (body)` (`Env.lean:254`), `trySubmitCommand!`/`.assert` for assertions.
- Term builders (`Blaster/Smt/Term.lean`): `selectSmt f #[i]` (`:400`), `storeSmt a i v` (`:404`), `mkSimpleSmtAppN sym #[..]`, `arraySort #[intSort, elemSort]` (`:63`), `intSort`, `boolSort`, `mkReservedSymbol`, `smtSimpleVarId`, `natLitSmt`. Boolean/arith builders exist: confirm exact names of `ite`, `and`, `<=`, `<`, `>=` term builders before use (grep `iteSmt`/`andSmt`/`leqSmt`/`ltSmt`/`geqSmt` in `Term.lean`; use whatever the codebase already defines, e.g. the symbols `iteSymbol`, `andSymbol`, `leqSymbol`, `ltSymbol` are present — wrap with `mkSimpleSmtAppN`).
- `updateIndInstCache (d) (n) (instSort) (isReservedSymbol)` (`Quantifier.lean:176`) stores `{instName := @is<n>, instSort, ...}` and returns the decl. `decl.instSort` is the sort returned for the type.

### Naming scheme (single source of truth)

Derive all SMT names from one fresh-id `v` so the type translator (declares) and the op translator (applies) agree. Add to `Blaster/Smt/Term.lean`:

```lean
/-- SMT names for the `SMTArray` datatype-pair encoding at fresh-id `v`.
    Single source of truth shared by `translateArrayType` (declaration) and
    `translateSMTArrayOp?` (application). -/
structure SmtArrNames where
  sortSym  : SmtSymbol   -- datatype sort, e.g. @SMTArray_3
  ctorSym  : SmtSymbol   -- constructor,   e.g. @mkSMTArray_3
  dataSel  : SmtSymbol   -- data selector, e.g. @dataSMTArray_3
  sizeSel  : SmtSymbol   -- size selector, e.g. @sizeSMTArray_3
  dfltSym  : SmtSymbol   -- per-instance oob default const, e.g. @dfltSMTArray_3

def smtArrNames (v : Nat) : SmtArrNames :=
  { sortSym := mkReservedSymbol s!"SMTArray_{v}"
    ctorSym := mkReservedSymbol s!"@mkSMTArray_{v}"
    dataSel := mkReservedSymbol s!"@dataSMTArray_{v}"
    sizeSel := mkReservedSymbol s!"@sizeSMTArray_{v}"
    dfltSym := mkReservedSymbol s!"@dfltSMTArray_{v}" }
```

Note: `updateIndInstCache` will be called with `n := names.sortSym`, producing qualifier `@isSMTArray_{v}` and we pass `instSort := .SymbolSort names.sortSym`. The op translator recovers `v` by re-translating the `SMTArray α` type (cache hit) and reading the sort symbol — see Task 2 Step 5 for how the element type is recovered and re-keyed. To avoid string surgery, the op translator does NOT parse `v` out of the symbol; instead it re-runs `translateArrayType` on the array argument's `SMTArray α` type (idempotent cache hit) and obtains the `SmtArrNames` from a small **second cache** keyed by the same `Expr` (Task 2 Step 1 adds it).

---

## Task 1: Add `SMTArray.size` and keep it opaque

**Files:**
- Modify: `Blaster/SmtArray.lean`
- Modify: `Blaster/Optimize/Opaque.lean` (the `opaqueFuns` list that already contains `Blaster.SMTArray.get`/`.set`, near `:140-142`)
- Test: `Tests/Smt/SmtArray/SmtArrayOps.lean`

- [ ] **Step 1: Add `SMTArray.size`**

In `Blaster/SmtArray.lean`, after `SMTArray.set`:

```lean
/-- Number of elements; translated to the SMT `size` selector of the datatype-pair encoding. -/
def SMTArray.size (a : SMTArray α) : Nat := a.toArray.size
```

- [ ] **Step 2: Register it opaque in the optimizer**

In `Blaster/Optimize/Opaque.lean`, add to the list containing `Blaster.SMTArray.get`/`.set`:

```lean
    ``Blaster.SMTArray.size,
```

- [ ] **Step 3: Build to confirm no regression**

Run: `lake build Blaster`
Expected: builds clean (no behavior change yet — `.size` has no translation until Task 2, but it is now recognized as opaque so the optimizer will not unfold it).

- [ ] **Step 4: Commit**

```bash
git add Blaster/SmtArray.lean Blaster/Optimize/Opaque.lean
git commit -m "feat(smtarray): add SMTArray.size, register opaque"
```

---

## Task 2: Datatype-pair representation + bounds-aware get/set/size

This is the core change. The first green checkpoint is at Step 9. Build is expected to be red between Step 4 and Step 8 (sort changes before ops are updated) — that is acceptable mid-task; do not commit until Step 9 passes.

**Files:**
- Modify: `Blaster/Smt/Term.lean` (naming helper from the Background section + selector/ctor term builders)
- Modify: `Blaster/Smt/Translate/Quantifier.lean` (`translateArrayType` `:1317-1347`; add a second cache for `SmtArrNames`)
- Modify: `Blaster/Optimize/Env.lean` (add the `SmtArrNames` cache field next to `indTypeInstCache` `:383`)
- Modify: `Blaster/Smt/Translate/Application.lean` (add `translateSMTArrayOp?`; dispatch it `:1220` area; remove `.get`/`.set` from `opaqueFuns` `:66-67` and from `translateOpaqueFun` `:414-415`)
- Test: `Tests/Smt/SmtArray/SmtArrayOps.lean`

- [ ] **Step 1: Add the `SmtArrNames` helper + a names cache**

Add `SmtArrNames` + `smtArrNames` to `Blaster/Smt/Term.lean` (code in the Background section).

In `Blaster/Optimize/Env.lean`, add a field to the SMT env structure that holds `indTypeInstCache` (`:383`):

```lean
  -- maps the `SMTArray α` Expr to its datatype-pair SMT names
  smtArrNamesCache : Std.HashMap Lean.Expr SmtArrNames
```

and initialise it `Std.HashMap.emptyWithCapacity` in the same initialiser block that sets `indTypeInstCache := Std.HashMap.emptyWithCapacity` (`:454`). (Import/qualify `SmtArrNames` as needed.)

- [ ] **Step 2: Add selector/constructor term builders to `Blaster/Smt/Term.lean`**

```lean
/-- `(sel a)` — apply a unary datatype selector. -/
def smtSelectorApp (sel : SmtSymbol) (a : SmtTerm) : SmtTerm := mkSimpleSmtAppN sel #[a]

/-- `(ctor data size)` — apply the 2-field SMTArray constructor. -/
def smtArrCtorApp (ctor : SmtSymbol) (data size : SmtTerm) : SmtTerm :=
  mkSimpleSmtAppN ctor #[data, size]
```

(Confirm `iteSymbol`, `andSymbol`, `leqSymbol`, `ltSymbol`, `geqSymbol` exist in `Term.lean`; if a `geq`/`<=` symbol is missing, reuse `leqSymbol` with swapped args. Define thin wrappers only if absent.)

- [ ] **Step 3: Rewrite `translateArrayType` to declare the datatype + default const + qualifier**

Replace the body of `translateArrayType` (`Blaster/Smt/Translate/Quantifier.lean:1317-1347`) with:

```lean
def translateArrayType
    (typeTranslator : Expr → TranslateEnvT SortExpr)
    (t : Expr) : TranslateEnvT SortExpr := do
  match (← get).smtEnv.indTypeInstCache.get? t with
  | some decl => return decl.instSort
  | none =>
    let elemType := t.appArg!
    let elemSort ← typeTranslator elemType
    let dataSort := arraySort #[intSort, elemSort]
    let v ← mkFreshId
    let names := smtArrNames v
    -- datatype: (declare-datatype SMTArray_v ((@mkSMTArray_v (@dataSMTArray_v (Array Int σ)) (@sizeSMTArray_v Int))))
    let ctorDecl : SmtConstructorDecl :=
      (names.ctorSym, some #[(names.dataSel, dataSort), (names.sizeSel, intSort)])
    declareDataType names.sortSym { params := none, ctors := #[ctorDecl] }
    let arrSort := SortExpr.SymbolSort names.sortSym
    -- per-instance out-of-bounds default constant, constrained to satisfy the element qualifier
    declareConst names.dfltSym elemSort
    let dfltPred ← createPredQualifierAppAux (smtSimpleVarId names.dfltSym) elemType (inPredQualifier := true)
    trySubmitCommand! (.assert dfltPred)
    -- cache the decl (qualifier name @isSMTArray_v) and the names
    let decl ← updateIndInstCache t names.sortSym arrSort (isReservedSymbol := true)
    modify (fun env => { env with smtEnv.smtArrNamesCache := env.smtEnv.smtArrNamesCache.insert t names })
    -- qualifier: size >= 0 AND elements satisfy the element qualifier through the data selector
    let xsym := mkReservedSymbol "@x"
    let isym := mkReservedSymbol "@i"
    let sizeNonNeg := mkSimpleSmtAppN leqSymbol #[natLitSmt 0, smtSelectorApp names.sizeSel (smtSimpleVarId xsym)]
    let elemSel := selectSmt (smtSelectorApp names.dataSel (smtSimpleVarId xsym)) #[smtSimpleVarId isym]
    let elemPred ← createPredQualifierAppAux elemSel elemType (inPredQualifier := true)
    let elemForall := mkForallTerm none #[(isym, intSort)] elemPred none
    let body := mkSimpleSmtAppN andSymbol #[sizeNonNeg, elemForall]
    defineFun decl.instName #[(xsym, arrSort)] boolSort body
    return arrSort
```

Notes: `updateIndInstCache t names.sortSym arrSort` stores `instName = @isSMTArray_v`, `instSort = arrSort`. Confirm `.assert` is the `SmtCommand` constructor name (`Syntax.lean`); if assertions go through a helper (e.g. `assertSmt`/`addAssertion`), use that instead.

- [ ] **Step 4: Remove `get`/`set` from the opaque path**

In `Blaster/Smt/Translate/Application.lean`: delete `` ``Blaster.SMTArray.get, `` and `` ``Blaster.SMTArray.set `` from the `opaqueFuns` list (`:66-67`), and delete the two arms at `:414-415`. (Leave `SMTArray.size` out of `opaqueFuns` too — it is handled in Step 5.)

- [ ] **Step 5: Add `translateSMTArrayOp?`**

Add as a `where`-helper of `translateApp` (alongside `translateVectorOp?`), returning `Option SmtTerm`. Arg layouts (all args incl. implicits, via `withApp`):
`@SMTArray.get α inst a i` → `#[α, inst, a, i]`; `@SMTArray.set α a i v` → `#[α, a, i, v]`; `@SMTArray.size α a` → `#[α, a]`.

```lean
translateSMTArrayOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
  match n with
  | ``Blaster.SMTArray.get | ``Blaster.SMTArray.set | ``Blaster.SMTArray.size => do
    -- recover the SMTArray α type from the element type α (args[0]) and resolve names via the type translator
    let elemTy := args[0]!
    let arrTy := mkApp (mkConst ``Blaster.SMTArray [← Lean.Meta.getLevel elemTy]) elemTy
    let _ ← translateType termTranslator arrTy   -- ensures datatype declared + names cached (idempotent)
    let some names := (← get).smtEnv.smtArrNamesCache.get? arrTy
      | throwEnvError "translateSMTArrayOp?: SMTArray names not cached for {reprStr arrTy}"
    match n with
    | ``Blaster.SMTArray.get =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: SMTArray.get expects 4 args, got {args.size}"
        let a ← termTranslator args[2]!
        let i ← termTranslator args[3]!
        let inB := mkSimpleSmtAppN andSymbol
          #[mkSimpleSmtAppN leqSymbol #[natLitSmt 0, i],
            mkSimpleSmtAppN ltSymbol #[i, smtSelectorApp names.sizeSel a]]
        let hit := selectSmt (smtSelectorApp names.dataSel a) #[i]
        return some (mkSimpleSmtAppN iteSymbol #[inB, hit, smtSimpleVarId names.dfltSym])
    | ``Blaster.SMTArray.set =>
        if args.size != 4 then throwEnvError "translateSMTArrayOp?: SMTArray.set expects 4 args, got {args.size}"
        let a ← termTranslator args[1]!
        let i ← termTranslator args[2]!
        let v ← termTranslator args[3]!
        let inB := mkSimpleSmtAppN andSymbol
          #[mkSimpleSmtAppN leqSymbol #[natLitSmt 0, i],
            mkSimpleSmtAppN ltSymbol #[i, smtSelectorApp names.sizeSel a]]
        let newData := mkSimpleSmtAppN iteSymbol
          #[inB, storeSmt (smtSelectorApp names.dataSel a) i v, smtSelectorApp names.dataSel a]
        return some (smtArrCtorApp names.ctorSym newData (smtSelectorApp names.sizeSel a))
    | ``Blaster.SMTArray.size =>
        if args.size != 2 then throwEnvError "translateSMTArrayOp?: SMTArray.size expects 2 args, got {args.size}"
        let a ← termTranslator args[1]!
        return some (smtSelectorApp names.sizeSel a)
    | _ => return none
  | _ => return none
```

Confirm `Lean.Meta.getLevel` is the right way to get α's universe level here (alternative: reuse the level from `f`'s `Expr.const _ levels` in `translateApp`, threading it in). If level recovery is awkward, build `arrTy` by `inferType args[2]!`/`inferType args[1]!` (the array argument) instead — that yields `SMTArray α` directly and sidesteps level handling. Prefer the `inferType` route if simpler in this codebase.

- [ ] **Step 6: Dispatch the new helper**

In `translateApp` (`Application.lean:1207-1237`), add before `translateSMTArrayCtor?` (`:1220`):

```lean
         if let some r ← translateSMTArrayOp? n args then return r
```

- [ ] **Step 7: Write the failing soundness + positive tests**

In `Tests/Smt/SmtArray/SmtArrayOps.lean`, add:

```lean
-- SOUND: out-of-bounds set is a no-op, so unguarded set/get is NOT valid (countermodel exists)
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i : Nat) (v : Int), (a.set i v).get i = v]
-- SOUND positive: with an in-bounds guard it IS valid
#blaster [∀ (a : SMTArray Int) (i : Nat) (v : Int), i < a.size → (a.set i v).get i = v]
```

- [ ] **Step 8: Build**

Run: `lake build Blaster`
Expected: builds clean.

- [ ] **Step 9: Run the new tests (first green checkpoint)**

Run: `lake env lean Tests/Smt/SmtArray/SmtArrayOps.lean`
Expected: the unguarded statement reports a countermodel (`solve-result: 1`), the guarded statement reports `✅ Valid`. No `translateFinType`/`unknown constant`/Z3 datatype errors.

- [ ] **Step 10: Commit**

```bash
git add Blaster/Smt/Term.lean Blaster/Optimize/Env.lean \
        Blaster/Smt/Translate/Quantifier.lean Blaster/Smt/Translate/Application.lean \
        Tests/Smt/SmtArray/SmtArrayOps.lean
git commit -m "fix(smtarray): faithful size-aware datatype model for get/set/size"
```

---

## Task 3: Fix the false-but-Valid tests and verify the whole suite

**Files:**
- Modify: `Tests/Smt/SmtArray/SmtArrayOps.lean` (`:9`, `:13`, `:15`)
- Modify: `Tests/Smt/SmtArray/SmtArrayQualifier.lean` (`:28`)

- [ ] **Step 1: Convert each false-but-Valid statement to positive (guarded) + negative (cex) forms**

`SmtArrayOps.lean:9` `(a.set i v).get i = v` — replace with the two forms already added in Task 2 Step 7 (remove the now-duplicate line `:9`).

`SmtArrayOps.lean:13` `((a.set i v).set i w).get i = w` — replace with:

```lean
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Int) (i : Nat) (v w : Int), ((a.set i v).set i w).get i = w]
#blaster [∀ (a : SMTArray Int) (i : Nat) (v w : Int), i < a.size → ((a.set i v).set i w).get i = w]
```

`SmtArrayOps.lean:15` `(a.set i v).get i = v` for `SMTArray (BitVec 8)` — replace with:

```lean
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), (a.set i v).get i = v]
#blaster [∀ (a : SMTArray (BitVec 8)) (i : Nat) (v : BitVec 8), i < a.size → (a.set i v).get i = v]
```

`SmtArrayQualifier.lean:28` `(a.set i v).get i = v` for `SMTArray Nat` — replace with:

```lean
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray Nat) (i : Nat) (v : Nat), (a.set i v).get i = v]
#blaster [∀ (a : SMTArray Nat) (i : Nat) (v : Nat), i < a.size → (a.set i v).get i = v]
```

Leave `SmtArrayOps:11` (`i ≠ j → (a.set i v).get j = a.get j`), `:17`, and the `:28`-Ops cex untouched — verify in Step 3 that `:11` still proves under the new model (it should: see spec analysis).

- [ ] **Step 2: Run the two SMTArray test files**

Run: `lake env lean Tests/Smt/SmtArray/SmtArrayOps.lean && lake env lean Tests/Smt/SmtArray/SmtArrayQualifier.lean`
Expected: every guarded statement `✅ Valid`; every unguarded statement reports a countermodel; `:11` still `✅ Valid`.

- [ ] **Step 3: Full regression — the entire test suite, especially Vector**

Run: `lake test`
Expected: all pass, including `Tests/Smt/SmtVector/*` (no `translateVectorType` change ⇒ Vector unaffected). If `lake test` is too broad/slow, at minimum run every file under `Tests/Smt/SmtArray/` and `Tests/Smt/SmtVector/`.

- [ ] **Step 4: Commit**

```bash
git add Tests/Smt/SmtArray/SmtArrayOps.lean Tests/Smt/SmtArray/SmtArrayQualifier.lean
git commit -m "test(smtarray): replace false set/get theorems with guarded+cex forms"
```

---

## Self-review notes (addressed)

- **Spec coverage:** Decision 1 (datatype pair) → Task 2 Steps 1-3,5. Decision 2 (`DFLT`) → Task 2 Step 3 (`declareConst` + qualifier assert) and Step 5 (oob branch). Decision 3 (`SMTArray.size` + test forms) → Task 1 + Task 3. "Do not touch `translateVectorType`" → enforced; verified in Task 3 Step 3.
- **`@dflt` soundness:** constrained by `(@isElem @dflt)` (Task 2 Step 3) so element qualifiers (e.g. `SMTArray Nat` ≥ 0) hold for oob reads.
- **Open confirmations the executor must resolve against the real code (flagged inline, not placeholders):** exact boolean/arith term-builder names in `Term.lean` (Step 2); the `.assert` command/helper name (Step 3); the level-recovery vs `inferType` choice for `arrTy` (Step 5). Each has a concrete fallback stated.
- **Type consistency:** `SmtArrNames` fields (`sortSym`/`ctorSym`/`dataSel`/`sizeSel`/`dfltSym`) used identically in Quantifier (declare) and Application (apply); `smtArrNamesCache` keyed by the `SMTArray α` `Expr` in both writer (Quantifier Step 3) and reader (Application Step 5).
