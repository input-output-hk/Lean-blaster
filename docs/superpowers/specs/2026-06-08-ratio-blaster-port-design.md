# Design: Porting the Lustre `Ratio` Formalization to Lean 4 + Blaster

**Date:** 2026-06-08
**Status:** Proposed (vertical slice)

## Background

The stablecoin project formalizes a `CustomRatio` Plutus implementation in Lustre
(`stablecoin-plutus/fm/ratio/Ratio.lus`), verified with Kind2/Z3. The library defines a
`Ratio` value (numerator, denominator, NaN flag) plus ~40 operations, and ~75 theorem
files each stating algebraic/relational properties via Kind2 `check`.

All theorems are **combinational** (no `pre`, no temporal state). We want to re-express
this in Lean 4 and discharge the properties with **Blaster** (the Lean → SMT-Lib/Z3
translator in this repo).

## Decisions (locked)

1. **Verification path: `#blaster` pure propositions.** Each Lustre combinational `check`
   maps 1:1 to a `#blaster [∀ …, prop]`, which negates the goal and asks Z3 for unsat
   (property valid). This is the direct analogue of a Kind2 `check`. The `StateMachine`
   class (`#bmc`/`#kind`) is *not* used — it targets transition systems, which these
   stateless algebraic properties are not.

2. **Encoding: all-Bool, mirroring Lustre.** Lustre is fully boolean-valued, so:
   - `Ratio` is a `structure { numerator denominator : Int, isNaN : Bool }`.
   - Every operation returns its Lustre type: `Ratio`-valued functions return `Ratio`;
     `bool`-valued predicates (`isValidRatio`, `eqRatio`, `ltRatio`, …) return `Bool`.
   - Lustre connectives map to Bool ops: `and`→`&&`, `or`→`||`, `not`→`!`.
   - Lustre `=` **between two `Ratio` values** is value equality → Lean `==` via a `BEq`
     instance (NOT propositional `Eq`). This is distinct from `eqRatio`, which is
     cross-multiplication ratio equality.
   - Lustre `=` **between two `int`s** → `==` (`BEq Int`, Bool).
   - Lustre `=` **between two `bool` predicate results** (boolean iff, e.g. `ADD_REQ_IFF`)
     → `==` (`BEq Bool`, Bool).
   - Integer comparisons `<`/`≤`/`>`/`≥` are Prop in Lean; wrapped as `decide (a < b)` to
     stay Bool. Blaster normalizes these via `Blaster.decide'`
     (`Optimize/Rewriting/OptimizeDecide*`).

3. **Top-level theorem shape: Prop `→` with Bool `= true` atoms.** A Lustre check
   `p => q => r` becomes `p = true → q = true → r = true` (or, where the conclusion is a
   single Bool expression, `… → concl = true`). Top-level `→` is the proven idiom across
   the existing `#blaster` tests and is logically identical to a Bool `bimp` chain (the
   solver asserts `p ∧ q ∧ ¬r` either way). We do **not** introduce a `bimp` operator.

4. **Location: in the Lean-blaster repo,** mirroring the existing `EVM/` + `Tests/EVM/`
   precedent. The `Ratio` library compiles directly against Blaster with no extra setup.

## Scope: vertical slice

This pass validates the entire workflow end-to-end against the SMT backend on the
**Addition** operation group, before scaling to all ~75 theorems.

**In scope:**
- `Ratio/Ratio.lean` — the `Ratio` struct, its `BEq` instance, the 4 constants
  (`R_ZERO`, `R_ONE`, `R_HALF`, `R_NaN`), and all operations **reachable from the
  Addition group**: `normalizeRatio`, `fromInteger`, `ratio`, `absInt`, `eqRatio`,
  `ltRatio`, `leqRatio`, `gtRatio`, `geqRatio`, `addRatio`, `subRatio`, `mulRatio`,
  `negate`, `isValidRatio`, `isValidAndNormalizedRatio`. The remaining ops
  (`recip`, `truncate`, `ceil`, `quotient`, `min/maxRatio`, integer/ratio comparisons,
  etc.) are ported in later passes.
- `Tests/Ratio/Addition.lean` — the 9 Addition theorem files as `#blaster` commands:
  `AdditionBasics`, `AdditionCommutativity`, `AdditionAssociativityOne`,
  `AdditionAssociativityTwo`, `AdditionIdentity`, `AdditionNegation`,
  `AdditionDistributivity`, `AdditionRelational`, `AdditionValidity`.

**Out of scope (later passes):** the other ~66 theorems; `div`-based operations
(`quotient`/`truncate`/`ceil`/`truncateRecipRatio`) which carry their own Int-division
rounding-semantics question (Lean `Int.div` truncates toward zero; Z3 default is
Euclidean — must be reconciled before porting those groups).

## Risks (in priority order)

1. **`BEq` on a *derived* struct may not translate.** `==` on `Ratio` appears in nearly
   every theorem. Blaster's `BEq.beq` match (`Optimize/Expr.lean:156`) special-cases
   Int/Bool instances; a `deriving BEq` instance on `Ratio` may instead be treated as an
   **opaque** uninterpreted function, silently breaking every value-equality theorem.
   *Mitigation:* this is **Build Step 1** (see below). If the derived instance is opaque,
   supply an explicit instance with a Bool body so the translator sees `&&` of field
   comparisons:
   ```lean
   instance : BEq Ratio where
     beq a b := a.numerator == b.numerator && a.denominator == b.denominator
                && a.isNaN == b.isNaN
   ```
   Find this out at line 20, not line 200.

2. **Nonlinear integer arithmetic.** The cross-multiplication equalities
   (`a.num * b.den = b.num * a.den`) are nonlinear → undecidable in general; Z3 can stall.
   `AdditionDistributivity.lus` is annotated `-- 25 sec` in the source — even Kind2 found
   it expensive. Expect to need `(timeout: N)` on that check. Slow/undetermined on
   Distributivity is *not* presumed a translation bug.

## Build order (for the implementation plan)

1. **Smallest end-to-end probe first.** `Ratio` struct + `BEq` instance + `addRatio` +
   `R_ZERO`, and a single `#blaster` commutativity check. Run it. Confirm `==` discharges
   (Risk 1). Only then proceed.
2. Port the remaining Addition-reachable operations and constants into `Ratio/Ratio.lean`;
   confirm the library type-checks.
3. Port the 9 Addition theorem files into `Tests/Ratio/Addition.lean`, one check at a
   time, running `#blaster` on each. Apply `(timeout: N)` where needed (Distributivity).
4. Wire the new files into the lake build / test aggregation following the `EVM` pattern.

## Translation reference (worked examples)

Lustre:
```
check "ADD_COMMUTATIVITY"
  isValidRatio(a) => isValidRatio(b) => not(b.isNaN) => addRatio(a, b) = addRatio(b, a);
```
Lean:
```lean
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → b.isNaN = false →
  (addRatio a b == addRatio b a) = true ]
```

Lustre boolean iff (`ADD_REQ_IFF`):
```
isValidRatio(a) => isValidRatio(b) =>
  eqRatio(addRatio(a, b), addRatio(a, c)) = eqRatio(b, c);
```
Lean — `=` between two Bool predicate results becomes `==`:
```lean
… → (eqRatio (addRatio a b) (addRatio a c) == eqRatio b c) = true
```

## Success criteria

- `Ratio/Ratio.lean` type-checks.
- All 9 Addition theorem files port to `#blaster` commands; each either proves valid or has
  its non-discharge explained (timeout on Distributivity is acceptable and noted).
- The workflow (define → state → `#blaster` → SMT) is validated, ready to scale to the
  remaining theorem groups in subsequent passes.
