# Ratio → Blaster Port (Addition Slice) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the Lustre `Ratio` library and its Addition theorem group to Lean 4, discharging each property with Blaster's `#blaster` command against Z3.

**Architecture:** A single `Ratio/Ratio.lean` module holds the `Ratio` struct + a `BEq` instance + the Addition-reachable operations, mirroring `stablecoin-plutus/fm/ratio/Ratio.lus` line-for-line in an all-Bool encoding. `Tests/Ratio/Addition.lean` re-expresses each Lustre `check` as a `#blaster [∀ …, … = true]`. The very first task is an empirical probe of the highest-risk assumption (does `==` on a struct translate?) before any bulk porting.

**Tech Stack:** Lean 4 (toolchain pinned in `lean-toolchain`), Lake, the in-repo `Blaster` library, Z3 (`/opt/homebrew/bin/z3`).

**Reference source:** `/Users/romainsoulat/Documents/GitHub/stablecoin/stablecoin-plutus/fm/ratio/Ratio.lus` and `…/theorems/Addition*.lus`.

**Spec:** `docs/superpowers/specs/2026-06-08-ratio-blaster-port-design.md`

---

## Conventions used throughout

- **Run a single file:** `lake env lean <path>` (after Blaster + Ratio are built). It elaborates the file; each `#blaster` prints `✅ Valid` on success, `⚠️ … Undetermined` on timeout/unknown, or a counterexample on falsification. Compile errors print as Lean errors.
- **Encoding rules** (from the spec): predicates return `Bool`; Lustre `and`/`or`/`not` → `&&`/`||`/`!`; Lustre `=` between two `Ratio` values → `==` (the `BEq` instance); Lustre `=` between `Int`s or between two `Bool` predicate results → `==`; integer `<`/`≤`/`>`/`≥` → `decide (…)`; a Lustre `check` of the form `p => q => r` → `p = true → q = true → r = true`.
- **Precedence caution:** `==`/`=` bind *tighter* than `&&`/`||`. Always parenthesize a Bool conjunction before `= true`, e.g. `((x == y) && z) = true`, never `x == y && z = true`.
- **Negative literals** need parens as function args: `ratio (-15) 100`.

---

## Task 0: Wire the `Ratio` library into Lake

**Files:**
- Create: `Ratio.lean` (lib root)
- Create: `Ratio/Ratio.lean` (placeholder, filled in Task 1)
- Modify: `lakefile.lean`

- [ ] **Step 1: Create the placeholder module** `Ratio/Ratio.lean`

```lean
import Lean
import Blaster

namespace Ratio

end Ratio
```

- [ ] **Step 2: Create the lib root** `Ratio.lean`

```lean
import Ratio.Ratio
```

- [ ] **Step 3: Register the lib in** `lakefile.lean`

Add this block immediately after the `lean_lib «Blaster»` block (before `@[test_driver] lean_lib «Tests»`):

```lean
lean_lib «Ratio» where
  precompileModules := true
```

- [ ] **Step 4: Build to verify wiring**

Run: `lake build Blaster Ratio`
Expected: build succeeds (no errors). Blaster may take a while on first build.

- [ ] **Step 5: Commit**

```bash
git add lakefile.lean Ratio.lean Ratio/Ratio.lean
git commit -m "build: scaffold Ratio library wired to Blaster"
```

---

## Task 1: BEq probe — validate the highest-risk assumption FIRST

**Why:** `==` on `Ratio` appears in nearly every theorem. A `deriving BEq` instance might be translated by Blaster as an *opaque* uninterpreted function, silently breaking every value-equality theorem. We find this out now with the smallest possible artifact, not after porting everything.

**Files:**
- Modify: `Ratio/Ratio.lean`
- Create: `Tests/Ratio/Probe.lean`

- [ ] **Step 1: Add the minimal definitions** to `Ratio/Ratio.lean` (replace the whole file)

```lean
import Lean
import Blaster

namespace Ratio

/-- Arbitrary-precision ratio. NaN models a zero denominator. -/
structure Ratio where
  numerator   : Int
  denominator : Int
  isNaN       : Bool
deriving BEq, Repr

def R_NaN : Ratio := { numerator := 0, denominator := 0, isNaN := true }

/-- Ensure the denominator is positive by pushing the sign onto the numerator. -/
def normalizeRatio (num denum : Int) : Ratio :=
  if denum < 0 then { numerator := -num, denominator := -denum, isNaN := false }
  else { numerator := num, denominator := denum, isNaN := false }

/-- Constructor: NaN when the denominator is zero, otherwise normalized. -/
def ratio (num denum : Int) : Ratio :=
  if denum == 0 then R_NaN else normalizeRatio num denum

/-- Addition of two ratios; NaN propagates. -/
def addRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator + b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

end Ratio
```

- [ ] **Step 2: Write the probe** `Tests/Ratio/Probe.lean`

```lean
import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Probe

-- Probe A: does `==` on the derived BEq instance translate? (addRatio is commutative
-- unconditionally — NaN guard is symmetric, Int + and * commute.)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  (addRatio (ratio a_n a_d) (ratio b_n b_d) == addRatio (ratio b_n b_d) (ratio a_n a_d)) = true ]

-- Probe B: does a term-level `let` inside the proposition translate?
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  (addRatio a b == addRatio b a) = true ]

end Tests.Ratio.Probe
```

- [ ] **Step 3: Build the Ratio lib, then run the probe**

Run: `lake build Ratio && lake env lean Tests/Ratio/Probe.lean`
Expected (success): two `✅ Valid` messages, one per `#blaster`.

- [ ] **Step 4: Branch on the result**

- **If both print `✅ Valid`:** the derived `BEq` and `let` both translate. Keep `deriving BEq` and the `let` form. Proceed.
- **If a `#blaster` is `⚠️ Undetermined` or errors about an opaque/uninterpreted `BEq.beq` / unknown function:** the derived instance is opaque. Replace `deriving BEq, Repr` with `deriving Repr` and add an explicit Bool-bodied instance right after the struct:

```lean
instance : BEq Ratio where
  beq a b := a.numerator == b.numerator && a.denominator == b.denominator
             && a.isNaN == b.isNaN
```

Re-run Step 3 until Probe A prints `✅ Valid`.
- **If only Probe B (the `let` one) fails:** inline `ratio …` calls instead of `let` in all later theorems. Note this decision in the commit message.

- [ ] **Step 5: Commit the validated foundation**

```bash
git add Ratio/Ratio.lean Tests/Ratio/Probe.lean
git commit -m "feat: Ratio struct + BEq probe validated against Blaster"
```

---

## Task 2: Complete the Addition-reachable operations

**Files:**
- Modify: `Ratio/Ratio.lean`

- [ ] **Step 1: Replace** `Ratio/Ratio.lean` **with the full Addition-reachable library**

(If Task 1 switched to an explicit `BEq` instance, keep that instance and `deriving Repr`; otherwise keep `deriving BEq, Repr`. Everything else below is unchanged regardless.)

```lean
import Lean
import Blaster

namespace Ratio

/-- Arbitrary-precision ratio. NaN models a zero denominator. -/
structure Ratio where
  numerator   : Int
  denominator : Int
  isNaN       : Bool
deriving BEq, Repr

-- Constants
def R_ZERO : Ratio := { numerator := 0, denominator := 1, isNaN := false }
def R_ONE  : Ratio := { numerator := 1, denominator := 1, isNaN := false }
def R_HALF : Ratio := { numerator := 1, denominator := 2, isNaN := false }
def R_NaN  : Ratio := { numerator := 0, denominator := 0, isNaN := true }

/-- Absolute value on Int. -/
def absInt (a : Int) : Int := if a < 0 then -a else a

/-- Ensure the denominator is positive by pushing the sign onto the numerator. -/
def normalizeRatio (num denum : Int) : Ratio :=
  if denum < 0 then { numerator := -num, denominator := -denum, isNaN := false }
  else { numerator := num, denominator := denum, isNaN := false }

/-- Build a ratio from a single integer (denominator 1). -/
def fromInteger (a : Int) : Ratio := { numerator := a, denominator := 1, isNaN := false }

/-- Constructor: NaN when the denominator is zero, otherwise normalized. -/
def ratio (num denum : Int) : Ratio :=
  if denum == 0 then R_NaN else normalizeRatio num denum

/-- Ratio (cross-multiplication) equality. False if either operand is NaN. -/
def eqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else a.numerator * b.denominator == b.numerator * a.denominator

/-- Strict less-than. False if either operand is NaN. -/
def ltRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator < b.numerator * a.denominator)

/-- Less-than-or-equal. False if either operand is NaN. -/
def leqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator ≤ b.numerator * a.denominator)

/-- Strict greater-than. False if either operand is NaN. -/
def gtRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator > b.numerator * a.denominator)

/-- Greater-than-or-equal. False if either operand is NaN. -/
def geqRatio (a b : Ratio) : Bool :=
  if a.isNaN || b.isNaN then false
  else decide (a.numerator * b.denominator ≥ b.numerator * a.denominator)

/-- Addition; NaN propagates. -/
def addRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator + b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Subtraction; NaN propagates. -/
def subRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.denominator - b.numerator * a.denominator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Multiplication; NaN propagates. -/
def mulRatio (a b : Ratio) : Ratio :=
  if a.isNaN || b.isNaN then R_NaN
  else { numerator := a.numerator * b.numerator,
         denominator := a.denominator * b.denominator, isNaN := false }

/-- Negation; NaN propagates. -/
def negate (a : Ratio) : Ratio :=
  if a.isNaN then R_NaN
  else { numerator := -a.numerator, denominator := a.denominator, isNaN := false }

/-- A ratio is valid when it is not NaN. -/
def isValidRatio (a : Ratio) : Bool := !a.isNaN

/-- A ratio is valid and normalized when not NaN and the denominator is positive. -/
def isValidAndNormalizedRatio (a : Ratio) : Bool :=
  !a.isNaN && decide (a.denominator > 0)

end Ratio
```

- [ ] **Step 2: Type-check the library**

Run: `lake build Ratio`
Expected: build succeeds, no errors.

- [ ] **Step 3: Commit**

```bash
git add Ratio/Ratio.lean
git commit -m "feat: complete Addition-reachable Ratio operations"
```

---

## Task 3: AdditionBasics (concrete-constant checks)

**Files:**
- Create: `Tests/Ratio/Addition.lean`

- [ ] **Step 1: Create** `Tests/Ratio/Addition.lean` with the basics block

```lean
import Ratio.Ratio

open Ratio

namespace Tests.Ratio.Addition

/- AdditionBasics -/

-- ADD_ZERO_TWICE: 0 + 0 = 0
#blaster [ ((addRatio R_ZERO R_ZERO == R_ZERO) && eqRatio (addRatio R_ZERO R_ZERO) R_ZERO) = true ]

-- ONE_SUCC: 0 + 1 = 1
#blaster [ ((addRatio R_ZERO R_ONE == R_ONE) && eqRatio (addRatio R_ZERO R_ONE) R_ONE) = true ]

-- ADD_HALF_TWICE: 0.5 + 0.5 = 1
#blaster [ (eqRatio (addRatio R_HALF R_HALF) R_ONE) = true ]

-- ADD_ONE_TWICE: 1 + 1 = 2
#blaster [ ((addRatio R_ONE R_ONE == fromInteger 2) && eqRatio (addRatio R_ONE R_ONE) (fromInteger 2)) = true ]

-- ONE_NEGATE: 1 + (-1) = 0
#blaster [ (addRatio R_ONE (negate R_ONE) == R_ZERO) = true ]

-- ADD_CONSTANTS_1: 85/100 + 15/100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 100)) R_ONE) = true ]

-- ADD_CONSTANTS_2: 85/100 + 150/1000 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 150 1000)) R_ONE) = true ]

-- ADD_CONSTANTS_3: 85/100 + -15/100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) 100)) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_4: 85/100 + 15/-100 = 70/100
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio 15 (-100))) (ratio 70 100)) = true ]

-- ADD_CONSTANTS_5: 85/100 + -15/-100 = 1
#blaster [ (eqRatio (addRatio (ratio 85 100) (ratio (-15) (-100))) R_ONE) = true ]

end Tests.Ratio.Addition
```

- [ ] **Step 2: Run the file**

Run: `lake env lean Tests/Ratio/Addition.lean`
Expected: ten `✅ Valid` messages, no errors.

- [ ] **Step 3: Commit**

```bash
git add Tests/Ratio/Addition.lean
git commit -m "test: AdditionBasics ratio checks via #blaster"
```

---

## Task 4: Commutativity, Associativity, Identity, Negation

**Files:**
- Modify: `Tests/Ratio/Addition.lean`

- [ ] **Step 1: Append** these blocks to `Tests/Ratio/Addition.lean`, immediately before `end Tests.Ratio.Addition`

```lean
/- AdditionCommutativity -/

-- ADD_COMMUTATIVITY
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true → b.isNaN = false →
  (addRatio a b == addRatio b a) = true ]

/- AdditionAssociativity -/

-- ADD_ASSOCIATIVITY_1: (a + b) + c = a + (b + c)
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (addRatio (addRatio a b) c == addRatio a (addRatio b c)) = true ]

-- ADD_ASSOCIATIVITY_2: (a + c) + b = (a + b) + c
#blaster [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (addRatio (addRatio a c) b == addRatio (addRatio a b) c) = true ]

/- AdditionIdentity -/

-- IDENTITY_LEFT: 0 + a = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((addRatio R_ZERO a == a) && eqRatio (addRatio R_ZERO a) a) = true ]

-- IDENTITY_RIGHT: a + 0 = a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((addRatio a R_ZERO == a) && eqRatio (addRatio a R_ZERO) a) = true ]

/- AdditionNegation -/

-- ADD_OPPOSITE: a + (-a) = 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a (negate a)) R_ZERO) = true ]

-- ADD_NEG_DISTRIB: -(a + b) = -a + -b
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (negate (addRatio a b) == addRatio (negate a) (negate b)) = true ]
```

- [ ] **Step 2: Run the file**

Run: `lake env lean Tests/Ratio/Addition.lean`
Expected: all `#blaster` (the 10 basics + these 7) print `✅ Valid`.
If any of the new ones print `⚠️ Undetermined`, add `(timeout: 30)` after `#blaster` for that check and re-run (these are nonlinear — see spec Risk 2).

- [ ] **Step 3: Commit**

```bash
git add Tests/Ratio/Addition.lean
git commit -m "test: Addition commutativity/associativity/identity/negation checks"
```

---

## Task 5: AdditionRelational

**Files:**
- Modify: `Tests/Ratio/Addition.lean`

Note: Lustre `=` between two Bool predicate results is an iff, translated as `==`. These are nonlinear; `(timeout: 60)` is pre-applied to the iff checks defensively. If any prints `⚠️ Undetermined`, that is an acceptable, documented limitation of the slice (spec Risk 2), not a failure of the workflow — record it in the commit message and move on.

- [ ] **Step 1: Append** this block before `end Tests.Ratio.Addition`

```lean
/- AdditionRelational -/

-- ADD_TWICE_EQ_MUL_BY_2: a + a = 2 * a
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  (eqRatio (addRatio a a) (mulRatio (fromInteger 2) a)) = true ]

-- ADD_GT_POS: a > 0 → b > 0 → a + b > 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  gtRatio a R_ZERO = true → gtRatio b R_ZERO = true →
  (gtRatio (addRatio a b) R_ZERO) = true ]

-- ADD_LT_NEG: a < 0 → b < 0 → a + b < 0
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  ltRatio a R_ZERO = true → ltRatio b R_ZERO = true →
  (ltRatio (addRatio a b) R_ZERO) = true ]

-- ADD_OPP_GEQ_POS: a < 0 → a + b ≥ 0 → b ≥ -a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  ltRatio a R_ZERO = true → geqRatio (addRatio a b) R_ZERO = true →
  (geqRatio b (negate a)) = true ]

-- ADD_OPP_LEQ_NEG: a > 0 → a + b ≤ 0 → b ≤ -a
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  gtRatio a R_ZERO = true → leqRatio (addRatio a b) R_ZERO = true →
  (leqRatio b (negate a)) = true ]

-- ADD_REQ_IFF: (a + b = a + c) ↔ (b = c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a b) (addRatio a c) == eqRatio b c) = true ]

-- ADD_RLT_IFF: (a + b < a + c) ↔ (b < c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (ltRatio (addRatio a b) (addRatio a c) == ltRatio b c) = true ]

-- ADD_RLEQ_IFF: (a + b ≤ a + c) ↔ (b ≤ c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (leqRatio (addRatio a b) (addRatio a c) == leqRatio b c) = true ]

-- ADD_RGT_IFF: (a + b > a + c) ↔ (b > c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (gtRatio (addRatio a b) (addRatio a c) == gtRatio b c) = true ]

-- ADD_RGEQ_IFF: (a + b ≥ a + c) ↔ (b ≥ c)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (geqRatio (addRatio a b) (addRatio a c) == geqRatio b c) = true ]

-- ADD_EQ_SWAP: (a + b = c) ↔ (a = c - b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true →
  (eqRatio (addRatio a b) c == eqRatio a (subRatio c b)) = true ]

-- Normalization lemmas (numerator/denominator carry at most a shared sign flip)
#blaster [ ∀ (a_n a_d : Int),
  let a := ratio a_n a_d
  isValidRatio a = true →
  ((((a.denominator == -a_d) && (a.numerator == -a_n))
    || ((a.denominator == a_d) && (a.numerator == a_n)))) = true ]
```

- [ ] **Step 2: Run the file**

Run: `lake env lean Tests/Ratio/Addition.lean`
Expected: each `#blaster` prints `✅ Valid`, OR a nonlinear iff check prints `⚠️ Undetermined` (acceptable per Risk 2 — note which).

- [ ] **Step 3: Commit**

```bash
git add Tests/Ratio/Addition.lean
git commit -m "test: AdditionRelational checks (nonlinear, timeouts applied)"
```

---

## Task 6: AdditionValidity

**Files:**
- Modify: `Tests/Ratio/Addition.lean`

- [ ] **Step 1: Append** this block before `end Tests.Ratio.Addition`

```lean
/- AdditionValidity -/

-- ADD_NOT_VALIDRATIO_LEFT: ¬valid a → valid b → ¬valid (a + b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = false → isValidRatio b = true →
  (isValidRatio (addRatio a b)) = false ]

-- ADD_NOT_VALIDRATIO_RIGHT: valid a → ¬valid b → ¬valid (a + b)
#blaster [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = false →
  (isValidRatio (addRatio a b)) = false ]

-- ADD_VALID_AND_NORMALIZED_RATIO: valid a → valid b → validAndNormalized (a + b)
#blaster (timeout: 60) [ ∀ (a_n a_d b_n b_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  isValidRatio a = true → isValidRatio b = true →
  (isValidAndNormalizedRatio (addRatio a b)) = true ]
```

- [ ] **Step 2: Run the file**

Run: `lake env lean Tests/Ratio/Addition.lean`
Expected: the two validity-propagation checks print `✅ Valid`; the normalized check prints `✅ Valid` (it needs `a.den > 0 ∧ b.den > 0 → a.den * b.den > 0`, nonlinear — `⚠️ Undetermined` is acceptable, note it).

- [ ] **Step 3: Commit**

```bash
git add Tests/Ratio/Addition.lean
git commit -m "test: AdditionValidity propagation checks"
```

---

## Task 7: AdditionDistributivity (the nonlinear canary)

**Files:**
- Modify: `Tests/Ratio/Addition.lean`

Note: the source annotates this `-- 25 sec` for Kind2. Expect it to be the slowest. The Lustre node bundles normalization/positivity lemmas into the conjunction; we port them verbatim because they shape the search.

- [ ] **Step 1: Append** this block before `end Tests.Ratio.Addition`

```lean
/- AdditionDistributivity -/

-- ADD_MUL_DISTRIB: (a + b) * c = (a * c) + (b * c), plus the source's normalization/positivity lemmas
#blaster (timeout: 120) [ ∀ (a_n a_d b_n b_d c_n c_d : Int),
  let a := ratio a_n a_d
  let b := ratio b_n b_d
  let c := ratio c_n c_d
  isValidRatio a = true → isValidRatio b = true → isValidRatio c = true →
  ( eqRatio (mulRatio (addRatio a b) c) (addRatio (mulRatio a c) (mulRatio b c))
    && (((a.denominator == -a_d) && (a.numerator == -a_n)) || ((a.denominator == a_d) && (a.numerator == a_n)))
    && (((b.denominator == -b_d) && (b.numerator == -b_n)) || ((b.denominator == b_d) && (b.numerator == b_n)))
    && (((c.denominator == -c_d) && (c.numerator == -c_n)) || ((c.denominator == c_d) && (c.numerator == c_n)))
    && decide ((addRatio (mulRatio a c) (mulRatio b c)).denominator > 0)
    && decide ((mulRatio a c).denominator > 0)
    && decide ((mulRatio b c).denominator > 0)
    && decide ((mulRatio (addRatio a b) c).denominator > 0)
    && decide ((addRatio a b).denominator > 0)
    && decide (a.denominator > 0)
    && decide (b.denominator > 0)
    && decide (c.denominator > 0) ) = true ]
```

- [ ] **Step 2: Run the file**

Run: `lake env lean Tests/Ratio/Addition.lean`
Expected: `✅ Valid` if Z3 closes it within 120s; `⚠️ Undetermined` is an acceptable, documented outcome for this nonlinear property (spec Risk 2). Record the outcome.

- [ ] **Step 3: Commit**

```bash
git add Tests/Ratio/Addition.lean
git commit -m "test: AdditionDistributivity check (nonlinear, 120s timeout)"
```

---

## Task 8: Wire into the test driver and final build

**Files:**
- Modify: `Tests.lean`

- [ ] **Step 1: Register the new test module.** Append to `Tests.lean`:

```lean
import Tests.Ratio.Addition
```

(Leave `Tests/Ratio/Probe.lean` out of the aggregate — it was a one-off validation artifact. It stays in the repo for reference but is not imported into the driver.)

- [ ] **Step 2: Build the full test library**

Run: `lake build Tests`
Expected: build succeeds. Any `⚠️ Undetermined` on the nonlinear checks surfaces here as info/warning messages, not build failures.

- [ ] **Step 3: Commit**

```bash
git add Tests.lean
git commit -m "test: register Ratio Addition suite in test driver"
```

---

## Self-review notes (for the executor)

- **Spec coverage:** all 9 Addition theorem files are covered — Basics (Task 3), Commutativity/Associativity/Identity/Negation (Task 4), Relational (Task 5), Validity (Task 6), Distributivity (Task 7). The library's Addition-reachable ops are in Task 2. The BEq risk (spec Risk 1) is Task 1; the nonlinear risk (spec Risk 2) is handled with `(timeout:)` in Tasks 5–7.
- **Out of scope (do not add here):** the other ~66 theorem groups and the `div`-based ops (`quotient`/`truncate`/`ceil`/`truncateRecipRatio`) — those need the Int-division-semantics reconciliation called out in the spec.
- **Type/name consistency:** function names used in tests (`ratio`, `addRatio`, `subRatio`, `mulRatio`, `negate`, `fromInteger`, `eqRatio`, `ltRatio`, `leqRatio`, `gtRatio`, `geqRatio`, `isValidRatio`, `isValidAndNormalizedRatio`) and constants (`R_ZERO`, `R_ONE`, `R_HALF`, `R_NaN`) all match the definitions in Task 2.
