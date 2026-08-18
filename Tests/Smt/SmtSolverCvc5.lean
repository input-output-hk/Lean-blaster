import Blaster

namespace Test.SmtSolverCvc5

/-! ## Test objectives to validate the cvc5 backend (`solver:` option)

    These tests exercise the cvc5 solver adapter end-to-end: process spawning,
    default option translation, the `print-success` handshake, `check-sat`
    result parsing, counterexample retrieval through `get-value` and model
    reconstruction as Lean-flavored display strings (see `Blaster.Smt.Model`).
    They require a `cvc5` executable (≥ 1.2.1) in the PATH.

    NOTE: the reconstruction tests pin their counterexample display strings
    with `#guard_msgs`. Each negated goal forces the displayed counterexample
    assignment, and the pins define the expected rendering for the cvc5
    configurations exercised by this suite.
-/

/-! # Valid goals (unsat queries) -/

#blaster (solver: cvc5) [∀ (x : Nat), 0 < x → 0^x = 0]

#blaster (solver: cvc5) [∀ (x y : Int), x + y = y + x]

#blaster (solver: cvc5) [∀ (b : Bool), b = true ∨ b = false]

#blaster (solver: cvc5) [∀ (s : String), s ++ "" = s]

/-! # Falsified goals (sat queries) with scalar counterexamples -/

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x : Int), x + 3 > 7]

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x y : Nat), x ≤ y]

/-! # Falsified goals with inductive datatype counterexamples
     (cvc5 emits `as`-qualified constructor terms; z3 wraps long values over
      several lines — both are reconstructed by `Blaster.Smt.Model`) -/

structure Point where
  x : Int
  y : Int

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (p : Point), p.x + p.y > 0]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - o: Option.none
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (o : Option Int), o ≠ none]

/-! # Model reconstruction: forced counterexamples pinned as display strings

     Each negated goal has a single concrete witness, whose Lean-flavored
     display is pinned below. -/

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: 3
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x : Int), x ≠ 3]

-- Constructor application with a negative field
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - p: Test.SmtSolverCvc5.Point.mk 1 (-2)
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (p : Point), p ≠ Point.mk 1 (-2)]

-- Parametric constructor application (cvc5: `((as Option.some (@Option Int)) 5)`)
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - o: Option.some 5
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (o : Option Int), o ≠ some 5]

-- Tuple (cvc5: `((as Prod.mk (@Prod Int Bool)) 5 true)`)
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - t: (5, true)
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (t : Int × Bool), t ≠ (5, true)]

-- List (cvc5 shares the `as`-qualified cons through a `let` binding)
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - l: [1, 2]
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (l : List Int), l ≠ [1, 2]]

-- String (SMT-LIB escaping round trip: emitted as `"a""b"`, displayed Lean-quoted)
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - s: "a\"b"
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (s : String), s ≠ "a\"b"]

/-! # Recursive function definitions (define-fun-rec) -/

#blaster (solver: cvc5) [∀ (x : Nat), x^1 = x]

/-! # Undetermined goal through the per-check time limit (tlimit-per) -/

-- The tested cvc5 configurations are expected to return Undetermined for this
-- quantified goal under the 5s per-check limit. Solver heuristics and timing
-- can vary across machines and versions, so this is a bounded regression
-- expectation rather than a general semantic guarantee.
-- NOTE: remove solve option when induction schema implemented
#blaster (solver: cvc5) (timeout: 5) (solve-result: 2) [∀ (x : Nat), 0 < 2^x]

/-! # Model production without a Lean counterpart

     The negated goals below are satisfiable only with values that have no
     Lean rendering (uninterpreted-sort elements, uninterpreted functions), so
     `get-value` answers with solver-invented constants that fall back to raw
     display. No `#guard_msgs` here: the spelling of those constants is
     solver- and version-dependent (it even embeds elaboration-unique name
     indices), so pinning it would break on harmless upgrades. The regression
     value is: translation succeeds, no crash, no hang, and the Falsified
     verdict is asserted through `solve-result: 1`. -/

-- uninterpreted-sort element values (e.g. cvc5 1.3.4: `@@Instance_uniq.…_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (α : Type) (x y : α), x = y]

-- uninterpreted function value (e.g. cvc5 1.3.4: `@(@@ArrowT2 Int Int)_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]


end Test.SmtSolverCvc5
