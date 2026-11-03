import Blaster

namespace Test.SmtSolverCvc5

/-! ## Test objectives to validate the cvc5 backend (`solver:` option)

    These tests exercise the cvc5 solver adapter end-to-end: process spawning,
    default option translation, the `print-success` handshake, `check-sat`
    result parsing, and raw counterexample retrieval through `get-value`.
    They require a `cvc5` executable (≥ 1.2.1) in the PATH.

    NOTE: scalar and string responses are pinned with `#guard_msgs`.
    Datatype queries also force concrete counterexample assignments, but their
    raw SMT-LIB syntax can vary across cvc5 versions (including `as` sort
    ascriptions and `let` bindings), so their exact output is not pinned.
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
     (cvc5 can emit `as`-qualified constructor terms, preserved as returned
      by the solver) -/

structure Point where
  x : Int
  y : Int

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (p : Point), p.x + p.y > 0]

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (o : Option Int), o ≠ none]

/-! # Forced counterexamples through the portable `get-value` command

     Each negated goal has a single concrete witness. Values retain their
     SMT-LIB representation, including constructor syntax and string escapes. -/

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
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (p : Point), p ≠ Point.mk 1 (-2)]

-- Parametric constructor application (cvc5: `((as Option.some (@Option Int)) 5)`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (o : Option Int), o ≠ some 5]

-- Tuple (cvc5: `((as Prod.mk (@Prod Int Bool)) 5 true)`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (t : Int × Bool), t ≠ (5, true)]

-- List (cvc5 shares the `as`-qualified cons through a `let` binding)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (l : List Int), l ≠ [1, 2]]

-- String: SMT-LIB's doubled-quote escaping is retained in the raw response.
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - s: "a""b"
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

/-! # Uninterpreted model values

     The negated goals below exercise uninterpreted-sort elements and
     uninterpreted functions. Their `get-value` responses contain
     solver-invented constants, displayed as returned by the solver.
     No `#guard_msgs` here: the spelling of those constants is
     solver- and version-dependent (it even embeds elaboration-unique name
     indices), so pinning it would break on harmless upgrades. The regression
     value is: translation succeeds, no crash, no hang, and the Falsified
     verdict is asserted through `solve-result: 1`. -/

-- uninterpreted-sort element values (e.g. cvc5 1.3.4: `@@Instance_uniq.…_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (α : Type) (x y : α), x = y]

-- uninterpreted function value (e.g. cvc5 1.3.4: `@(@@ArrowT2 Int Int)_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]


end Test.SmtSolverCvc5
