import Blaster

namespace Test.SmtSolverCvc5

/-! ## Test objectives to validate the cvc5 backend (`solver:` option)

    These tests exercise the cvc5 solver adapter end-to-end: process spawning,
    option translation, result parsing, and counterexample retrieval through
    standard SMT-LIB `get-value`. They require a `cvc5` executable on `PATH`.
-/

/-! # Valid goals (unsat queries) -/

#blaster (solver: cvc5) [∀ (x : Nat), 0 < x → 0^x = 0]

#blaster (solver: cvc5) [∀ (x y : Int), x + y = y + x]

#blaster (solver: cvc5) [∀ (b : Bool), b = true ∨ b = false]

#blaster (solver: cvc5) [∀ (s : String), s ++ "" = s]

/-! # Falsified goals (sat queries) with scalar counterexamples -/

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x : Int), x + 3 > 7]

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x y : Nat), x ≤ y]

/-! # Falsified goals with inductive datatype counterexamples -/

structure Point where
  x : Int
  y : Int

#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (p : Point), p.x + p.y > 0]


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

     These checks assert the verdict without pinning solver-generated values,
     whose spelling is solver- and version-dependent. -/

-- uninterpreted-sort element values (e.g. cvc5 1.3.4: `@@Instance_uniq.…_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (α : Type) (x y : α), x = y]

-- uninterpreted function value (e.g. cvc5 1.3.4: `@(@@ArrowT2 Int Int)_0`)
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) (timeout: 10) [∀ (f : Int → Int) (x : Int), f x = f (x + 1)]


end Test.SmtSolverCvc5
