import Blaster

namespace Test.CounterexampleSpike

/-! Opt-in level-3 diagnostics capture the entire counterexample pipeline.
    This file is intentionally not imported by aggregate test targets because
    its diagnostic transcript is a saved spike artifact, not ordinary output. -/

-- Baseline: eligible top-level scalar, reconstructed successfully.
#blaster (solver: cvc5) (verbose: 3) (solve-result: 1) [∀ (x : Int), x ≠ 3]

-- A consecutive forall telescope keeps both source values eligible.
#blaster (solver: cvc5) (verbose: 3) (solve-result: 1) [∀ (x : Int), ∀ (y : Int), y = x]

-- A quantifier nested under a disjunction is not an eligible top-level source
-- binder. Its witness is therefore absent from the rendered evidence.
#blaster (solver: cvc5) (verbose: 3) (solve-result: 1)
  [∀ (x : Int), x = 0 ∨ (∀ (y : Int), y = x)]

-- Type-universe variables are intentionally excluded from `topLevelVars`.
-- The value variables remain retrievable as uninterpreted-sort elements.
#blaster (solver: cvc5) (verbose: 3) (solve-result: 1) (timeout: 10)
  [∀ (α : Type) (x y : α), x = y]

end Test.CounterexampleSpike
