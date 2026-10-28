import Blaster

namespace Test.FiniteField.OrdinaryCvc5Baseline

/-! Ordinary cvc5 baseline adapted from `TestsCvc5/Cvc5FinBaseline.lean` at
    `724e32c377b5c6bfdecaf200984203b21c75355b`. This standalone file uses no
    native finite-field syntax or CoCoA-specific functionality. Selecting
    cvc5 does not change the solver-independent rejection of `Fin` binders. -/

/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (solver: cvc5)
  [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (solver: cvc5) [∀ (a : Fin 7), a * a ≠ 2]

-- This closed goal is settled by optimization, not by the selected solver.
/-- info: ✅ Valid -/
#guard_msgs in
#blaster (solver: cvc5) [(1 : Fin 7) / 2 = 0]

-- Bounded Nat representatives exercise ordinary cvc5 integer arithmetic.
/-- info: ✅ Valid -/
#guard_msgs in
#blaster (solver: cvc5)
  [∀ (a b c : Nat), a < 7 → b < 7 → c < 7 →
     (a * ((b + c) % 7)) % 7 = ((a * b) % 7 + (a * c) % 7) % 7]

end Test.FiniteField.OrdinaryCvc5Baseline
