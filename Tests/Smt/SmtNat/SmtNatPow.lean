import Solver.Command.Syntax

namespace Test.SmtNatPow

/-! ## Test objectives to validate `Nat.pow` semantics with backend solver -/

/-! # Test cases to validate `Nat.pow` semantics with backend solver -/

#solve (only-optimize: 1) [∀ (x : Nat), x^0 = 1]

#solve (only-optimize: 1) [∀ (x y : Nat), x^y * x = x^(y + 1)]

#solve (only-optimize: 1) [∀ (x y : Nat), x^(y + 1) * x = x^(y + 2)]

#solve (only-optimize: 1) [∀ (x y : Nat), x^(Nat.succ y) = x^y * x]

#solve (only-optimize: 1) [∀ (x y : Nat), x^(y + 1) = x^y * x]

#solve (only-optimize: 1) [∀ (x y : Nat), x^y * x * x * x = x^(y + 3)]

#solve (only-optimize: 1) [∀ (x y : Nat), x * x^y * x * x = x^(y + 3)]

#solve [∀ (x : Nat), 0 < x → 0^x = 0]

-- NOTE: remove solve option when induction schema implemented
#solve (timeout: 5) (solve-result: 2) [(∀ (x y : Nat), x ≤ y → ∀ (i : Nat), x^i ≤ y^i)]

-- NOTE: remove solve option when induction schema implemented
#solve (timeout: 5) (solve-result: 2) [∀ (x y : Nat), 0 < x → 0 < x^y]

-- NOTE: remove solve option when induction schema implemented
#solve (timeout: 5) (solve-result: 2) [∀ (x : Nat), 0 < 2^x]

-- NOTE: remove solve option when induction schema implemented
#solve (timeout: 5) (solve-result: 2) [∀ (x : Nat), 2^(x + x) = 2^x * 2^x]

/-! # Test cases to ensure that counterexample are properly detected -/

#solve (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x^0 ≠ 1]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x^(Nat.succ y) = x^y]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), 0 < x → 0^x > 0]

end Test.SmtNatPow
