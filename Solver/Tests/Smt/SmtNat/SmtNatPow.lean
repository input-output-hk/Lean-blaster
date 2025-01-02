import Solver.Command.Syntax

namespace Tests.SmtNatPow

/-! ## Test objectives to validate `Nat.pow` semantics with backend solver -/

/-! # Test cases to validate `Nat.pow` semantics with backend solver -/

#solve [∀ (x : Nat), x^0 = 1]

#solve [∀ (x y : Nat), x^(Nat.succ y) = x^y * x]

#solve [∀ (x y : Nat), x^(y + 1) = x^y * x]

#solve [∀ (x y : Nat), x ≤ y → ∀ (i : Nat), x^i ≤ y^i]

#solve [∀ (x y : Nat), 0 < x → 0 < x^y]

#solve [∀ (x : Nat), 0 < x → 0^x = 0]

#solve [∀ (x : Nat), 0 < 2^x]


/-! # Test cases to ensure that counterexample are properly detected -/

end Tests.SmtNatPow
