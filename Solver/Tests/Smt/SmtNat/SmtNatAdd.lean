import Solver.Command.Syntax

namespace Tests.SmtNatAdd

/-! ## Test objectives to validate `Nat.add` semantics with the backend solver -/

/-! # Test cases to validate `Nat` domain -/

#solve [∀ (x : Nat), x ≥ 0]

#solve [∀ (x y : Nat), x + y ≥ 0]


/-! # Test cases to validate `Nat.add` semantics with backend solver -/

#solve [∀ (x : Nat), x + 1 > 0]

#solve [∀ (x y : Nat), x + y >= x]

#solve [∀ (x y : Nat), x + y >= y]

#solve [∀ (x y : Nat), x > 0 → y > 0 → x + y > y]

#solve [∀ (x y : Nat), x > 0 → y > 0 → x + y > x]

#solve [∀ (x y : Nat), (Nat.succ x) + y = Nat.succ (x + y)]

#solve [∀ (x y : Nat), x + y = y + x]

#solve [∀ (x y z : Nat), (x + y) + z = x + (y + z)]

#solve [∀ (x y z : Nat), x + (y + z) = y + (x + z)]

#solve [∀ (x y z : Nat), (x + y) + z = (x + z) + y]

#solve [∀ (x y z : Nat), x + y = x + z → y = z]

#solve [∀ (x y : Nat), x + y = 0 → x = 0 ∧ y = 0]

#solve [∀ (x : Nat), Nat.succ x ≠ 0]

#solve [∀ (x : Nat), Nat.succ x ≠ x]

#solve [∀ (x y : Nat), Nat.succ x ≤ y ↔ x < y]

#solve [∀ (x y : Nat), (x < Nat.succ y) ↔ x ≤ y]

#solve [∀ (x y : Nat), (Nat.succ x = Nat.succ y) ↔ x = y]

#solve [∀ (x : Nat), x ≠ 0 → ∃ (y : Nat), x = Nat.succ y]


/-! # Test cases to ensure that counterexample are properly detected -/

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x + y < x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x + y < y]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x + y != y]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x + y != x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x + y ≠ y + x]

end Tests.SmtNatAdd
