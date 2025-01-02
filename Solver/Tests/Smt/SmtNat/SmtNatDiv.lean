import Lean
import Solver.Command.Syntax

namespace Tests.SmtNatDiv

/-! ## Test objectives to validate `Nat.div` semantics with backend solver -/

/-! # Test cases to validate `Nat.div` semantics with backend solver -/

#solve [∀ (x y : Nat), x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0]

#solve [∀ (x y : Nat), x / y ≤ x]

#solve [∀ (x y : Nat), 0 < x → 1 < y → x / y < x]

#solve [∀ (x y : Nat), x * (y / x) + y % x = y]

#solve [∀ (x y : Nat), 0 < x → x ≤ y → y / x = (y - x) / x + 1]

#solve [∀ (x y : Nat), x % y + y * (x / y) = x]

#solve [∀ (x : Nat), x / 1 = x]

#solve [∀ (x : Nat), x / 0 = 0]

#solve [∀ (x : Nat), 0 / x = 0]

#solve [∀ (x y z : Nat), 0 < z → (x ≤ y / z ↔ x * z ≤ y)]

#solve [∀ (x y z : Nat), x / y / z = x / (y * z)]

#solve [∀ (x y : Nat), x / y * y ≤ x]

#solve [∀ (x y z : Nat), 0 < z → (x / z < y ↔ x < y * z)]

#solve [∀ (x z : Nat), (0 < z) → (x + z) / z = (x / z) + 1]

#solve [∀ (x z y : Nat), (0 < y) → (x + y * z) / y = x / y + z]

#solve [∀ (x y z : Nat), z * x ≤ y → y < (z + 1) * x → y / x = z]

#solve [∀ (x y z : Nat), (y*z ≤ x) → (x - y*z) / y = x / y - z]

#solve [∀ (x y z : Nat), x < y*z → (y * z - (x + 1)) / y = z - ((x / y) + 1)]

#solve [∀ (x y: Nat), 0 < y → x * y / y = x]

#solve [∀ (x y z : Nat), x ≤ z * y → x / z ≤ y]

#solve [∀ (x y z : Nat), 0 < x → y = z * x → y / x = z]

#solve [∀ (x y z : Nat), 0 < x → x * y / (x * z) = y / z]

#solve [∀ (x y : Nat), y * (x / y) ≤ x]


/-! # Test cases to ensure that counterexample are properly detected -/

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x / y > x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x / y > y]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), y = 0 → x / y ≠ 0]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), y = 1 → x / y ≠ x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x / y * y > x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y: Nat), 0 < y → x * y / y ≠ x]

end Tests.SmtNatDiv
