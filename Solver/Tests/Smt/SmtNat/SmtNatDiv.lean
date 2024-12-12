import Lean
import Solver.Command.Syntax

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

#solve [∀ (x y z : Nat), 0 < z → x ≤ y / z ↔ x * z ≤ y]

#solve [∀ (x y z : Nat), x / y / z = x / (y * z)]

#solve [∀ (x y : Nat), x / y * y ≤ x]

#solve [∀ (x y z : Nat), 0 < z → x / z < y ↔ x < y * z]


/-! # Test cases to ensure that counterexample are properly detected -/
