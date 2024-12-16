import Lean
import Solver.Command.Syntax

/-! ## Test objectives to validate `Nat.mod` semantics with backend solver -/

/-! # Test cases to validate `Nat.mod` semantics with backend solver -/

#solve [∀ (x y : Nat),  x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x]

#solve [∀ (x : Nat), x % 0 = x]

#solve [∀ (x : Nat), x % x = 0]

#solve [∀ (x : Nat), x % 1 = 0]

#solve [∀ (x y : Nat), x < y → x % y = x]

#solve [∀ (x : Nat), 1 % x = 0 ↔ x = 1]

#solve [∀ (x : Nat), (0 = 1 % x ↔ x = 1)]

#solve [∀ (x y : Nat), x ≥ y → x % y = (x - y) % y]

#solve [∀ (x y : Nat), y > 0 → x % y < y]

#solve [∀ (x y : Nat), 0 < x → x - y % x + y % x = x]

#solve [∀ (x y : Nat), x % y ≤ x]

#solve [∀ (x y : Nat), x % y + y * (x / y) = x]

#solve [∀ (x y : Nat), x % y = x - y * (x / y)]

#solve [∀ (x y : Nat), (x + y) % y = x % y]

-- NOTE: may have z3 running forever or crash with ASSERTION VIOLATION
#solve [∀ (x y z : Nat), (x + y * z) % y = x % y]

#solve [∀ (x y : Nat), (x * y) % x = 0]

#solve [∀ (x y z : Nat), (z * x) % (z * y) = z * (x % y)]


/-! # Test cases to ensure that counterexample are properly detected -/
