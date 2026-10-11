import Blaster

namespace Test.SmtNatDiv

/-! ## Test objectives to validate `Nat.div` semantics with backend solver -/

/-! # Test cases to validate `Nat.div` semantics with backend solver -/

#blaster [∀ (x y : Nat), x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0]

#blaster [∀ (x y : Nat), x / y ≤ x]

#blaster [∀ (x y : Nat), 0 < x → 1 < y → x / y < x]

#blaster [∀ (x y : Nat), x * (y / x) + y % x = y]

#blaster [∀ (x y : Nat), 0 < x → x ≤ y → y / x = (y - x) / x + 1]

#blaster [∀ (x y : Nat), x % y + y * (x / y) = x]

#blaster [∀ (x : Nat), x / 1 = x]

#blaster [∀ (x : Nat), x / 0 = 0]

#blaster [∀ (x : Nat), 0 / x = 0]

#blaster [∀ (x y z : Nat), 0 < z → (x ≤ y / z ↔ x * z ≤ y)]

#blaster [∀ (x y z : Nat), x / y / z = x / (y * z)]

#blaster [∀ (x y : Nat), x / y * y ≤ x]

#blaster [∀ (x y z : Nat), 0 < z → (x / z < y ↔ x < y * z)]

#blaster [∀ (x z : Nat), (0 < z) → (x + z) / z = (x / z) + 1]

#blaster [∀ (x z y : Nat), (0 < y) → (x + y * z) / y = x / y + z]

#blaster [∀ (x y z : Nat), z * x ≤ y → y < (z + 1) * x → y / x = z]

#blaster [∀ (x y z : Nat), (y*z ≤ x) → (x - y*z) / y = x / y - z]

#blaster [∀ (x y z : Nat), x < y*z → (y * z - (x + 1)) / y = z - ((x / y) + 1)]

#blaster [∀ (x y: Nat), 0 < y → x * y / y = x]

#blaster [∀ (x y z : Nat), x ≤ z * y → x / z ≤ y]

#blaster [∀ (x y z : Nat), 0 < x → y = z * x → y / x = z]

#blaster [∀ (x y z : Nat), 0 < x → x * y / (x * z) = y / z]

#blaster [∀ (x y : Nat), y * (x / y) ≤ x]


/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x / y > x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x / y > y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → x / y ≠ 0]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 1 → x / y ≠ x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x / y * y > x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y: Nat), 0 < y → x * y / y ≠ x]

end Test.SmtNatDiv
