import Blaster

namespace Test.SmtNatMod

/-! ## Test objectives to validate `Nat.mod` semantics with backend solver -/

/-! # Test cases to validate `Nat.mod` semantics with backend solver -/

#blaster [∀ (x y : Nat),  x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x]

#blaster [∀ (x : Nat), x % 0 = x]

#blaster [∀ (x : Nat), x % x = 0]

#blaster [∀ (x : Nat), x % 1 = 0]

#blaster [∀ (x y : Nat), x < y → x % y = x]

#blaster [∀ (x : Nat), 1 % x = 0 ↔ x = 1]

#blaster [∀ (x : Nat), (0 = 1 % x ↔ x = 1)]

#blaster [∀ (x y : Nat), x ≥ y → x % y = (x - y) % y]

#blaster [∀ (x y : Nat), y > 0 → x % y < y]

#blaster [∀ (x y : Nat), 0 < x → x - y % x + y % x = x]

#blaster [∀ (x y : Nat), x % y ≤ x]

#blaster [∀ (x y : Nat), x % y + y * (x / y) = x]

#blaster [∀ (x y : Nat), x % y = x - y * (x / y)]

#blaster [∀ (x y : Nat), (x + y) % y = x % y]

#blaster (random-seed: 2) [∀ (x y z : Nat), (x + y * z) % y = x % y]

#blaster [∀ (x y : Nat), (x * y) % x = 0]

#blaster (random-seed: 3) [∀ (x y z : Nat), (z * x) % (z * y) = z * (x % y)]


/-! # Test cases to ensure that counterexample are properly detected -/


#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → x % y ≠ x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 1 → x % y ≠ 0]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y ≥ y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x ≥ y → x % y ≠ (x - y) % y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y > x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x % y + y * (x / y) ≠ x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x + y) % y ≠ x % y]

end Test.SmtNatMod
