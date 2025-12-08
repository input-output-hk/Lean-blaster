import Blaster

namespace Test.SmtNatAdd

/-! ## Test objectives to validate `Nat.add` semantics with the backend solver -/

/-! # Test cases to validate `Nat` domain -/

#blaster [∀ (x : Nat), x ≥ 0]

#blaster [∀ (x y : Nat), x + y ≥ 0]


/-! # Test cases to validate `Nat.add` semantics with backend solver -/

#blaster [∀ (x : Nat), x + 1 > 0]

#blaster [∀ (x y : Nat), x + y >= x]

#blaster [∀ (x y : Nat), x + y >= y]

#blaster [∀ (x y : Nat), x > 0 → y > 0 → x + y > y]

#blaster [∀ (x y : Nat), x > 0 → y > 0 → x + y > x]

#blaster [∀ (x y : Nat), (Nat.succ x) + y = Nat.succ (x + y)]

#blaster [∀ (x y : Nat), x + y = y + x]

#blaster [∀ (x y z : Nat), (x + y) + z = x + (y + z)]

#blaster [∀ (x y z : Nat), x + (y + z) = y + (x + z)]

#blaster [∀ (x y z : Nat), (x + y) + z = (x + z) + y]

#blaster [∀ (x y z : Nat), x + y = x + z → y = z]

#blaster [∀ (x y : Nat), x + y = 0 → x = 0 ∧ y = 0]

#blaster [∀ (x : Nat), Nat.succ x ≠ 0]

#blaster [∀ (x : Nat), Nat.succ x ≠ x]

#blaster [∀ (x y : Nat), Nat.succ x ≤ y ↔ x < y]

#blaster [∀ (x y : Nat), (x < Nat.succ y) ↔ x ≤ y]

#blaster [∀ (x y : Nat), (Nat.succ x = Nat.succ y) ↔ x = y]

#blaster [∀ (x : Nat), x ≠ 0 → ∃ (y : Nat), x = Nat.succ y]

#blaster [∀ (x y : Nat), (1 + x ≤ y) = (x < y)]
#blaster [∀ (x y : Nat), (x < 1 + y) = (x ≤ y)]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y < x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y < y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y != y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y != x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y ≠ y + x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x ≤ y + 1) = (x < y)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (1 + x < y) = (x ≤ y)]

end Test.SmtNatAdd
