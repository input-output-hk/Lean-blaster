import Blaster

namespace Test.SmtNatAdd

/-! ## Test objectives to validate `Nat.add` semantics with the backend solver -/

/-! # Test cases to validate `Nat` domain -/

#blaster (solver: all) [∀ (x : Nat), x ≥ 0]

#blaster (solver: all) [∀ (x y : Nat), x + y ≥ 0]


/-! # Test cases to validate `Nat.add` semantics with backend solver -/

#blaster (solver: all) [∀ (x : Nat), x + 1 > 0]

#blaster (solver: all) [∀ (x y : Nat), x + y >= x]

#blaster (solver: all) [∀ (x y : Nat), x + y >= y]

#blaster (solver: all) [∀ (x y : Nat), x > 0 → y > 0 → x + y > y]

#blaster (solver: all) [∀ (x y : Nat), x > 0 → y > 0 → x + y > x]

#blaster (solver: all) [∀ (x y : Nat), (Nat.succ x) + y = Nat.succ (x + y)]

#blaster (solver: all) [∀ (x y : Nat), x + y = y + x]

#blaster (solver: all) [∀ (x y z : Nat), (x + y) + z = x + (y + z)]

#blaster (solver: all) [∀ (x y z : Nat), x + (y + z) = y + (x + z)]

#blaster (solver: all) [∀ (x y z : Nat), (x + y) + z = (x + z) + y]

#blaster (solver: all) [∀ (x y z : Nat), x + y = x + z → y = z]

#blaster (solver: all) [∀ (x y : Nat), x + y = 0 → x = 0 ∧ y = 0]

#blaster (solver: all) [∀ (x : Nat), Nat.succ x ≠ 0]

#blaster (solver: all) [∀ (x : Nat), Nat.succ x ≠ x]

#blaster (solver: all) [∀ (x y : Nat), Nat.succ x ≤ y ↔ x < y]

#blaster (solver: all) [∀ (x y : Nat), (x < Nat.succ y) ↔ x ≤ y]

#blaster (solver: all) [∀ (x y : Nat), (Nat.succ x = Nat.succ y) ↔ x = y]

#blaster (solver: all) [∀ (x : Nat), x ≠ 0 → ∃ (y : Nat), x = Nat.succ y]

#blaster (solver: all) [∀ (x y : Nat), (1 + x ≤ y) = (x < y)]
#blaster (solver: all) [∀ (x y : Nat), (x < 1 + y) = (x ≤ y)]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y < x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y < y]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y != y]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y != x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x + y ≠ y + x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (x ≤ y + 1) = (x < y)]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), (1 + x < y) = (x ≤ y)]

end Test.SmtNatAdd
