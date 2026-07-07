import Blaster

namespace Test.SmtNatSub

/-! ## Test objectives to validate `Nat.sub` semantics with backend solver -/

/-! # Test cases to validate `Nat.sub` semantics with backend solver -/

#blaster (solver: all) [∀ (x : Nat), 0 - x = 0]

#blaster (solver: all) [∀ (x y : Nat), x - (x + y) = 0]

#blaster (solver: all) [∀ (x y : Nat), x ≤ y → x - y = 0]

#blaster (solver: all) [∀ (x y : Nat), x > y → x - y > 0]

#blaster (solver: all) [∀ (x y : Nat), (x + y) - x = y]

#blaster (solver: all) [∀ (x y : Nat), (x + y) - y = x]

#blaster (solver: all) [∀ (x y : Nat), x - y ≤ Nat.succ x - y]

#blaster (solver: all) [∀ (x y : Nat), y < x → 0 < x - y]

#blaster (solver: all) [∀ (x y : Nat), y < x → x - (y + 1) < x - y]

#blaster (solver: all) [∀ (x y : Nat), x < y → y - x ≠ 0]

#blaster (solver: all) [∀ (x y : Nat), x ≤ y → x + (y - x) = y]

#blaster (solver: all) [∀ (x y : Nat), 0 < x → 0 < y → x - 1 = y - 1 → x = y]

#blaster (solver: all) [∀ (x y : Nat), x ≤ y → y - x + x = y]

#blaster (solver: all) [∀ (x y z : Nat), (x + z) - (y + z) = x - y]

#blaster (solver: all) [∀ (x y z : Nat), (z + x) - (z + y) = x - y]

#blaster (solver: all) [∀ (x y z : Nat), z ≤ y → x + y - z = x + (y - z)]

#blaster (solver: all) [∀ (x y z : Nat), y ≤ x → x - y = z → x = z + y]

#blaster (solver: all) [∀ (x y z : Nat), x = z + y → x - y = z]

#blaster (solver: all) [∀ (x y z : Nat), x - y ≤ z → x ≤ z + y]

#blaster (solver: all) [∀ (x y z : Nat), z < y → z < x → y - x < y - z]

#blaster (solver: all) [∀ (x y : Nat), x ≤ y → Nat.succ y - x = Nat.succ (y - x)]

#blaster (solver: all) [∀ (x y z : Nat), x - y - z = x - (y + z)]

#blaster (solver: all) [∀ (f : Nat → Prop) (x y : Nat), (∀ (k : Nat), y ≤ x → x = y + k → f k) → (x < y → f 0) → f (x - y)]

#blaster (solver: all) [∀ (x y : Nat), 0 < x → 0 < y → Nat.pred x = Nat.pred y → x = y]

#blaster (solver: all) [∀ (x : Nat), x ≠ 0 → Nat.pred x ≠ x]

#blaster (solver: all) [∀ (x : Nat), 0 < x → Nat.pred x < x]

#blaster (solver: all) [∀ (x y : Nat), x ≠ 0 → x < y → Nat.pred x < Nat.pred y]

#blaster (solver: all) [∀ (x y : Nat), Nat.pred x ≤ y ↔ x ≤ Nat.succ y]


/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x - y < x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x - y < y]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x - y > x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x - y > y]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x - y ≠ 0]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x < y → x - y ≠ 0]

end Test.SmtNatSub
