import Lean
import Solver.Command.Syntax


namespace Tests.SmtNatSub

/-! ## Test objectives to validate `Nat.sub` semantics with backend solver -/

/-! # Test cases to validate `Nat.sub` semantics with backend solver -/

#solve [∀ (x : Nat), 0 - x = 0]

#solve [∀ (x y : Nat), x - (x + y) = 0]

#solve [∀ (x y : Nat), x ≤ y → x - y = 0]

#solve [∀ (x y : Nat), x > y → x - y > 0]

#solve [∀ (x y : Nat), (x + y) - x = y]

#solve [∀ (x y : Nat), (x + y) - y = x]

#solve [∀ (x y : Nat), x - y ≤ Nat.succ x - y]

#solve [∀ (x y : Nat), y < x → 0 < x - y]

#solve [∀ (x y : Nat), y < x → x - (y + 1) < x - y]

#solve [∀ (x y : Nat), x < y → y - x ≠ 0]

#solve [∀ (x y : Nat), x ≤ y → x + (y - x) = y]

#solve [∀ (x y : Nat), 0 < x → 0 < y → x - 1 = y - 1 → x = y]

#solve [∀ (x y : Nat), x ≤ y → y - x + x = y]

#solve [∀ (x y z : Nat), (x + z) - (y + z) = x - y]

#solve [∀ (x y z : Nat), (z + x) - (z + y) = x - y]

#solve [∀ (x y z : Nat), z ≤ y → x + y - z = x + (y - z)]

#solve [∀ (x y z : Nat), y ≤ x → x - y = z → x = z + y]

#solve [∀ (x y z : Nat), x = z + y → x - y = z]

#solve [∀ (x y z : Nat), x - y ≤ z → x ≤ z + y]

#solve [∀ (x y z : Nat), z < y → z < x → y - x < y - z]

#solve [∀ (x y : Nat), x ≤ y → Nat.succ y - x = Nat.succ (y - x)]

#solve [∀ (x y z : Nat), x - y - z = x - (y + z)]

#solve [∀ (f : Nat → Prop) (x y : Nat), (∀ (k : Nat), y ≤ x → x = y + k → f k) → (x < y → f 0) → f (x - y)]

#solve [∀ (x y : Nat), 0 < x → 0 < y → Nat.pred x = Nat.pred y → x = y]

#solve [∀ (x : Nat), x ≠ 0 → Nat.pred x ≠ x]

#solve [∀ (x : Nat), 0 < x → Nat.pred x < x]

#solve [∀ (x y : Nat), x ≠ 0 → x < y → Nat.pred x < Nat.pred y]

#solve [∀ (x y : Nat), Nat.pred x ≤ y ↔ x ≤ Nat.succ y]


/-! # Test cases to ensure that counterexample are properly detected -/

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x - y < x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x - y < y]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x - y > x]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x - y > y]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x - y ≠ 0]

#solve (gen-cex: 0) (falsified-result: 1) [∀ (x y : Nat), x < y → x - y ≠ 0]

end Tests.SmtNatSub
