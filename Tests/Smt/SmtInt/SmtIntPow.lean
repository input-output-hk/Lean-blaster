import Blaster

namespace Test.SmtIntPow

/-! ## Test objectives to validate `Int.pow` semantics with backend solver -/

/-! # Test cases to validate `Int.pow` semantics with backend solver -/

#blaster (only-optimize: 1) [∀ (x : Int), x^0 = 1]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^y * x = x^(y + 1)]
#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x * x^y = x^(y + 1)]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^(y + 1) * x = x^(y + 2)]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^(Nat.succ y) = x^y * x]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), Int.pow x (y + 1) * x = x^(y + 2)]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), Int.pow x (Nat.succ y) = x^y * x]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^(y + 1) = x^y * x]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^(y + 1) = Int.pow x y * x]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x^y * x * x * x = x^(y + 3)]

#blaster (only-optimize: 1) [∀ (x : Int) (y : Nat), x * x^y * x * x = x^(y + 3)]

#blaster [∀ (x : Nat), 0 < x → (0 : Int)^x = 0]

-- NOTE: remove solve option when induction schema implemented
#blaster (timeout: 5) (solve-result: 2) [(∀ (x y : Int), 0 ≤ x → x ≤ y → ∀ (i : Nat), x^i ≤ y^i)]

-- NOTE: remove solve option when induction schema implemented
#blaster (timeout: 5) (solve-result: 2) [∀ (x : Int) (y : Nat), 0 ≤ x → 0 ≤ x^y]

-- NOTE: remove solve option when induction schema implemented
#blaster (timeout: 5) (solve-result: 2) [∀ (x : Nat), 0 < (2 : Int)^x]

-- NOTE: remove solve option when induction schema implemented
#blaster (timeout: 5) (solve-result: 2) [∀ (x : Nat), (2 : Int)^(x + x) = (2 : Int)^x * (2 : Int)^x]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x^0 ≠ 1]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int) (y : Nat), x^(Nat.succ y) = x^y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), 0 < x → (0 : Int)^x > 0]

end Test.SmtIntPow
