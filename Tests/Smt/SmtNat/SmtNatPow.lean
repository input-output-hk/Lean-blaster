import Blaster

namespace Test.SmtNatPow

/-! ## Test objectives to validate `Nat.pow` semantics with backend solver -/

/-! # Test cases to validate `Nat.pow` semantics with backend solver -/

#blaster (only-optimize: 1) [∀ (x : Nat), x^0 = 1]

#blaster (only-optimize: 1) [∀ (x y : Nat), x^y * x = x^(y + 1)]

#blaster (only-optimize: 1) [∀ (x y : Nat), x^(y + 1) * x = x^(y + 2)]

#blaster (only-optimize: 1) [∀ (x y : Nat), x^(Nat.succ y) = x^y * x]

#blaster (only-optimize: 1) [∀ (x y : Nat), x^(y + 1) = x^y * x]

#blaster (only-optimize: 1) [∀ (x y : Nat), x^y * x * x * x = x^(y + 3)]

#blaster (only-optimize: 1) [∀ (x y : Nat), x * x^y * x * x = x^(y + 3)]

#blaster [∀ (x : Nat), 0 < x → 0^x = 0]

-- These true induction laws may be proved by stronger backends; a counterexample is always wrong.
#blaster (timeout: 5) (cvc5-allow-undetermined: 1) [(∀ (x y : Nat), x ≤ y → ∀ (i : Nat), x^i ≤ y^i)]

#blaster (timeout: 5) (cvc5-allow-undetermined: 1) [∀ (x y : Nat), 0 < x → 0 < x^y]

#blaster (timeout: 5) (cvc5-allow-undetermined: 1) [∀ (x : Nat), 0 < 2^x]

#blaster (timeout: 5) (cvc5-allow-undetermined: 1) [∀ (x : Nat), 2^(x + x) = 2^x * 2^x]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x^0 ≠ 1]

#blaster (gen-cex: 0) (solve-result: 1) (cvc5-allow-undetermined: 1) [∀ (x y : Nat), x^(Nat.succ y) = x^y]

#blaster (gen-cex: 0) (solve-result: 1) (cvc5-allow-undetermined: 1) [∀ (x : Nat), 0 < x → 0^x > 0]

end Test.SmtNatPow
