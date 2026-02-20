import Blaster

namespace Test.SmtNatMul

/-! ## Test objectives to validate `Nat.mul` semantics with backend solver -/

/-! # Test cases to validate `Nat.mul` semantics with backend solver -/

#blaster [∀ (x : Nat), (x * 0) = 0]

#blaster [∀ (x : Nat), (x * 1) = x]

#blaster [∀ (x y : Nat), x * Nat.succ y = x * y + x]

#blaster [∀ (x y : Nat), x * y = y * x]

#blaster [∀ (x y z : Nat), (x + y) * z = (x * z) + (y * z)]

#blaster [∀ (x y z : Nat), z * (x + y) = (z * x) + (z * y)]

#blaster [∀ (x y z : Nat), (x * y) * z = x * (y * z)]

#blaster [∀ (x y z : Nat), x * (y * z) = y * (x * z)]

#blaster [∀ (x : Nat), x * 2 = x + x]

#blaster [∀ (x y z : Nat), x ≤ y → z * x ≤ z * y]

#blaster [∀ (w x y z : Nat), w ≤ x → y ≤ z → w * y ≤ x * z]

#blaster [∀ (x y z : Nat), x < y → z > 0 → x * z < y * z]

#blaster [∀ (x y : Nat), x > 0 → y > 0 -> x * y > 0]

#blaster [∀ (x y z : Nat), 0 < x → x * y = x * z → y = z]

def isInjective (f : Nat → Nat) : Prop :=
  ∀ (x y : Nat), f x = f y → x = y

def isSurjective (f : Nat → Nat) : Prop :=
  ∀ (y : Nat), ∃ (x : Nat), f x = y

def isBijective (f : Nat → Nat) : Prop :=
  isInjective f ∧ isSurjective f

def square (x : Nat) : Nat := x * x

#blaster [isInjective square]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1) [isSurjective square]

#blaster (gen-cex: 0) (solve-result: 1) [isBijective square]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y ≠ y * x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y > x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y > y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x = 0 → x * y > 0]

-- x * y = x * z | y * x = x * z | x * y = z * x | y * x = z * x ==> y = z (if Type(x) ∈ [Nat, Int] ∧ nonZeroInHyps x]

#blaster (only-optimize: 1) [∀ (x y z : Nat), x ≠ 0 → x * y = x * z → y = z]
-- TODO: this should be optimized as well?
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat), 2 * x = y * 2 → x = y]

end Test.SmtNatMul
