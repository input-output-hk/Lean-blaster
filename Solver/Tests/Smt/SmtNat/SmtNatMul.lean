import Lean
import Solver.Command.Syntax

/-! ## Test objectives to validate `Nat.mul` semantics with backend solver -/

/-! # Test cases to validate `Nat.mul` semantics with backend solver -/

#solve [∀ (x : Nat), (x * 0) = 0]

#solve [∀ (x : Nat), (x * 1) = x]

#solve [∀ (x y : Nat), x * Nat.succ y = x * y + x]

#solve [∀ (x y : Nat), x * y = y * x]

#solve [∀ (x y z : Nat), (x + y) * z = (x * z) + (y * z)]

#solve [∀ (x y z : Nat), z * (x + y) = (z * x) + (z * y)]

#solve [∀ (x y z : Nat), (x * y) * z = x * (y * z)]

#solve [∀ (x y z : Nat), x * (y * z) = y * (x * z)]

#solve [∀ (x : Nat), x * 2 = x + x]

#solve [∀ (x y z : Nat), x ≤ y → z * x ≤ z * y]

#solve [∀ (w x y z : Nat), w ≤ x → y ≤ z → w * y ≤ x * z]

#solve [∀ (x y z : Nat), x < y → z > 0 → x * z < y * z]

#solve [∀ (x y : Nat), x > 0 → y > 0 -> x * y > 0]

#solve [∀ (x y z : Nat), 0 < x → x * y = x * z → y = z]

def isInjective (f : Nat → Nat) : Prop :=
  ∀ (x y : Nat), f x = f y → x = y

def isSurjective (f : Nat → Nat) : Prop :=
  ∀ (y : Nat), ∃ (x : Nat), f x = y

def isBijective (f : Nat → Nat) : Prop :=
  isInjective f ∧ isSurjective f

def square (x : Nat) : Nat := x * x

#solve [isInjective square]

/-! # Test cases to ensure that counterexample are properly detected -/

#solve [isSurjective square]
#solve [isBijective square]
