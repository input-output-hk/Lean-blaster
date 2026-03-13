import Blaster

-- Nat.add
example : ∀ {x : Nat}, 0 + x = x := by blaster
example : ∀ {x : Nat}, 0 + (0 + x) = x := by blaster
example : ∀ {x : Nat}, 0 + (0 + (0 + x)) = x := by blaster

-- Nat.mul
example : ∀ {x : Nat}, 0 * x = 0 := by blaster
example : ∀ {x : Nat}, 0 * (0 * x) = 0 := by blaster
example : ∀ {x : Nat}, 0 * (0 * (0 * x)) = 0 := by blaster

-- Combination
example : ∀ {x : Nat}, (0 * (0 * (0 + x))) + x = x := by blaster
