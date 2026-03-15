import Blaster

-- Nat.add
example : 1 + 2 = 3 := by blaster
example : ∀ {n : Nat}, 0 + n = n := by blaster
example : ∀ {n : Nat}, 0 + (0 + n) = n := by blaster
example : ∀ {n : Nat}, 0 + (0 + (0 + n)) = n := by blaster

-- Nat.mul
example : 2 * 3 = 6 := by blaster
example : ∀ {n : Nat}, 0 * n = 0 := by blaster
example : ∀ {n : Nat}, 0 * (0 * n) = 0 := by blaster
example : ∀ {n : Nat}, 0 * (0 * (0 * n)) = 0 := by blaster
example : ∀ {n : Nat}, 1 * n = n := by blaster
example : ∀ {n : Nat}, 1 * (1 * n) = n := by blaster
example : ∀ {n : Nat}, 1 * (1 * (1 * n)) = n := by blaster

-- Combination
example : (2 * 3) + 1 = 7 := by blaster
example : ∀ {n : Nat}, 0 + ((0 * (0 * (0 + n))) + n) = n := by blaster
example : ∀ {n : Nat}, (0 + n) + 1 = n + 1 := by blaster
example : ∀ {n : Nat}, 1 + (0 + n) = n + 1 := by blaster
