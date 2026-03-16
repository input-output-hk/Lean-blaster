import Blaster

-- Nat.add
example : 1 + 2 = 3 := by blaster
example : ∀ {n : Nat}, 0 + n = n := by blaster
example : ∀ {n : Nat}, 0 + (0 + n) = n := by blaster
example : ∀ {n : Nat}, 0 + (0 + (0 + n)) = n := by blaster

-- Nat.sub
example : ∀ {n : Nat}, n - n = 0 := by blaster
example : ∀ {n : Nat}, 0 - n = 0 := by blaster

-- Nat.mul
example : 2 * 3 = 6 := by blaster
example : ∀ {n : Nat}, 0 * n = 0 := by blaster
example : ∀ {n : Nat}, 0 * (0 * n) = 0 := by blaster
example : ∀ {n : Nat}, 0 * (0 * (0 * n)) = 0 := by blaster
example : ∀ {n : Nat}, 1 * n = n := by blaster
example : ∀ {n : Nat}, 1 * (1 * n) = n := by blaster
example : ∀ {n : Nat}, 1 * (1 * (1 * n)) = n := by blaster

-- N1 + (N2 + n) ==> (N1 "+" N2) + n
example : ∀ (x : Nat), 10 + (20 + x) = 30 + x := by blaster

-- Combination
example : (2 * 3) + 1 = 7 := by blaster
example : ∀ {n : Nat}, 0 + ((0 * (0 * (0 + n))) + n) = n := by blaster
example : ∀ {n : Nat}, (1 * ((0 * n) + n)) - 0 = n := by blaster
example : ∀ {n : Nat}, (0 + n) + 1 = n + 1 := by blaster
example : ∀ {n : Nat}, 1 + (0 + n) = n + 1 := by blaster
