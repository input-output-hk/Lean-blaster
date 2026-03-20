import Blaster

/-! ## Tests that `blaster` closes goals with valid proof certificates (no sorry). -/

-- Nat.zero_add: 0 + n → n
example : ∀ {n : Nat}, 0 + n = n := by blaster

-- Nat.sub_self: n - n → 0
example : ∀ {n : Nat}, n - n = 0 := by blaster

-- Nat.zero_sub: 0 - n → 0
example : ∀ {n : Nat}, 0 - n = 0 := by blaster

-- Nat.sub_zero: n - 0 → n
example : ∀ {n : Nat}, n - 0 = n := by blaster

-- Nat.zero_mul: 0 * n → 0
example : ∀ {n : Nat}, 0 * n = 0 := by blaster

-- Nat.one_mul: 1 * n → n
example : ∀ {n : Nat}, 1 * n = n := by blaster

-- Constant evaluation
example : 1 + 2 = 3 := by blaster
example : 2 * 3 = 6 := by blaster
example : (2 * 3) + 1 = 7 := by blaster

-- Constant propagation
example : ∀ (x : Nat), 10 + (20 + x) = 30 + x := by blaster
example : ∀ (x : Nat), 120 - (40 + x) = 80 - x := by blaster
example : ∀ (x : Nat), 120 - (x + 40) = 80 - x := by blaster

-- Nat.add commutativity
example : ∀ (m n : Nat), m + n = n + m := by blaster
example : ∀ (n : Nat), n + 1 = 1 + n := by blaster

-- Nat.mul commutativity
example : ∀ (m n : Nat), m * n = n * m := by blaster
example : ∀ (n : Nat), 2 * n = n * 2 := by blaster

-- Mixed rewrites
example : ∀ {n : Nat}, 0 + (0 + n) = n := by blaster
example : ∀ {n : Nat}, 0 * (0 * n) = 0 := by blaster
example : ∀ {n : Nat}, 1 * (1 * n) = n := by blaster

example : ∀ {n : Nat}, 0 + ((0 * (0 * (0 + n))) + n) = n := by blaster
example : ∀ {n : Nat}, (1 * ((0 * n) + n)) - 0 = n := by blaster
example : ∀ {n : Nat}, (0 + n) + 1 = n + 1 := by blaster
example : ∀ {n : Nat}, 1 + (0 + n) = n + 1 := by blaster

-- Mixed rewrite + commutativity
example : ∀ (m n : Nat), 0 + (m + n) = n + m := by blaster
example : ∀ (m n : Nat), (m + n) + 0 = n + m := by blaster
example : ∀ (m n : Nat), 1 * (m + n) = n + m := by blaster
example : ∀ (m n : Nat), (m + n) - 0 = n + m := by blaster

-- Multiple arguments rewrites
example : ∀ {x y : Nat}, (x + 0) + (y - 0) = x + y := by blaster
example : ∀ {x y : Nat}, (0 + x) + (0 + y)  = x + y := by blaster
example : ∀ {x y : Nat}, (x - 0) + (y + 0) = y + x := by blaster
example : ∀ {x y : Nat}, (0 + x) + (0 + y)  = y + x := by blaster

-- Rewrites inside if-then-else
example : ∀ (c : Bool) (x y : Nat),
  (if c then x + 0 else y) = (if c then 0 + x else 0 + y) := by blaster

-- Rewrites inside match
example : ∀ (n : Nat),
  (match n with | 0 => 0 + 1 | k + 1 => k + 0) =
  (match n with | 0 => 1 | k + 1 => k) := by blaster

-- TODO: Multiple commutativity on different sub-expressions
example : ∀ {m n p q : Nat}, (m + n) + (p + q) = (q + p) + (n + m) := by blaster

-- TODO: Commutativity on both sides of different operators
example : ∀ {a b c d : Nat}, (a * b) + (c * d) = (d * c) + (b * a) := by blaster
