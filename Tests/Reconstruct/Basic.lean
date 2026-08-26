import Blaster

/-! ## Tests that `blaster` closes goals with valid proof certificates (no sorry). -/

-- Eliminative rewrites
example : ∀ {n : Nat}, 0 + n = n := by blaster
example : ∀ {n : Nat}, n - n = 0 := by blaster
example : ∀ {n : Nat}, 0 - n = 0 := by blaster
example : ∀ {n : Nat}, n - 0 = n := by blaster
example : ∀ {n : Nat}, 0 * n = 0 := by blaster
example : ∀ {n : Nat}, 1 * n = n := by blaster
example : ∀ (n : Nat), n / 0 = 0 := by blaster
example : ∀ (n : Nat), 0 / n = 0 := by blaster
example : ∀ (n : Nat), n / 1 = n := by blaster
example : ∀ (n : Nat), n % 0 = n := by blaster
example : ∀ (n : Nat), 0 % n = 0 := by blaster
example : ∀ (n : Nat), n % 1 = 0 := by blaster
example : ∀ (x : Nat), x % x = 0 := by blaster
example : ∀ (x y : Nat), (x * y) % y = 0 := by blaster
example : ∀ (x y : Nat), (y * x) % y = 0 := by blaster

-- Constant evaluation
example : 1 + 2 = 3 := by blaster
example : 2 * 3 = 6 := by blaster
example : (2 * 3) + 1 = 7 := by blaster
example : 18 / 3 = 6 := by blaster

-- Constant propagation
example : ∀ (x : Nat), 10 + (20 + x) = 30 + x := by blaster
example : ∀ (x : Nat), 120 - (40 + x) = 80 - x := by blaster
example : ∀ (x : Nat), (x / 10) / 20 = x / 200 := by blaster
example : ∀ (x : Nat), (10 * x) / 5 = 2 * x := by blaster
example : ∀ (x : Nat), (124 * x) % 4 = 0 := by blaster

-- Constant-level rewrites (Nat.succ / Nat.pred)
example : ∀ (n : Nat), Nat.succ n = 1 + n := by blaster
example : ∀ (n : Nat), Nat.pred n = n - 1 := by blaster
example : ∀ (n : Nat), Nat.succ (Nat.succ n) = 1 + (1 + n) := by blaster

-- Commutativity
example : ∀ (m n : Nat), m + n = n + m := by blaster
example : ∀ (m n : Nat), m * n = n * m := by blaster

-- Mixed rewrites (chained eliminatives)
example : ∀ {n : Nat}, 0 + (0 + n) = n := by blaster
example : ∀ {n : Nat}, 1 * (1 * n) = n := by blaster
example : ∀ {n : Nat}, 0 + ((0 * (0 * (0 + n))) + n) = n := by blaster
example : ∀ {n : Nat}, (1 * ((0 * n) + n)) - 0 = n := by blaster

-- Mixed rewrites + commutativity
example : ∀ (m n : Nat), 0 + (m + n) = n + m := by blaster
example : ∀ (m n : Nat), 1 * (m + n) = n + m := by blaster
example : ∀ (x : Nat), 0 + (x + 40) - (40 + x) = 0 := by blaster

-- Multiple arguments
example : ∀ {x y : Nat}, (x + 0) + (y - 0) = x + y := by blaster
example : ∀ {x y : Nat}, (0 + x) + (0 + y) = y + x := by blaster

-- Multiple commutativity on different sub-expressions
example : ∀ {m n p q : Nat}, (m + n) + (p + q) = (q + p) + (n + m) := by blaster
example : ∀ {a b c d : Nat}, (a * b) + (c * d) = (d * c) + (b * a) := by blaster

-- Rewrites inside if-then-else
example : ∀ (c : Bool) (x y : Nat),
  (if c then x + 0 else y) =
  (if c then 0 + x else 0 + y) := by blaster

-- Rewrites inside match
example : ∀ (n : Nat),
  (match n with | 0 => 0 + 1 | k + 1 => k + 0) =
  (match n with | 0 => 1 | k + 1 => k) := by blaster

-- Propositional equality: (∀ xs, P xs) = (∀ xs, Q xs)
example : (∀ (n : Nat), 0 + n = n) = (∀ (n : Nat), n = n) := by blaster
example : (∀ (m n : Nat), m + n = n + m) = (∀ (m n : Nat), n + m = n + m) := by blaster

-- Optimized side is a top-level implication
example : (∀ (a b : Prop), a ∨ (b → a)) = (∀ (a b : Prop), b → a) := by blaster

-- Propositional equality with True
example : (∀ (x : Nat), 0 * x = 0) = True := by blaster
example : (∀ (m n : Nat), m + n = n + m) = True := by blaster
example : (0 + 0 = 0) = True := by blaster

-- Hypothesis-dependent rewrites
example : ∀ (n : Nat), 0 < n → n / n = 1 := by blaster
example : ∀ (x y : Nat), 0 < y → (x * y) / y = x := by blaster
example : ∀ (x y : Nat), 0 < x → (x * y) / x = y := by blaster
