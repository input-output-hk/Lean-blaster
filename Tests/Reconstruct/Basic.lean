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
-- eliminated binders, one of them a `Decidable` instance
example : (∀ (a : Prop) [Decidable a], false = decide a) = ∀ (a : Prop), ¬ a := by blaster
example : (∀ (a : Prop) (_n : Nat), ¬ a) = ∀ (a : Prop), ¬ a := by blaster

-- Optimized side is a top-level implication
example : (∀ (a b : Prop), a ∨ (b → a)) = (∀ (a b : Prop), b → a) := by blaster

-- Propositional equality with True
example : (∀ (x : Nat), 0 * x = 0) = True := by blaster
example : (∀ (m n : Nat), m + n = n + m) = True := by blaster
example : (0 + 0 = 0) = True := by blaster

-- Propositional equality whose forall has a function-typed binder
example : (∀ (f : Nat → Nat → Nat) (x y : Nat), f x y + x = x + f x y) =
          (∀ (f : Nat → Nat → Nat) (x y : Nat), x + f x y = x + f x y) := by blaster

-- Hypothesis-dependent rewrites
example : ∀ (n : Nat), 0 < n → n / n = 1 := by blaster
example : ∀ (x y : Nat), 0 < y → (x * y) / y = x := by blaster
example : ∀ (x y : Nat), 0 < x → (x * y) / x = y := by blaster

-- Hypotheses not in optimizer normal form (rewritten on replay)
example : ∀ (a b : Bool), a = true → (a && b) = b := by blaster
example : ∀ (a b : Bool), ¬ (false = a) → (a && b) = b := by blaster
example : ∀ (a b : Bool), a → (a && b) = b := by blaster
example : ∀ (a b : Bool), a = true → b = true → (a && b) = true := by blaster
example : ∀ (a : Bool), a = true → ∀ (b : Bool), (a && b) = b := by blaster
example : ∀ (n : Nat), n ≠ 0 → n / n = 1 := by blaster
example : ∀ (n : Nat), n ≠ 0 → n / n + n / n = 2 := by blaster
example : ∀ (m n : Nat), m ≤ n → ¬ n < m := by blaster
example : ∀ (x y : Int), x ≠ 0 → (x * y) / x = y := by blaster
example : ∀ (x y : Int), x ≤ y → ¬ y < x := by blaster
example : ∀ (x y : Int), x ≥ y → ¬ x < y := by blaster
example : ∀ (a b : Prop), (True ∧ a) → (a ∧ b) = b := by blaster
example : ∀ (p q : Prop), ¬¬p → (p ∧ q) = q := by blaster

-- Steps built from a hypothesis are not replayed on it
example : ∀ (a c : Prop), (a ∧ (a ∨ c)) → (a ∨ c) := by blaster
example : ∀ (a b c d : Prop), (a ∧ (b ∨ c)) → b → (a ∧ d) = d ∧ (b ∨ c) := by blaster
example : ∀ (x y : Nat), (x + 0 < y ∧ y < 10) → (x < y ∧ y < 10) = (y < 10) := by blaster

-- Int literal folds and normalizations
example : ∀ (x : Int), (x * 6) / 3 = x * 2 := by blaster
example : ∀ (n : Int), ¬ ((4 * n) / 6 = (2 * n) / 3) ∨ n = n := by blaster
example : ∀ (n : Nat), Int.toNat (-(Int.ofNat n)) = 0 := by blaster
example : ∀ (n : Nat), Int.negSucc n = -(Int.ofNat (1 + n)) := by blaster
example : ∀ (n : Nat), Int.toNat (Int.ofNat n) - n = 0 := by blaster
example : ∀ (x y : Int), ((3 + x < 5) = (x < 2)) ∧ y - y = 0 := by blaster
example : ∀ (x y : Int), Int.le x y = (x ≤ y) := by blaster

-- Negated hypotheses
example : ∀ (a b : Prop), a → ((¬ a ∨ b) = b) := by blaster

-- `≠` in the goal
example : ∀ (x y : Int), x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by blaster
example : ∀ (a : Nat), a + 1 ≠ 0 := by blaster

-- Constructor equalities whose operands still simplify
example : ∀ (x y : Nat), ([x + 0, y] = [x, y, y]) = False := by blaster
example : ∀ (a b c : Nat), ([b + a, c] = [a + c, c, b]) = False := by blaster

-- `Nat.le` normalization
example : ∀ (x y : Nat), Nat.le x y = (x ≤ y) := by blaster
example : ∀ (x y : Nat), Nat.le x y → ¬ (y < x) := by blaster

-- Binders below a leading `let` or `have`
example : let x := (2 : Int); ∀ (y : Int), x + y = y + 2 := by blaster
example : let x := (2 : Nat); ∀ (y : Nat), x + y = y + 2 := by blaster
example : let b := true; ∀ (a : Bool), (a && b) = a := by blaster
example : let p := True; ∀ (a : Prop), (a ∧ p) = a := by blaster
example : (let x := (2 : Int); ∀ (y : Int), x + y = y + 2) = True := by blaster
example : let x := (2 : Int); (∀ (y : Int), x + y = y + 2) = True := by blaster
example : have x := (2 : Int); ∀ (y : Int), x + y = y + 2 := by blaster

-- Nested De Morgan, or next to a hypothesis it must leave alone
example : ∀ (a b c : Prop), (¬ (¬ (¬ a ∧ ¬ b) ∧ ¬ c)) = (¬ (¬ c ∧ (a ∨ b))) := by blaster
example : ∀ (a b c : Prop), (¬ (¬ (¬ a ∨ ¬ b) ∨ ¬ c)) = (¬ (¬ c ∨ (a ∧ b))) := by blaster
example : ∀ (a b c : Prop), ¬ (¬ a ∧ ¬ b) → (¬ (¬ c ∧ ¬ c)) → (a ∨ b) ∧ c := by blaster

-- Core function, cast and `Int.ofNat` literal spellings
example : ∀ (n : Nat), Int.toNat (-(n : Int)) = 0 := by blaster
example : ∀ (n : Nat), Int.toNat (n : Int) - n = 0 := by blaster
example : ∀ (x y z : Int), (Int.ediv x 2 + y = y + x / 2) ∧ z - z = 0 := by blaster
example : ∀ (x y z : Int), (x % 3 + y = y + Int.emod x 3) ∧ z - z = 0 := by blaster
example : ∀ (x : Int), x / 2 ≠ 0 → Int.ediv (x / 2) (x / 2) = 1 := by blaster
example : ∀ (x y : Int), Int.emod (x / 2) 3 + y = y + Int.emod (x / 2) 3 := by blaster
example : ∀ (n : Int), ¬ (Int.ediv (4 * n) 6 = Int.ediv (2 * n) 3) ∨ n = n := by blaster
example : ∀ (x : Int), Int.ediv (x * 6) 3 = 2 * x := by blaster
example : ∀ (x y : Int), ((Int.ofNat 7 * 2 + x) = (x + 14)) ∧ y - y = 0 := by blaster

-- Core `Nat.add` spelling
example : ∀ (x : Nat), Nat.add (Nat.succ x) 1 = x + 2 := by blaster

-- A conclusion found in the hypotheses
example : ∀ (x : Nat), x > 0 → x ≠ 0 := by blaster
example : ∀ (x y : Int), x > y → x ≠ y := by blaster
example : ∀ (x y : Int), x = y → ¬ (x < y) := by blaster
example : ∀ (x : Nat), x ≠ 0 → 0 < x := by blaster
example : ∀ (a b : Prop), a ∧ b → b := by blaster
example : ∀ (x : Nat), (x > 0 → x ≠ 0) = True := by blaster
example : ∀ (a b : Prop), (a ∧ b → b) ∧ (a ∧ b → a) := by blaster
example : ∀ (a b c : Prop), a ∧ b → ((c → b) ∧ (c → a)) := by blaster

-- `(p → q) ∧ (¬ p → q)` with `¬ p` in normal form
example : ∀ (x : Bool) (q : Prop), (((true = x) → q) ∧ ((false = x) → q)) = q := by blaster
example : ∀ (x : Bool) (q : Prop), (((false = x) → q) ∧ ((true = x) → q)) = q := by blaster

-- Steps whose hypothesis proof the replay cannot type are skipped
example : ∀ (a b : Bool) (f : ¬ a → Bool → Bool) (h : ¬ a), f h b = true → f h b = true := by blaster

-- Steps whose hypothesis proof types only after evaluation are kept
example : ∀ (y : Nat) (c : Prop), (List.replicate 300 0).length < y → ((300 < y) ∧ c) = c := by blaster
