import Lean
import Solver.Command.Tactic

namespace Test.SmtEqArith

#solve (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), 10 + x = x]
#solve (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x = x + 100]

#solve (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Int), 1120 + x = x]
#solve (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = x + 200]

#solve [∀ (n m x: Nat), n = m → m = n + x → 0 = x]
#solve [∀ (n m x: Nat), m < n → m = n + x → 0 = x]
#solve [∀ (n m x: Nat), m > n → m = n + x → m - n = x]

#solve (only-optimize: 1) [∀ (x: Nat), 10 = 10 + x → 0 = x]
#solve (only-optimize: 1) [∀ (x: Nat), 20 + x = 10 → 0 = x]
#solve (only-optimize: 1) [∀ (x: Nat), x + 35 = 100 → 65 = x]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 < x → 0 < y → ¬ ((x * y) + 35 = 35)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 < x → 0 ≠ y → ¬ ((x * y) + 35 = 35)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 ≠ x → 0 ≠ y → ¬ ((x * y) + 35 = 35)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 ≠ x → 0 < y → ¬ ((x * y) + 35 = 35)]
#solve (only-optimize: 1) [∀ (x: Nat), 0 ≠ 10 + x]
#solve (only-optimize: 1) [∀ (x: Nat), 5 ≠ 10 + x]
#solve (only-optimize: 1) [∀ (x: Nat), 11 = 10 + x ↔ 1 = x]
#solve (only-optimize: 1) [∀ (x: Nat), 10 = 10 + x ↔ 0 = x]

#solve [∀ (n m x: Int), m = n + x → m - n = x]
#solve (only-optimize: 1) [∀ (x: Int), 10 = 30 + x → -20 = x]
#solve (only-optimize: 1) [∀ (x: Int), 100 = 30 + x → 70 = x]
#solve (only-optimize: 1) [∀ (x: Int), x + 100 = 100 → 0 = x]
#solve (only-optimize: 1) [∀ (x: Int), 0 < x → ¬ (x + 100 = 100) ]
#solve (only-optimize: 1) [∀ (x: Int), x < 0 → ¬ (x + 100 = 100) ]
#solve (only-optimize: 1) [∀ (x: Int), x ≠ 0 → ¬ (x + 100 = 100) ]

#solve [∀ (n m x: Nat), m ≠ n → m + x ≠ n + x]
#solve [∀ (n m x: Int), m ≠ n → m + x ≠ n + x]

#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), 10 + x = x + 20]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), x + 100 = x + 20]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), x + 100 = 20 + x]

#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), -10 + x = x + 20]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), x + 100 = x + 20]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), x + 100 = -20 + x]

#solve [∀ (m n x y : Nat), m ≤ n → m + x = n + y → x = (n - m) + y]
#solve [∀ (m n x y : Nat), m > n → m + x = n + y → (m - n) + x = y]
#solve [∀ (m n x y : Int), m ≤ n → m + x = n + y → x = (n - m) + y]
#solve [∀ (m n x y : Int), m > n → m + x = n + y → (m - n) + x = y]

#solve (only-optimize: 1) [∀ (x y : Nat), 10 + x = 20 + y → x = 10 + y]
#solve (only-optimize: 1) [∀ (x y : Nat), 100 + x = 20 + y → 80 + x = y]
#solve (only-optimize: 1) [∀ (x y : Nat), 100 + x = 100 + y → x = y]

#solve (only-optimize: 1) [∀ (x y : Int), 10 + x = 20 + y → x = 10 + y]
#solve (only-optimize: 1) [∀ (x y : Int), 100 + x = 20 + y → 80 + x = y]
#solve (only-optimize: 1) [∀ (x y : Int), 100 + x = 100 + y → x = y]

#solve (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x + y = x)]

#solve (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 ≠ y → ¬ (y + x = x)]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 < y → ¬ (y + x = x)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 ≠ y → ¬ (x = y + x)]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 < y → ¬ (x = y + x)]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (y < 0) → ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≥ 0 → ¬ (x + y = x)]

#solve (only-optimize: 1) [∀ (x y : Int), 0 ≠ y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 > y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 ≠ y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (x + y = x)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 > y → ¬ (x + y = x)]

#solve (only-optimize: 1) [∀ (x y : Int), 0 ≠ y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 > y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 ≠ y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (x = x + y)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 > y → ¬ (x = x + y)]


#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y = 0 → ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → ¬ (x + y = x)]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 0 → ¬ (x + y = x)]


end Test.SmtEqArith
