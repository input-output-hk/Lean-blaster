import Lean
import Solver.Command.Tactic

namespace Test.SmtLtArith

#solve [∀ (m n x : Nat), m + x < n + x → m < n]
#solve [∀ (m n x : Int), m + x < n + x → m < n]

#solve (only-optimize: 1) [∀ (x : Nat), 10 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 100 + x]

#solve (only-optimize: 1) [∀ (x : Int), 10 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 20 + x]
#solve (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 100 + x]

#solve (only-optimize: 1) [∀ (x y : Nat), ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (y x : Nat), ¬ (y + x < x)]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), x + y < z]
#solve (gen-cex: 0) (solve-result: 1) [∀ (y x z : Nat), y + x < z]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z + y < x]
#solve (gen-cex: 0) (solve-result: 1) [∀ (y x z : Nat), y + z < x]


#solve (only-optimize: 1) [∀ (x y : Int), y ≥ 0 → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (x y : Int), 0 = y → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (x y : Int), y = 0 → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (y x : Int), y ≥ 0 → ¬ (x + y < x)]
#solve (only-optimize: 1) [∀ (y x : Int), ¬ (y < 0) → ¬ (y + x < x)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (y + x < x)]
#solve (only-optimize: 1) [∀ (y x : Int), 0 = y → ¬ (y + x < x)]
#solve (only-optimize: 1) [∀ (y x : Int), y = 0 → ¬ (y + x < x)]

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (x + y < x)]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y < 0 → ¬ (x + y < x)]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x > 0 → ¬ (x + y < x)]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x ≥ 0 → ¬ (x + y < x)]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x = 0 → ¬ (x + y < x)]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x < 0 → ¬ (x + y < x)]

#solve (only-optimize: 1) [∀ (x y : Int), y < 0 → x + y < x]
#solve (only-optimize: 1) [∀ (y x : Int), y < 0 → y + x < x]

#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x + y < x]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y > 0 → x + y < x]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y = 0 → x + y < x]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → x + y < x]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → x + y < x]
#solve (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (0 < y) → x + y < x]

#solve (only-optimize: 1) [∀ (x y : Nat), y = 0 → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 = y → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (y x : Nat), y = 0 → ¬ x < y + x]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 = y → ¬ x < y + x]
#solve (only-optimize: 1) [∀ (x y : Nat), ¬ (0 < y) → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (y x : Nat), ¬ (0 < y) → ¬ x < y + x]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y > 0 → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≥ 0 → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (y < 0) → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), ¬ (z < 0) → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), ¬ (z < 0) → ¬ x < z + y]

#solve (only-optimize: 1) [∀ (x y : Nat), 0 < y → x < x + y]
#solve (only-optimize: 1) [∀ (y x : Nat), 0 < y → x < y + x]
#solve (only-optimize: 1) [∀ (x y : Nat), y > 0 → x < x + y]
#solve (only-optimize: 1) [∀ (y x : Nat), y > 0 → x < y + x]
#solve (only-optimize: 1) [∀ (x y : Nat), 0 > y → x < x + y]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z = 0 → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z = 0 → x < z + y]


#solve (only-optimize: 1) [∀ (x y : Int), y ≤ 0 → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (x y : Int), y < 0 → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (x y : Int), y = 0 → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (x y : Int), ¬ (0 < y) → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (x y : Int), 0 ≥ y → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (y x : Int), y ≤ 0 → ¬ x < x + y]
#solve (only-optimize: 1) [∀ (y x : Int), y < 0 → ¬ x < y + x]
#solve (only-optimize: 1) [∀ (y x : Int), y = 0 → ¬ x < y + x]
#solve (only-optimize: 1) [∀ (y x : Int), ¬ (0 < y) → ¬ x < y + x]
#solve (only-optimize: 1) [∀ (y x : Int), 0 ≥ y → ¬ x < y + x]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y > 0 → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 < y  → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z  → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), ¬ (z < 0) → ¬ x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → ¬ x < y + z]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z  → ¬ x < y + z]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), ¬ (z < 0) → ¬ x < y + z]

#solve (only-optimize: 1) [∀ (x y : Int), 0 < y → x < x + y]
#solve (only-optimize: 1) [∀ (x y : Int), y > 0 → x < x + y]
#solve (only-optimize: 1) [∀ (y x : Int), 0 < y → x < y + x]
#solve (only-optimize: 1) [∀ (y x : Int), y > 0 → x < y + x]

#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y < 0 → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 0 → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 > y → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 ≥ y → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z → x < x + y]
#solve (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z → x < z + y]


end Test.SmtLtArith
