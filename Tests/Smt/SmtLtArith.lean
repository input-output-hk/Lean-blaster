import Lean
import Blaster

namespace Test.SmtLtArith

#blaster [∀ (m n x : Nat), m + x < n + x → m < n]
#blaster [∀ (m n x : Int), m + x < n + x → m < n]

#blaster (only-optimize: 1) [∀ (x : Nat), 10 + x < 20 + x]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 20 + x]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Nat), 100 + x < 100 + x]

#blaster (only-optimize: 1) [∀ (x : Int), 10 + x < 20 + x]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 20 + x]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x : Int), 100 + x < 100 + x]

#blaster (only-optimize: 1) [∀ (x y : Nat), ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Nat), ¬ (y + x < x)]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), x + y < z]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (y x z : Nat), y + x < z]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z + y < x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (y x z : Nat), y + z < x]


#blaster (only-optimize: 1) [∀ (x y : Int), y ≥ 0 → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 = y → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), y = 0 → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), y ≥ 0 → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), ¬ (y < 0) → ¬ (y + x < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (y + x < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 = y → ¬ (y + x < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), y = 0 → ¬ (y + x < x)]

#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (x + y < x)]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y < 0 → ¬ (x + y < x)]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x > 0 → ¬ (x + y < x)]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x ≥ 0 → ¬ (x + y < x)]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x = 0 → ¬ (x + y < x)]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x < 0 → ¬ (x + y < x)]

#blaster (only-optimize: 1) [∀ (x y : Int), y < 0 → x + y < x]
#blaster (only-optimize: 1) [∀ (y x : Int), y < 0 → y + x < x]

#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), x + y < x]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y > 0 → x + y < x]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y = 0 → x + y < x]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → x + y < x]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → x + y < x]
#blaster (gen-cex:0) (solve-result: 1) [∀ (x y : Int), ¬ (0 < y) → x + y < x]

#blaster (only-optimize: 1) [∀ (x y : Nat), y = 0 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 = y → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), y = 0 → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 = y → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Nat), ¬ (0 < y) → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), ¬ (0 < y) → ¬ x < y + x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y > 0 → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≥ 0 → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (y < 0) → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), ¬ (z < 0) → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), ¬ (z < 0) → ¬ x < z + y]

#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 < y → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Nat), y > 0 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), y > 0 → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 > y → x < x + y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z = 0 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z = 0 → x < z + y]


#blaster (only-optimize: 1) [∀ (x y : Int), y ≤ 0 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), y < 0 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), y = 0 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), ¬ (0 < y) → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 ≥ y → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), y ≤ 0 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), y < 0 → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (y x : Int), y = 0 → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (y x : Int), ¬ (0 < y) → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 ≥ y → ¬ x < y + x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y > 0 → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 < y  → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z  → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), ¬ (z < 0) → ¬ x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → ¬ x < y + z]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z  → ¬ x < y + z]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), ¬ (z < 0) → ¬ x < y + z]

#blaster (only-optimize: 1) [∀ (x y : Int), 0 < y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), y > 0 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 < y → x < y + x]
#blaster (only-optimize: 1) [∀ (y x : Int), y > 0 → x < y + x]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y < 0 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 0 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 > y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 ≥ y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 0 < z → x < z + y]

#blaster (only-optimize: 1) [∀ (x y : Int), Int.neg x < Int.neg y ↔ y < x]
#blaster (only-optimize: 1) [∀ (x y : Nat), Int.ofNat x < Int.ofNat y ↔ x < y]

#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < x → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 0 < y then 0 < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 0 < x then 0 < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 0 = x then p else 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 0 = y then p else 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 < z then if 0 < y then 0 < x + y else p else p]
#blaster (only-optimize: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 < z then if 0 < x then 0 < x + y else p else p]
#blaster (only-optimize: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 = x then p else if 0 < z then 0 < x + y else p]
#blaster (only-optimize: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 = y then p else if 0 < z then 0 < x + y else p]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), 0 < z → 0 < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 < z then 0 < x + y else p]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat) (p : Prop), p → if 0 = z then p else 0 < x + y]


/-! Positive / negative operands derived indirectly from other hypotheses (e.g. `10 < y`, `y < -100`, `7 = y`). -/

#blaster (only-optimize: 1) [∀ (x y : Nat), 10 < y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), x < y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 7 = y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), y = 7 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), 10 < y → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Nat), 10 < y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y z : Nat), z < x → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 3 = x → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 10 < y then 0 < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 5 = y then x < x + y else p]
#blaster (only-optimize: 1) [∀ (x y z : Nat) (p : Prop), p → if z < x then y < y + x else p]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y < 10 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), 10 < z → x < x + y]

#blaster (only-optimize: 1) [∀ (x y : Int), 10 < y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 7 = y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), y = 7 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), 10 < y → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Int), y < -100 → x + y < x]
#blaster (only-optimize: 1) [∀ (x y : Int), -7 = y → x + y < x]
#blaster (only-optimize: 1) [∀ (x y : Int), y = -7 → x + y < x]
#blaster (only-optimize: 1) [∀ (y x : Int), y < -100 → y + x < x]
#blaster (only-optimize: 1) [∀ (x y : Int), 7 = y → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), y = -7 → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if 10 < y then x < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if y < -100 then x + y < x else p]

#blaster (only-optimize: 1) [∀ (x : Int), 10 < x → 0 ≤ x]
#blaster (only-optimize: 1) [∀ (x : Int), 10 < x → ¬ (x < 0)]
#blaster (only-optimize: 1) [∀ (x : Int), x < -100 → x ≤ 0]
#blaster (only-optimize: 1) [∀ (x : Int), x < -100 → ¬ (0 < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 < y → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 10 < y → ¬ (y + x < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), y < -100 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), y < -100 → ¬ x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 < x → 20 < y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 < x → 20 < y → 0 ≤ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 < x → 0 ≤ y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), x < -1 → y < -100 → x + y ≤ 0]
#blaster (only-optimize: 1) [∀ (x y : Int), x < -1 → y < -100 → ¬ 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (y < -100) with
  | true  => ¬ x < x + y
  | false => p
]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (10 < x), decide (20 < y) with
  | true, true => 0 < x + y
  | _   , _    => p
]

/-! Positive / negative operands derived from non-strict bounds: `10 ≤ y` is normalized to
    `¬ (y < 10)` and `y ≤ -100` to `¬ (-100 < y)`, from which `0 < y` / `y < 0` (and the
    corresponding `¬ (0 = y)`, `¬ (y < 0)` / `¬ (0 < y)`) are derived (see `addNotPropFacts`). -/

#blaster (only-optimize: 1) [∀ (x y : Nat), 10 ≤ y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), ¬ (y < 10) → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), y ≥ 1 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Nat), 10 ≤ y → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Nat), 10 ≤ y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 10 ≤ y → ¬ (x + y ≤ x)]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if 10 ≤ y then 0 < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if y < 10 then p else x < x + y]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≤ 10 → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), 0 ≤ y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), 10 ≤ z → x < x + y]

#blaster (only-optimize: 1) [∀ (x y : Int), 10 ≤ y → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), ¬ (y < 10) → x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), y ≥ 1 → x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), 10 ≤ y → x < y + x]
#blaster (only-optimize: 1) [∀ (x y : Int), y ≤ -100 → x + y < x]
#blaster (only-optimize: 1) [∀ (x y : Int), ¬ (-100 < y) → x + y < x]
#blaster (only-optimize: 1) [∀ (x y : Int), y ≤ -1 → x + y < x]
#blaster (only-optimize: 1) [∀ (y x : Int), y ≤ -100 → y + x < x]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 ≤ y → ¬ (x + y < x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 10 ≤ y → ¬ (y + x < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), y ≤ -100 → ¬ x < x + y]
#blaster (only-optimize: 1) [∀ (y x : Int), y ≤ -100 → ¬ x < y + x]

#blaster (only-optimize: 1) [∀ (x : Int), 10 ≤ x → 0 < x]
#blaster (only-optimize: 1) [∀ (x : Int), 10 ≤ x → 0 ≤ x]
#blaster (only-optimize: 1) [∀ (x : Int), 10 ≤ x → ¬ (x < 0)]
#blaster (only-optimize: 1) [∀ (x : Int), x ≤ -100 → x < 0]
#blaster (only-optimize: 1) [∀ (x : Int), x ≤ -100 → x ≤ 0]
#blaster (only-optimize: 1) [∀ (x : Int), x ≤ -100 → ¬ (0 < x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 ≤ x → 20 ≤ y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 ≤ x → 20 ≤ y → 0 ≤ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 ≤ x → 0 ≤ y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 10 < x → 20 ≤ y → 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), x ≤ -1 → y ≤ -100 → x + y ≤ 0]
#blaster (only-optimize: 1) [∀ (x y : Int), x ≤ -1 → y ≤ -100 → ¬ 0 < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), x < -1 → y ≤ -100 → x + y < 0]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if 10 ≤ y then x < x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if y ≤ -100 then x + y < x else p]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if y < 10 then p else x < x + y]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (y ≤ -100) with
  | true  => ¬ x < x + y
  | false => p
]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (10 ≤ x), decide (20 ≤ y) with
  | true, true => 0 < x + y
  | _   , _    => p
]

-- no sign information is derived from `0 ≤ y` (`¬ (y < 0)`), `y ≤ 0`, `-10 ≤ y` or `y ≤ 10`
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), 0 ≤ y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 0 → x + y < x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), -10 ≤ y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 10 → x + y < x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 10 ≤ z → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), -10 ≤ x → 0 ≤ x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x ≤ 10 → x ≤ 0]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), -10 < y → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y < 10 → x + y < x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), 10 < z → x < x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), -10 < x → 0 ≤ x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x < 10 → x ≤ 0]

end Test.SmtLtArith
