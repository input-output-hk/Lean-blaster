import Lean
import Blaster

namespace Test.SmtEqArith

#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), 10 + x = x]
#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), x = x + 100]

#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Int), 1120 + x = x]
#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = x + 200]

#blaster [∀ (n m x: Nat), n = m → m = n + x → 0 = x]
#blaster [∀ (n m x: Nat), m < n → m = n + x → 0 = x]
#blaster [∀ (n m x: Nat), m > n → m = n + x → m - n = x]

#blaster (only-optimize: 1) [∀ (x: Nat), 10 = 10 + x → 0 = x]
#blaster (only-optimize: 1) [∀ (x: Nat), 20 + x = 10 → 0 = x]
#blaster (only-optimize: 1) [∀ (x: Nat), x + 35 = 100 → 65 = x]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < x → 0 < y → ¬ ((x * y) + 35 = 35)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < x → 0 ≠ y → ¬ ((x * y) + 35 = 35)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ x → 0 ≠ y → ¬ ((x * y) + 35 = 35)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ x → 0 < y → ¬ ((x * y) + 35 = 35)]
#blaster (only-optimize: 1) [∀ (x: Nat), 0 ≠ 10 + x]
#blaster (only-optimize: 1) [∀ (x: Nat), 5 ≠ 10 + x]
#blaster (only-optimize: 1) [∀ (x: Nat), 11 = 10 + x ↔ 1 = x]
#blaster (only-optimize: 1) [∀ (x: Nat), 10 = 10 + x ↔ 0 = x]

#blaster [∀ (n m x: Int), m = n + x → m - n = x]
#blaster (only-optimize: 1) [∀ (x: Int), 10 = 30 + x → -20 = x]
#blaster (only-optimize: 1) [∀ (x: Int), 100 = 30 + x → 70 = x]
#blaster (only-optimize: 1) [∀ (x: Int), x + 100 = 100 → 0 = x]
#blaster (only-optimize: 1) [∀ (x: Int), 0 < x → ¬ (x + 100 = 100) ]
#blaster (only-optimize: 1) [∀ (x: Int), x < 0 → ¬ (x + 100 = 100) ]
#blaster (only-optimize: 1) [∀ (x: Int), x ≠ 0 → ¬ (x + 100 = 100) ]

#blaster [∀ (n m x: Nat), m ≠ n → m + x ≠ n + x]
#blaster [∀ (n m x: Int), m ≠ n → m + x ≠ n + x]

#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), 10 + x = x + 20]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), x + 100 = x + 20]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Nat), x + 100 = 20 + x]

#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), -10 + x = x + 20]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), x + 100 = x + 20]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [∀ (x: Int), x + 100 = -20 + x]

#blaster [∀ (m n x y : Nat), m ≤ n → m + x = n + y → x = (n - m) + y]
#blaster [∀ (m n x y : Nat), m > n → m + x = n + y → (m - n) + x = y]
#blaster [∀ (m n x y : Int), m ≤ n → m + x = n + y → x = (n - m) + y]
#blaster [∀ (m n x y : Int), m > n → m + x = n + y → (m - n) + x = y]

#blaster (only-optimize: 1) [∀ (x y : Nat), 10 + x = 20 + y → x = 10 + y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 100 + x = 20 + y → 80 + x = y]
#blaster (only-optimize: 1) [∀ (x y : Nat), 100 + x = 100 + y → x = y]

#blaster (only-optimize: 1) [∀ (x y : Int), 10 + x = 20 + y → x = 10 + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 100 + x = 20 + y → 80 + x = y]
#blaster (only-optimize: 1) [∀ (x y : Int), 100 + x = 100 + y → x = y]

#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x + y = x)]

#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 ≠ y → ¬ (y + x = x)]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 < y → ¬ (y + x = x)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 ≠ y → ¬ (x = y + x)]
#blaster (only-optimize: 1) [∀ (y x : Nat), 0 < y → ¬ (x = y + x)]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), ¬ (y < 0) → ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y = 0 → ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≥ 0 → ¬ (x + y = x)]

#blaster (only-optimize: 1) [∀ (x y : Int), 0 ≠ y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 > y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 ≠ y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (x + y = x)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 > y → ¬ (x + y = x)]

#blaster (only-optimize: 1) [∀ (x y : Int), 0 ≠ y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 < y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 > y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 ≠ y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 < y → ¬ (x = x + y)]
#blaster (only-optimize: 1) [∀ (y x : Int), 0 > y → ¬ (x = x + y)]


#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), ¬ (y < 0) → ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y = 0 → ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≥ 0 → ¬ (x + y = x)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y ≤ 0 → ¬ (x + y = x)]

#blaster (only-optimize: 1) [∀ (x y : Nat), x ≠ 0 → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ x → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), x ≠ 0 → (x + y ≠ 0)]
#blaster (only-optimize: 1) [∀ (x y : Nat), x > 0 → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < x → (0 ≠ x + y)]

#blaster (only-optimize: 1) [∀ (x y : Nat), if x ≠ 0 then 0 ≠ x + y else true]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if x ≠ 0 then 0 ≠ x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if x = 0 then p else x + y ≠ 0]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), (if x ≠ 0 then 0 ≠ x + y else p) = (x = 0 → p)]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop),
  p → match decide (x ≠ 0) with
       | true  => 0 ≠ x + y
       | false => p
]

#blaster (only-optimize: 1) [∀ (x y : Nat),
  match x == 0 with
  | true  => true
  | false => x + y ≠ 0
]

#blaster (only-optimize: 1) [∀ (x y : Nat),
  match decide (x ≠ 0 ∧ y ≠ 0) with
  | true  => x + y ≠ 0
  | false => true
]

#blaster (only-optimize: 1) [∀ (x y : Nat),
  match decide (x ≠ 0) && decide (y ≠ 0) with
  | true  => x + y ≠ 0
  | false => true
]

#blaster (only-optimize: 1) [∀ (x y : Nat), if LT.lt 0 y then 0 ≠ x + y else true]
#blaster (only-optimize: 1) [∀ (x y : Nat), if GT.gt x 0 then 0 ≠ x + y else true]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x ≠ 0 → (0 = x + y)]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), 0 ≠ x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), z ≠ 0 → (0 ≠ x + y)]

#blaster (only-optimize: 1) [∀ (x y : Nat), y ≠ 0 → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 ≠ y → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), y ≠ 0 → (x + y ≠ 0)]
#blaster (only-optimize: 1) [∀ (x y : Nat), y > 0 → (0 ≠ x + y)]
#blaster (only-optimize: 1) [∀ (x y : Nat), 0 < y → (0 ≠ x + y)]

#blaster (only-optimize: 1) [∀ (x y : Nat), if y ≠ 0 then 0 ≠ x + y else true]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if y ≠ 0 then 0 ≠ x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p → if y = 0 then p else x + y ≠ 0]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), (if y ≠ 0 then 0 ≠ x + y else p) = (y = 0 → p)]
#blaster (only-optimize: 1) [∀ (x y : Nat) (p : Prop), p →
  match decide (y ≠ 0) with
  | true  => 0 ≠ x + y
  | false => p
]

#blaster (only-optimize: 1) [∀ (x y : Nat),
  match y == 0 with
  | true  => true
  | false => x + y ≠ 0
]

-- TODO: check optimization rules for imply (`→`)
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat), (x = 0 → y ≠ 0) → (0 ≠ x + y)]

-- TODO: check this one
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat) (p : Prop), p →
  match y, x with
  | 0, 0 => p
  | _, _ => x + y ≠ 0
]

-- TODO: check `decide (x ≠ 0)` ↔ `x != 0`
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat),
  match x != 0 && y != 0 with
  | true  => x + y ≠ 0
  | false => true
]

-- TODO: check `decide (x = 0)` ↔ `x == 0`
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Nat),
  match x == 0 || y == 0 with
  | true  => true
  | false => x + y ≠ 0
]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), y ≠ 0 → (0 = x + y)]

#blaster (only-optimize: 1) [∀ (x y : Int), x > 0 → y > 0 → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 < x → y > 0 → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), x > 0 → 0 < y → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 < x → 0 < y → 0 ≠ x + y]

#blaster (only-optimize: 1) [∀ (x y : Int), if 0 < x ∧ 0 < y then 0 ≠ x + y else true]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if 0 < x ∧ 0 < y then 0 ≠ x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  if 0 < y
    then if 0 < x then 0 ≠ x + y else p
    else p
]

#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (0 < y ∧ 0 < x) with
  | true => 0 ≠ x + y
  | _    => p
]

#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (0 < y), decide (0 < x) with
  | true, true => 0 ≠ x + y
  | _   , _    => p
]

#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (0 < y), decide (x ≤ 0) with
  | true, false => 0 ≠ x + y
  | _   , _     => p
]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), x > 0 → 0 ≠ x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y > 0 → 0 ≠ x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → y > 0 → 0 ≠ x + y]

#blaster (only-optimize: 1) [∀ (x y : Int), x < 0 → y < 0 → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 > x → y < 0 → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), x < 0 → 0 > y → 0 ≠ x + y]
#blaster (only-optimize: 1) [∀ (x y : Int), 0 > x → 0 > y → 0 ≠ x + y]

#blaster (only-optimize: 1) [∀ (x y : Int), if 0 > x ∧ 0 > y then 0 ≠ x + y else true]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), if 0 > x ∧ 0 < y then 0 ≠ x + y else true]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p → if 0 < x ∧ 0 < y then 0 ≠ x + y else p]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int) (p : Prop), p → if 0 < x ∧ y < 0 then 0 ≠ x + y else p]
#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  if 0 > y
    then if 0 > x then 0 ≠ x + y else p
    else p
]

#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (0 > y ∧ 0 > x) with
  | true => 0 ≠ x + y
  | _    => p
]

#blaster (only-optimize: 1) [∀ (x y : Int) (p : Prop), p →
  match decide (0 > y), decide (0 > x) with
  | true, true => 0 ≠ x + y
  | _   , _    => p
]

-- TODO: check `.negSucc _ < 0`
#blaster (only-optimize: 1) (solve-result: 2) [∀ (x y : Int) (p : Prop), p →
  match x, y with
  | .negSucc _, .negSucc _ => 0 ≠ x + y
  | _         , _          => p
]

#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), x > 0 → 0 ≠ x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : Int), y > 0 → 0 ≠ x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), z > 0 → y > 0 → 0 ≠ x + y]

-- TODO: implement these

-- 0 < x + y ===> True (if Type (x) = Int ∧ gtZeroIntInHyps x ∧ gtZeroIntInHyps y)
-- #blaster (only-optimize: 1) [∀ (x y : Int), x > 0 → y > 0 → 0 < x + y]
-- #blaster (only-optimize: 1) [∀ (x y : Int), 0 < x → 0 < y → 0 < x + y]

-- 0 < x + y ==> False (if Type (x) = Int ∧ ltZeroIntInHyps x ∧ ltZeroIntInHyps y)
-- #blaster (only-optimize: 1) [∀ (x y : Int), x < 0 → y < 0 → ¬ 0 < x + y]
-- #blaster (only-optimize: 1) [∀ (x y : Int), x < 0 → y < 0 → x + y ≤ 0]

end Test.SmtEqArith
