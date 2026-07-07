import Blaster

namespace Test.SmtNatMul

/-! ## Test objectives to validate `Nat.mul` semantics with backend solver -/

/-! # Test cases to validate `Nat.mul` semantics with backend solver -/

#blaster (solver: all) [∀ (x : Nat), (x * 0) = 0]

#blaster (solver: all) [∀ (x : Nat), (x * 1) = x]

#blaster (solver: all) [∀ (x y : Nat), x * Nat.succ y = x * y + x]

#blaster (solver: all) [∀ (x y : Nat), x * y = y * x]

#blaster (solver: all) [∀ (x y z : Nat), (x + y) * z = (x * z) + (y * z)]

#blaster (solver: all) [∀ (x y z : Nat), z * (x + y) = (z * x) + (z * y)]

#blaster (solver: all) [∀ (x y z : Nat), (x * y) * z = x * (y * z)]

#blaster (solver: all) [∀ (x y z : Nat), x * (y * z) = y * (x * z)]

#blaster (solver: all) [∀ (x : Nat), x * 2 = x + x]

#blaster (solver: all) [∀ (x y z : Nat), x ≤ y → z * x ≤ z * y]

#blaster (solver: all) [∀ (w x y z : Nat), w ≤ x → y ≤ z → w * y ≤ x * z]

#blaster (solver: all) [∀ (x y z : Nat), x < y → z > 0 → x * z < y * z]

#blaster (solver: all) [∀ (x y : Nat), x > 0 → y > 0 -> x * y > 0]

#blaster (solver: all) [∀ (x y z : Nat), 0 < x → x * y = x * z → y = z]

def isInjective (f : Nat → Nat) : Prop :=
  ∀ (x y : Nat), f x = f y → x = y

def isSurjective (f : Nat → Nat) : Prop :=
  ∀ (y : Nat), ∃ (x : Nat), f x = y

def isBijective (f : Nat → Nat) : Prop :=
  isInjective f ∧ isSurjective f

def square (x : Nat) : Nat := x * x

#blaster (solver: all) [isInjective square]

/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [isSurjective square]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [isBijective square]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y ≠ y * x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y > x]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x * y > y]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y : Nat), x = 0 → x * y > 0]

#blaster (only-optimize: 1) [∀ (x y z : Nat), x ≠ 0 → x * y = x * z → y = z]
#blaster (only-optimize: 1) [∀ (x y z : Nat), x > 0 → y * x = x * z → y = z]
#blaster (only-optimize: 1) [∀ (x y : Nat), 2 * x = y * 2 → x = y]

#blaster (only-optimize: 1) [∀ (x y z : Nat), x ≠ 0 → x * z = y * x → y = z]
-- NOTE: solve optimization "ordering"
#blaster (solver: all)                    [∀ (x y z : Nat), x * z = y * x → x ≠ 0 → y = z]

#blaster (only-optimize: 1) [∀ (x y z : Nat), x ≠ 0 → if x * z = y * x then y = z else true]
-- NOTE: solve optimization "ordering"
#blaster (solver: all)                    [∀ (x y z : Nat), x * z = y * x → if x = 0 then true else y = z]
#blaster (only-optimize: 1) [∀ (a b c x y z : Nat) (p : Prop), p →
  match b, a * b == b * c with
  | 0, _     => p
  | _, true  => a = c
  | _, false => p
]

#blaster (only-optimize: 1) [∀ (a b c x y z : Nat) (p : Prop), p →
  match b with
  | 0 => p
  | _ => match a * b == b * c with
         | true  => a = c
         | false => p
]

#blaster (only-optimize: 1) [∀ (a b c x y z : Nat) (p : Prop), p →
  match decide (a * b = b * c), b with
  | _    , 0 => p
  | true , _ => a = c
  | false, _ => p
]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), x ≠ 0 → x * y = y * z → y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), x * y = x * z → y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Nat), x = z → x * y = x * z]

#blaster (only-optimize: 1) [∀ (x y z : Int), x ≠ 0 → x * y = x * z → y = z]
#blaster (only-optimize: 1) [∀ (x y z : Int), x > 0 → x * y = x * z → y = z]
#blaster (only-optimize: 1) [∀ (x y z : Int), x < 0 → x * y = x * z → y = z]
#blaster (only-optimize: 1) [∀ (x y z : Int), y ≠ 0 → y * y = z * y → y = z]

-- NOTE: This test case can be resolved to True at preprocessing phase when reordering on hypothesis is considered.
#blaster (solver: all)                    [∀ (x y z : Int), x * z = y * x → x ≠ 0 → y = z]
#blaster (only-optimize: 1) [∀ (x y z : Int), x ≠ 0 → if x * z = y * x then y = z else true]
-- NOTE: This test case can be resolved to True at preprocessing phase when reordering on hypothesis is considered.
#blaster (solver: all)                    [∀ (x y z : Int), x * z = y * x → if x = 0 then true else y = z]
#blaster (only-optimize: 1) [∀ (a b c x y z : Int) (p : Prop), p →
  match b, decide (a * b = b * c) with
  | 0, _     => p
  | _, true  => a = c
  | _, false => p
]

#blaster (only-optimize: 1) [∀ (a b c x y z : Int) (p : Prop), p →
  match decide (a * b = b * c), b with
  | _    , 0 => p
  | true , _ => a = c
  | false, _ => p
]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), x ≠ 0 → x * y = y * z → y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), x * y = x * z → y = z]
#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), x = z → x * y = x * z]

#blaster (solver: all) (gen-cex: 0) (solve-result: 1) [∀ (x y z : Int), x * y = x * z → z = y]

end Test.SmtNatMul
