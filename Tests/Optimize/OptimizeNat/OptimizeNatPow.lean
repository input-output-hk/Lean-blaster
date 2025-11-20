import Lean
import Tests.Utils
import Solver.Command.Tactic
open Lean Elab Command Term

namespace Test.OptimizeNatPow

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.pow -/

/-! Test cases for `reduceApp` rule on ``Nat.pow. -/

-- 0 ^ 0 ===> 1
def natPowCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natPowCst_1" : term => return natPowCst_1

#testOptimize [ "NatPowCst_1" ] (0 : Nat) ^ 0 ===> natPowCst_1

-- 2 ^ 3 ===> 8
def natPowCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 8)
elab "natPowCst_2" : term => return natPowCst_2

#testOptimize [ "NatPowCst_2" ] (2 : Nat) ^ 3 ===> natPowCst_2

-- 5 ^ 2 ===> 25
def natPowCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 25)
elab "natPowCst_3" : term => return natPowCst_3

#testOptimize [ "NatPowCst_3" ] (5 : Nat) ^ 2 ===> natPowCst_3

-- 10 ^ 0 ===> 1
#testOptimize [ "NatPowCst_4" ] (10 : Nat) ^ 0 ===> natPowCst_1

-- 3 ^ 1 ===> 3
def natPowCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 3)
elab "natPowCst_5" : term => return natPowCst_5

#testOptimize [ "NatPowCst_5" ] (3 : Nat) ^ 1 ===> natPowCst_5

-- 7 ^ 1 ===> 7
def natPowCst_6 : Expr := Lean.Expr.lit (Lean.Literal.natVal 7)
elab "natPowCst_6" : term => return natPowCst_6

#testOptimize [ "NatPowCst_6" ] (7 : Nat) ^ 1 ===> natPowCst_6

-- 0 ^ 5 ===> 0
def natPowCst_7 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natPowCst_7" : term => return natPowCst_7

#testOptimize [ "NatPowCst_7" ] (0 : Nat) ^ 5 ===> natPowCst_7

-- 1 ^ 100 ===> 1
#testOptimize [ "NatPowCst_8" ] (1 : Nat) ^ 100 ===> natPowCst_1

-- 1 ^ 5 ===> 1
#testOptimize [ "NatPowCst_9" ] (1 : Nat) ^ 5 ===> natPowCst_1

variable (x : Nat)
/-! Test cases for simplification rules `1 ^ n ===> 1`. -/

-- 1 ^ x ===> 1
#testOptimize [ "NatPowOneBase_1" ] 1 ^ x = 1 ===> True

-- 1 ^ (x + 3) ===> 1
#testOptimize [ "NatPowOneBase_2" ] 1 ^ (x + 3) = 1 ===> True

-- 1 ^ (10 - x) ===> 1
#testOptimize [ "NatPowOneBase_3" ] 1 ^ (10 - x) = 1 ===> True

-- 1 ^ 0 ===> 1
#testOptimize [ "NatPowOneBase_4" ] 1 ^ 0 = 1 ===> True

-- 1 ^ Nat.zero ===> 1
#testOptimize [ "NatPowOneBase_5" ] 1 ^ Nat.zero = 1 ===> True


/-! Test cases for simplification rules `0 ^ n ===> 1` (if n = 0 := _ ∈ hypothesisContext.hypothesisMap)-/

-- 0 ^ 0 ===> 1
#testOptimize [ "NatPowZeroBase_1" ] 0 ^ 0 = 1 ===> True

-- 0 ^ Nat.zero ===> 1
#testOptimize [ "NatPowZeroBase_2" ] 0 ^ Nat.zero = 1 ===> True

-- 0 ^ (x - x) ===> 1
#testOptimize [ "NatPowZeroBase_3" ] 0 ^ (x - x) = 1 ===> True

-- x = 0 ⇒ 0 ^ x = 1 ===> True
#testOptimize [ "NatPowZeroBase_4" ] ∀ (x : Nat), x = 0 → 0 ^ x = 1 ===> True


/-! Test cases for simplification rule `n ^ 0 ==> 1`. -/

-- x ^ 0 ===> 1
#testOptimize [ "NatPowZeroExp_1" ] x ^ 0 = 1 ===> True

-- x ^ Nat.zero ===> 1
#testOptimize [ "NatPowZeroExp_2" ] x ^ Nat.zero = 1 ===> True

-- (x + 5) ^ 0 ===> 1
#testOptimize [ "NatPowZeroExp_3" ] (x + 5) ^ 0 = 1 ===> True

-- (10 - x) ^ 0 ===> 1
#testOptimize [ "NatPowZeroExp_4" ] (10 - x) ^ 0 = 1 ===> True


/-! Test cases for simplification rule `n ^ 1 ==> n`. -/

-- x ^ 1 ===> x
#testOptimize [ "NatPowOneExp_1" ] ∀ (y : Nat), x ^ 1 ≤ y ===> ∀ (y : Nat), ¬ y < x

-- x ^ 1 = x ===> True
#testOptimize [ "NatPowOneExp_2" ] x ^ 1 = x ===> True

-- (x + 3) ^ 1 = x + 3 ===> True
#testOptimize [ "NatPowOneExp_3" ] (x + 3) ^ 1 = x + 3 ===> True

-- (10 - x) ^ 1 = 10 - x ===> True
#testOptimize [ "NatPowOneExp_4" ] (10 - x) ^ 1 = 10 - x ===> True


/-! Test cases for simplification rule `1 ^ n ==> 1`. -/

-- 1 ^ x = 1 (in equality test)
def natPowOneBase_1 : Expr :=
  Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.const `Not [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
          (Lean.Expr.lit (Lean.Literal.natVal 0)))
        (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default)

elab "natPowOneBase_1" : term => return natPowOneBase_1

#testOptimize [ "NatPowOneBase_1" ] ∀ (y : Nat), 1 ^ x ≤ y ===> natPowOneBase_1

-- 1 ^ x = 1 ===> True
#testOptimize [ "NatPowOneBase_2" ] 1 ^ x = 1 ===> True

-- 1 ^ (x + 5) = 1 ===> True
#testOptimize [ "NatPowOneBase_3" ] 1 ^ (x + 5) = 1 ===> True

-- 1 ^ (10 - x) = 1 ===> True
#testOptimize [ "NatPowOneBase_4" ] 1 ^ (10 - x) = 1 ===> True


/-! Test cases for simplification rule `0 ^ n ==> 0` (when n ≠ 0). -/
-- 0 ^ 5 ===> 0
#testOptimize [ "NatPowZeroBase_1" ] 0 ^ (5 : Nat) = 0 ===> True

-- (h1: 0 ≠ x) ⇒ 0 ^ x = 0 ===> True
#testOptimize [ "NatPowZeroBase_3" ] ∀ (x : Nat), x > 0 → 0 ^ x = 0 ===> True

/-! Test cases for simplification rule `(n ^ m1) ^ m2 ==> n ^ (m1 * m2)`. -/

-- (x ^ 2) ^ 3 = x ^ 6 ===> True
#testOptimize [ "NatPowOfPow_1" ] (x ^ 2) ^ 3 = x ^ 6 ===> True

-- (2 ^ 3) ^ 2 = 64 ===> True
#testOptimize [ "NatPowOfPow_2" ] (2 ^ 3) ^ 2 = 64 ===> True

-- (x ^ 1) ^ 5 = x ^ 5 ===> True
#testOptimize [ "NatPowOfPow_3" ] (x ^ 1) ^ 5 = x ^ 5 ===> True

-- ((x ^ 2) ^ 3) ^ 2 = x ^ 12 ===> True
#testOptimize [ "NatPowOfPow_4" ] ((x ^ 2) ^ 3) ^ 2 = x ^ 12 ===> True

-- (x ^ (x + 1)) ^ 2 = x ^ (2 * (x + 1)) ===> True
#testOptimize [ "NatPowOfPow_5" ] (x ^ (x + 1)) ^ 2 = x ^ (2 * (x + 1)) ===> True

/-! Test cases to ensure that simplification rules are not wrongly applied. -/

-- x ^ 10 ===> x ^ 10 (must remain unchanged)
def natPowUnchanged_1 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
     (Lean.Expr.const `Nat [])
       (Lean.Expr.app
         (Lean.Expr.app
           (Lean.Expr.app
             (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
             (Lean.Expr.const `instLTNat []))
           (Lean.Expr.app
             (Lean.Expr.app (Lean.Expr.const `Nat.pow []) (Lean.Expr.bvar 1))
             (Lean.Expr.lit (Lean.Literal.natVal 10))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natPowUnchanged_1" : term => return natPowUnchanged_1

#testOptimize [ "NatPowUnchanged_1" ] ∀ (x y : Nat), x ^ 10 < y ===> natPowUnchanged_1

-- x ^ y < 10 ===> x ^ y < 10 (must remain unchanged)
def natPowUnchanged_2 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
     (Lean.Expr.const `Nat [])
       (Lean.Expr.app
         (Lean.Expr.app
           (Lean.Expr.app
             (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
             (Lean.Expr.const `instLTNat []))
           (Lean.Expr.app
             (Lean.Expr.app (Lean.Expr.const `Nat.pow []) (Lean.Expr.bvar 1))
             (Lean.Expr.bvar 0)))
         (Lean.Expr.lit (Lean.Literal.natVal 10)))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natPowUnchanged_2" : term => return natPowUnchanged_2

#testOptimize [ "NatPowUnchanged_2" ] ∀ (x y : Nat), x ^ y < 10 ===> natPowUnchanged_2


/-! Test cases for power reduction via constant propagation. -/

variable (x : Nat)
variable (y : Nat)

variable (a : Nat)
variable (m n : Nat)
-- (x ^ 2) ^ (y - y) = x ^ 0 = 1 ===> True
#testOptimize [ "NatPowReduce_1" ] (x ^ 2) ^ (y - y) = 1 ===> True

-- (x ^ 2) ^ (y - y) = x ^ 0 ===> True
#testOptimize [ "NatPowReduce_2" ] (x ^ 2) ^ (y - y) = x ^ 0 ===> True

theorem one_pow_any (m : Nat) : (1 : Nat) ^ m = 1 := by blaster
#testOptimize ["Issue1"] a ^ (m + n) = a ^ m * a ^ n ===> True
end Test.OptimizeNatPow
