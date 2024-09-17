import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatDiv

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.div -/

/-! Test cases for `reduceApp` rule on ``Nat.div. -/

-- 0 / 432 ===> 0
def natDivCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natDivCst_1" : term => return natDivCst_1

#testOptimize [ "NatDivCst_1" ] (0 : Nat) / 432 ===> natDivCst_1

-- 432 / 0 ===> 0
-- NOTE: divison by zero not triggered
#testOptimize [ "NatDivCst_2" ] (432 : Nat) / 0 ===> natDivCst_1

-- 132 / 1 ===> 132
def natDivCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 132)
elab "natDivCst_3" : term => return natDivCst_3

#testOptimize [ "NatDivCst_3" ] (132 : Nat) / 1 ===> natDivCst_3

-- 7 / 3 ===> 2
def natDivCst_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 2)
elab "natDivCst_4" : term => return natDivCst_4

#testOptimize [ "NatDivCst_4" ] (7 : Nat) / 3 ===> natDivCst_4

-- 18 / 3 ===> 6
def natDivCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 6)
elab "natDivCst_5" : term => return natDivCst_5

#testOptimize [ "NatDivCst_5" ] (18 : Nat) / 3 ===> natDivCst_5

-- 8 / 3 ===> 2
#testOptimize [ "NatDivCst_6" ] (8 : Nat) / 3 ===> natDivCst_4


/-! Test cases for simplification rule `n / 0 ==> 0`. -/

-- x / 0 ===> 0
def natDivZero_1 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.lit (Lean.Literal.natVal 0)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natDivZero_1" : term => return natDivZero_1

#testOptimize [ "NatDivZero_1" ] ∀ (x y : Nat), x / 0 < y ===> natDivZero_1

-- x / 0 = 0 ===> True
#testOptimize [ "NatDivZero_2" ] ∀ (x : Nat), x / 0 = 0 ===> True

-- x / Nat.zero ===> 0
#testOptimize [ "NatDivZero_3" ] ∀ (x y : Nat), x / Nat.zero < y ===> natDivZero_1

-- x / Nat.zero = 0 ===> True
#testOptimize [ "NatDivZero_4" ] ∀ (x : Nat), x / Nat.zero = 0 ===> True

-- ∀ (x y : Nat), (x / y - y) = 0 ===> True
#testOptimize [ "NatDivZero_5" ] ∀ (x y : Nat), x / (y - y) = 0 ===> True

-- ∀ (x y : Nat), (x / ((1 * y) - y)) = 0 ===> True
#testOptimize [ "NatDivZero_6" ] ∀ (x y : Nat), x / ((1 * y) - y) = 0 ===> True


/-! Test cases for simplification rule `n / 1 ==> n`. -/

-- x / 1 ===> x
#testOptimize [ "NatDivOne_1" ] ∀ (x y : Nat), x / 1 < y ===> ∀ (x y : Nat), x < y

-- x / 1 = x ===> True
#testOptimize [ "NatDivOne_2" ] ∀ (x : Nat), x / 1 = x ===> True

-- ∀ (x y : Nat), (x / ((((Nat.succ y) - 1) - y) + 1) = x ===> True
#testOptimize [ "NatDivOne_3" ] ∀ (x y : Nat), x / ((((Nat.succ y) - 1) - y) + 1) = x ===> True

-- ∀ (x y : Nat), (x / (((100 - y) -230) + 1) = x ===> True
#testOptimize [ "NatDivOne_4" ] ∀ (x y : Nat), x / (((100 - y) -230) + 1) = x ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
      - `n / 0 ==> 0`
      - `n / 1 ==> n`
-/

-- x / 10 ===> x / 10
def natDivCstUnchanged_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 1))
          (Lean.Expr.lit (Lean.Literal.natVal 10))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natDivCstUnchanged_1" : term => return natDivCstUnchanged_1

#testOptimize [ "NatDivCstUnchanged_1" ] ∀ (x y : Nat), x / 10 < y ===> natDivCstUnchanged_1

-- x / (100 - 90) ===> x / 10
#testOptimize [ "NatDivCstUnchanged_2" ] ∀ (x y : Nat), x / (100 - 90) < y ===> natDivCstUnchanged_1


-- ∀ (x y z : Nat), (x / y - x) < z ==> ∀ (x y z : Nat), Nat.div x (Nat.sub y x) < z
#testOptimize [ "NatDivCstUnchanged_3" ] ∀ (x y z : Nat), x / (y - x) < z ===>
                                         ∀ (x y z : Nat), Nat.div x (Nat.sub y x) < z


/-! Test cases for simplification rule `0 / n ==> 0`. -/

-- 0 / x ===> 0
#testOptimize [ "NatZeroDiv_1" ] ∀ (x y : Nat), 0 / x < y ===> natDivZero_1

-- 0 / x = 0 ===> True
#testOptimize [ "NatZeroDiv_2" ] ∀ (x : Nat), 0 / x = 0 ===> True

-- Nat.zero / x ===> 0
#testOptimize [ "NatZeroDiv_3" ] ∀ (x y : Nat), Nat.zero / x < y ===> natDivZero_1

-- Nat.zero / x = 0 ===> True
#testOptimize [ "NatZeroDiv_4" ] ∀ (x : Nat), Nat.zero / x = 0 ===> True


-- ∀ (x y : Nat), (y - y) / x = 0 ===> True
#testOptimize [ "NatZeroDiv_5" ] ∀ (x y : Nat), (y - y) / x  = 0 ===> True

-- ∀ (x y : Nat), ((100 - y) - 120) / x = 0 ===> True
#testOptimize [ "NatZeroDiv_6" ] ∀ (x y : Nat), ((100 - y) - 120) / x = 0 ===> True



/-! Test cases to ensure that simplification rule `0 / n ==> 0` is not wrongly applied. -/

-- 10 / x ===> 10 / x
def natCstDivUnchanged_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
          (Lean.Expr.bvar 1)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natCstDivUnchanged_1" : term => return natCstDivUnchanged_1

#testOptimize [ "NatCstDivUnchanged_1" ] ∀ (x y : Nat), 10 / x < y ===> natCstDivUnchanged_1

-- (100 - 90) / x ===> 10 / x
#testOptimize [ "NatCstDivUnchanged_2" ] ∀ (x y : Nat), (100 - 90) / x < y ===> natCstDivUnchanged_1


-- ∀ (x y z : Nat), (x / y - x) < z ==> ∀ (x y z : Nat), Nat.div x (Nat.sub y x) < z
#testOptimize [ "NatCstDivUnchanged_3" ] ∀ (x y z : Nat), (y - x) / x < z ===>
                                         ∀ (x y z : Nat), Nat.div (Nat.sub y x) x < z


/-! Test cases for simplification rule `(n / N1) / N2 ==> n / (N1 "*" N2) (if N1 > 0 ∧ N2 > 0)`. -/

-- (x / 10) / 20 ===> x / 200
def natDivDivCstProp_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 1))
          (Lean.Expr.lit (Lean.Literal.natVal 200))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natDivDivCstProp_1" : term => return natDivDivCstProp_1

#testOptimize [ "NatDivDivCstProp_1" ] ∀ (x y : Nat), (x / 10) / 20 < y ===> natDivDivCstProp_1

-- (x / 10) / 20 = x / 200 ===> True
#testOptimize [ "NatDivDivCstProp_2" ] ∀ (x : Nat), (x / 10) / 20 = (x / 200) ===> True

-- (x / 0) / 20 = 0 ===> True
#testOptimize [ "NatDivDivCstProp_3" ] ∀ (x : Nat), (x / 0) / 20 = 0 ===> True

-- (x / 10) / 0 = 0 ===> True
#testOptimize [ "NatDivDivCstProp_4" ] ∀ (x : Nat), (x / 10) / 0 = 0 ===> True

-- (x / 10) / 0 = 0 ===> True
#testOptimize [ "NatDivDivCstProp_5" ] ∀ (x : Nat), (x / 10) / 0 = 0 ===> True

-- (x / 10) / ((20 - (50 + x)) + 10) = x / 100 ===> True
#testOptimize [ "NatDivDivCstProp_6" ] ∀ (x : Nat), (x / 10) / ((20 - (50 + x)) + 10) = x / 100 ===> True

-- (((x / 10) / 3) / 40) = x / 1200 ===> True
#testOptimize [ "NatDivDivCstProp_7" ] ∀ (x : Nat), (((x / 10) / 3) / 40) = x / 1200 ===> True

-- (((x / 100 + ((120 - x) - 150)) / 3) / 14) = x / 4200 ===> True
#testOptimize [ "NatDivDivCstProp_8" ] ∀ (x : Nat), (((x / 100 + ((120 - x) - 150)) / 3) / 14) = x / 4200 ===> True


/-! Test cases to ensure that simplification rule `(n / N1) / N2 ==> n / (N1 "*" N2) (if N1 > 0 ∧ N2 > 0)`
    is not wrongly applied.
-/

-- (x / 10) / y ===> (x / 10) / y
def natDivDivCstUnchanged_1 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `z
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Nat.div [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 2))
                (Lean.Expr.lit (Lean.Literal.natVal 10))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.bvar 0))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natDivDivCstUnchanged_1" : term => return natDivDivCstUnchanged_1

#testOptimize [ "NatDivDivCstUnchanged_1" ] ∀ (x y z : Nat), (x / 10) / y < z ===>  natDivDivCstUnchanged_1

-- (x / 10) / y = (x / 10) / y ===> True
#testOptimize [ "NatDivDivCstUnchanged_2" ] ∀ (x y : Nat), (x / 10) / y = (x / 10) / y ===> True

-- (x / y) / 20 ===> (x / y) / 20
def natDivDivCstUnchanged_3 : Expr :=
Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `z
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Nat.div [])
              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 1)))
            (Lean.Expr.lit (Lean.Literal.natVal 20))))
        (Lean.Expr.bvar 0))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natDivDivCstUnchanged_3" : term => return natDivDivCstUnchanged_3

#testOptimize [ "NatDivDivCstUnchanged_3" ] ∀ (x y z : Nat), (x / y) / 20 < z ===> natDivDivCstUnchanged_3

-- (x / y) / 20 = (x / y) / 20 ===> True
#testOptimize [ "NatDivDivCstUnchanged_4" ] ∀ (x y : Nat), (x / y) / 20 = (x / y) / 20 ===> True



/-! Test cases for simplification rule
       `(N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0)`.
-/

-- (10 * x) / 5 ===> 2 * x
def natMulDivCstProp_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 2)))
          (Lean.Expr.bvar 1)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstProp_1" : term => return natMulDivCstProp_1

#testOptimize [ "NatMulDivCstProp_1" ] ∀ (x y : Nat), (10 * x) / 5 < y ===> natMulDivCstProp_1

def natMulDivCstProp_2 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 2)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 3))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstProp_2" : term => return natMulDivCstProp_2

-- (10 * x) / 15 ===> (2 * x) / 3
#testOptimize [ "NatMulDivCstProp_2" ] ∀ (x y : Nat), (10 * x) / 15 < y ===> natMulDivCstProp_2

def natMulDivCstProp_3 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 13))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstProp_3" : term => return natMulDivCstProp_3

-- (10 * x) / 13 ===> (10 * x) / 13
#testOptimize [ "NatMulDivCstProp_3" ] ∀ (x y : Nat), (10 * x) / 13 < y ===> natMulDivCstProp_3


-- (6 * x) / 120 ===> x / 20
def natMulDivCstProp_4 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 1))
          (Lean.Expr.lit (Lean.Literal.natVal 20))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstProp_4" : term => return natMulDivCstProp_4

#testOptimize [ "NatMulDivCstProp_4" ] ∀ (x y : Nat), (6 * x) / 120 < y ===> natMulDivCstProp_4

-- (16 * x) / 16 ===> x
#testOptimize [ "NatMulDivCstProp_5" ] ∀ (x y : Nat), (16 * x) / 16 < y ===> ∀ (x y : Nat), x < y


/-! Test cases to ensure that simplification rule
      `(N1 * n) / N2 ===> ((N1 "/" Nat.gcd N1 N2) * n) / (N2 "/" Nat.gcd N1 N2) (if N2 > 0)`
    is not wrongly applied.
-/

-- (10 * x) / 0 ===> 0
def natMulDivCstUnchanged_1 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.lit (Lean.Literal.natVal 0)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstUnchanged_1" : term => return natMulDivCstUnchanged_1

#testOptimize [ "NatMulDivCstUnchanged_1" ] ∀ (x y : Nat), (10 * x) / 0 < y ===> natMulDivCstUnchanged_1

-- (10 * x) / y ===> (10 * x) / y
def natMulDivCstUnchanged_2 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.bvar 0)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstUnchanged_2" : term => return natMulDivCstUnchanged_2

#testOptimize [ "NatMulDivCstUnchanged_2" ] ∀ (x y : Nat), (10 * x) / y < y ===> natMulDivCstUnchanged_2

def natMulDivCstUnchanged_3 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0)))
          (Lean.Expr.lit (Lean.Literal.natVal 13))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstUnchanged_3" : term => return natMulDivCstUnchanged_3

-- (x * y) / 13 ===> (x * y) / 13
#testOptimize [ "NatMulDivCstUnchanged_3" ] ∀ (x y : Nat), (x * y) / 13 < y ===> natMulDivCstUnchanged_3


-- (6 - x) / 120 ===> (6 - x) / 20
def natMulDivCstUnchanged_4 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 6)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 120))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstUnchanged_4" : term => return natMulDivCstUnchanged_4

#testOptimize [ "NatMulDivCstUnchanged_4" ] ∀ (x y : Nat), (6 - x) / 120 < y ===> natMulDivCstUnchanged_4

-- (16 + x) / 16 ===> (16 + x) / 16
def natMulDivCstUnchanged_5 : Expr :=
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
          (Lean.Expr.app
            (Lean.Expr.const `Nat.div [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 16)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 16))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulDivCstUnchanged_5" : term => return natMulDivCstUnchanged_5

#testOptimize [ "NatMulDivCstUnchanged_5" ] ∀ (x y : Nat), (16 + x) / 16 < y ===> natMulDivCstUnchanged_5



/-! Test cases for the following simplification rules:
      - `(m * n) / m ==> n`
      - `(n * m) / m ==> n`
-/

-- (x * y) / y ===> x
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulDivReduce_1" ] ∀ (x y z : Nat), (x * y) / y < z ===> ∀ (x _y z : Nat), x < z

-- (x * y) / y = x ===> True
#testOptimize [ "NatMulDivReduce_2" ] ∀ (x y : Nat), (x * y) / y = x ===> True

-- (y * x) / y ===> x
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulDivReduce_3" ] ∀ (y x z : Nat), (y * x) / y < z ===> ∀ (_y x z : Nat), x < z

-- (y * x) / y = x ===> True
#testOptimize [ "NatMulDivReduce_4" ] ∀ (y x : Nat), (y * x) / y = x ===> True

-- (y * x) / (y + 0) = x ===> True
#testOptimize [ "NatMulDivReduce_5" ] ∀ (y x : Nat), (y * x) / (y + 0) = x ===> True

-- (y * x) / (y + (z - z)) = x ===> True
#testOptimize [ "NatMulDivReduce_6" ] ∀ (y x z : Nat), (y * x) / (y + (z - z)) = x ===> True

-- ((y + 0) * x) / (y + (z - z)) = x ===> True
#testOptimize [ "NatMulDivReduce_7" ] ∀ (y x z : Nat), ((y + 0) * x) / (y + (z - z)) = x ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied
      - `(m * n) / m ==> n`
      - `(n * m) / m ==> n`
-/

-- (x * y) / z ===> (x * y) / z
#testOptimize [ "NatMulDivReduceUnchanged_1" ] ∀ (x y z : Nat), (x * y) / z < z ===>
                                               ∀ (x y z : Nat), Nat.div (Nat.mul x y) z < z

-- (y * x) / z ===> (y * x) / z
#testOptimize [ "NatMulDivReduceUnchanged_2" ] ∀ (y x z : Nat), (y * x) / z < z ===>
                                               ∀ (y x z : Nat), Nat.div (Nat.mul y x) z < z

-- (y * x) / (y + z) ===> Nat.div (Nat.mul x y) (Nat.add y z)
#testOptimize [ "NatMulDivReduceUnchanged_3" ] ∀ (x y z : Nat), (y * x) / (y + z) < z ===>
                                               ∀ (x y z : Nat), Nat.div (Nat.mul x y) (Nat.add y z) < z



/-! Test cases to ensure that `Nat.div` is preserved when expected and is not a commutative operator. -/
-- x / y ===> x / y
#testOptimize [ "NatDivVar_1" ] ∀ (x y z : Nat), x / y < z ===> ∀ (x y z : Nat), Nat.div x y < z

-- x / y = x / y ===> True
#testOptimize [ "NatDivVar_2" ] ∀ (x y : Nat), x / y = x / y ===> True

-- x / (y / 1) ===> x / y
#testOptimize [ "NatDivVar_3" ] ∀ (x y z : Nat), x / (y / 1) < z ===> ∀ (x y z : Nat), Nat.div x y < z

-- (x / 1) / y ===> x / y
#testOptimize [ "NatDivVar_4" ] ∀ (x y z : Nat), (x / 1) / y < z ===> ∀ (x y z : Nat), Nat.div x y < z

-- (x / 1) / (y / y) = x / (y / y) ===> True
#testOptimize [ "NatDivVar_5" ] ∀ (x y : Nat), (x / 1) / (y / y) = x / (y / y) ===> True

-- (x / 10) / y = (x / (15 - 5)) / y ===> True
#testOptimize [ "NatDivVar_6" ] ∀ (x y : Nat), (x / 10) / y = (x / (15 - 5)) / y ===> True

-- (x / 10) / y ===> (x / 10) / y
def natDivVar_7 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `z
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Nat.div [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 2))
                (Lean.Expr.lit (Lean.Literal.natVal 10))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.bvar 0))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natDivVar_7" : term => return natDivVar_7

#testOptimize [ "NatDivVar_7" ] ∀ (x y z : Nat), (x / 10) / y < z ===> natDivVar_7


/-! Test cases to ensure that `reduceApp` is properly called
    when `Nat.div` operands are reduced to constant values
    via optimization. -/

opaque x : Nat
opaque y : Nat
opaque z : Nat

-- (((x * y) / y) - x) / z ===> 0
def natDivReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natDivReduce_1" : term => return natDivReduce_1

#testOptimize [ "NatDivReduce_1" ] (((x * y) / y) - x) / z ===>  natDivReduce_1

-- (30 + (0 / x)) / ((((((120 * x) / 12) / 10) - x)) + 10) ===> 3
def natDivReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 3)
elab "natDivReduce_2" : term => return natDivReduce_2

#testOptimize [ "NatDivReduce_2" ]  (30 + (0 / x)) / ((((((120 * x) / 12) / 10) - x)) + 10) ===> natDivReduce_2

end Test.OptimizeNatDiv
