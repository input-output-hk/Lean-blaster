import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatMod

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.mod -/

/-! Test cases for `reduceApp` rule on ``Nat.div. -/

-- 0 % 432 ===> 0
def natModCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natModCst_1" : term => return natModCst_1

#testOptimize [ "NatModCst_1" ] (0 : Nat) % 432 ===> natModCst_1

-- 432  % 0 ===> 432
-- NOTE: divison by zero not triggered
def natModCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 432)
elab "natModCst_2" : term => return natModCst_2

#testOptimize [ "NatModCst_2" ] (432 : Nat) % 0 ===> natModCst_2

-- 121 % 1 ==> 0
#testOptimize [ "NatModCst_3" ] (121 : Nat) % 1 ===> natModCst_1

-- 7 % 3 ===> 1
def natModCst_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natModCst_4" : term => return natModCst_4

#testOptimize [ "NatModCst_4" ] (7 : Nat) % 3 ===> natModCst_4

-- 18 % 3 ===> 0
#testOptimize [ "NatModCst_5" ] (18 : Nat) % 3 ===> natModCst_1


/-! Test cases for simplification rule `n % 0 ==> n`. -/

-- x % 0 ===> x
#testOptimize [ "NatModZero_1" ] ∀ (x y : Nat), x % 0 < y ===> ∀ (x y : Nat), x < y

-- x % 0 = x ===> True
#testOptimize [ "NatModZero_2" ] ∀ (x : Nat), x % 0 = x ===> True

-- x % Nat.zero ===> x
#testOptimize [ "NatModZero_3" ] ∀ (x y : Nat), x % Nat.zero < y ===> ∀ (x y : Nat), x < y

-- x % Nat.zero = x ===> True
#testOptimize [ "NatModZero_4" ] ∀ (x : Nat), x % Nat.zero = x ===> True

-- ∀ (x y : Nat), (x % y - y) = x ===> True
#testOptimize [ "NatModZero_5" ] ∀ (x y : Nat), x % (y - y) = x ===> True

-- ∀ (x y : Nat), (x % ((1 * y) - y)) = x ===> True
#testOptimize [ "NatModZero_6" ] ∀ (x y : Nat), x % ((1 * y) - y) = x ===> True


/-! Test cases for simplification rule `n % 1 ==> 0`. -/

-- x % 1 ===> 0
def natModOne_1 : Expr :=
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

elab "natModOne_1" : term => return natModOne_1

#testOptimize [ "NatModOne_1" ] ∀ (x y : Nat), x % 1 < y ===> natModOne_1

-- x % 1 = 0 ===> True
#testOptimize [ "NatModOne_2" ] ∀ (x : Nat), x % 1 = 0 ===> True

-- ∀ (x y : Nat), (x % ((((Nat.succ y) - 1) - y) + 1) = 0 ===> True
#testOptimize [ "NatModOne_3" ] ∀ (x y : Nat), x % ((((Nat.succ y) - 1) - y) + 1) = 0 ===> True

-- ∀ (x y : Nat), (x % (((100 - y) -230) + 1) = 0 ===> True
#testOptimize [ "NatModOne_4" ] ∀ (x y : Nat), x % (((100 - y) -230) + 1) = 0 ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
      - `n % 0 ==> n`
      - `n % 1 ==> 0`
-/

-- x % 10 ===> x % 10
def natModCstUnchanged_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.mod []) (Lean.Expr.bvar 1))
          (Lean.Expr.lit (Lean.Literal.natVal 10))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natModCstUnchanged_1" : term => return natModCstUnchanged_1

#testOptimize [ "NatModCstUnchanged_1" ] ∀ (x y : Nat), x % 10 < y ===> natModCstUnchanged_1

-- x % (100 - 90) ===> x % 10
#testOptimize [ "NatModCstUnchanged_2" ] ∀ (x y : Nat), x % (100 - 90) < y ===> natModCstUnchanged_1


-- ∀ (x y z : Nat), (x % y - x) < z ==> ∀ (x y z : Nat), Nat.div x (Nat.sub y x) < z
#testOptimize [ "NatModCstUnchanged_3" ] ∀ (x y z : Nat), x % (y - x) < z ===>
                                         ∀ (x y z : Nat), Nat.mod x (Nat.sub y x) < z


/-! Test cases for simplification rule `0 % n ==> 0`. -/

-- 0 % x ===> 0
#testOptimize [ "NatZeroMod_1" ] ∀ (x y : Nat), 0 % x < y ===> natModOne_1

-- 0 % x = 0 ===> True
#testOptimize [ "NatZeroMod_2" ] ∀ (x : Nat), 0 % x = 0 ===> True

-- Nat.zero % x ===> 0
#testOptimize [ "NatZeroMod_3" ] ∀ (x y : Nat), Nat.zero % x < y ===> natModOne_1

-- Nat.zero % x = 0 ===> True
#testOptimize [ "NatZeroMod_4" ] ∀ (x : Nat), Nat.zero % x = 0 ===> True


-- ∀ (x y : Nat), (y - y) % x = 0 ===> True
#testOptimize [ "NatZeroMod_5" ] ∀ (x y : Nat), (y - y) % x  = 0 ===> True

-- ∀ (x y : Nat), ((100 - y) - 120) % x = 0 ===> True
#testOptimize [ "NatZeroMod_6" ] ∀ (x y : Nat), ((100 - y) - 120) % x = 0 ===> True



/-! Test cases to ensure that simplification rule `0 % n ==> 0` is not wrongly applied. -/

-- 10 % x ===> 10 % x
def natCstModUnchanged_1 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.mod []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
          (Lean.Expr.bvar 1)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natCstModUnchanged_1" : term => return natCstModUnchanged_1

#testOptimize [ "NatCstModUnchanged_1" ] ∀ (x y : Nat), 10 % x < y ===> natCstModUnchanged_1

-- (100 - 90) % x ===> 10 % x
#testOptimize [ "NatCstModUnchanged_2" ] ∀ (x y : Nat), (100 - 90) % x < y ===> natCstModUnchanged_1


-- ∀ (x y z : Nat), (x % y - x) < z ==> ∀ (x y z : Nat), Nat.mod x (Nat.sub y x) < z
#testOptimize [ "NatCstModUnchanged_3" ] ∀ (x y z : Nat), (y - x) % x < z ===>
                                         ∀ (x y z : Nat), Nat.mod (Nat.sub y x) x < z




/-! Test cases for simplification rule `(N1 * n) % N2 ==> 0 (if N1 % N2 = 0 ∧ N2 > 0)`. -/


-- (124 * x) % 4 ===> 0
-- TODO: remove unused quantifier when COI performed on forall
def natMulModCstProp_1 : Expr :=
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
elab "natMulModCstProp_1" : term => return natMulModCstProp_1

#testOptimize [ "NatMulModCstProp_1" ] ∀ (x y : Nat), (124 * x) % 4 < y ===> natMulModCstProp_1

-- (2197 * x) % 13 ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulModCstProp_2" ] ∀ (x y : Nat), (2197 * x) % 13 < y ===> natMulModCstProp_1


-- ((169 - (200 - (x + 259))) * x) % 13 ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulModCstProp_3" ] ∀ (x y : Nat), ((169 - (200 - (x + 259))) * x) % 13 < y ===> natMulModCstProp_1



/-! Test cases to ensure that simplification rule `(N1 * n) % N2 ==> 0 (if N1 % N2 = 0 ∧ N2 > 0)`
    is not wrongly applied.
-/

-- (124 * x) % 9 ===> (124 * x) % 9
def natMulModCstUnchanged_1 : Expr :=
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
            (Lean.Expr.const `Nat.mod [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 124)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 9))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulModCstUnchanged_1" : term => return natMulModCstUnchanged_1

#testOptimize [ "NatMulModCstUnchanged_1" ] ∀ (x y : Nat), (124 * x) % 9 < y ===> natMulModCstUnchanged_1

-- (2197 * x) % 14 ===> (2197 * x) % 14
def natMulModCstUnchanged_2 : Expr :=
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
            (Lean.Expr.const `Nat.mod [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 2197)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 14))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulModCstUnchanged_2" : term => return natMulModCstUnchanged_2

#testOptimize [ "NatMulModCstUnchanged_2" ] ∀ (x y : Nat), (2197 * x) % 14 < y ===> natMulModCstUnchanged_2


-- ((169 - (200 - (x + 259))) * x) % 14 ===> (169 * x)% 14
def natMulModCstUnchanged_3 : Expr :=
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
            (Lean.Expr.const `Nat.mod [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 169)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 14))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulModCstUnchanged_3" : term => return natMulModCstUnchanged_3

#testOptimize [ "NatMulModCstUnchanged_3" ] ∀ (x y : Nat), ((169 - (200 - (x + 259))) * x) % 14 < y ===> natMulModCstUnchanged_3


/-! Test cases for simplification rule `n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)` -/

-- x % x ===> 0
-- TODO: remove unused quantifier when COI performed on forall
def natModIdentity_1 : Expr :=
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
elab "natModIdentity_1" : term => return natModIdentity_1

#testOptimize [ "NatModIdentity_1" ] ∀ (x y : Nat), x % x < y ===> natModIdentity_1


-- (m * n) % (n * m) ===> 0
-- TODO: remove unused quantifier when COI performed on forall
def natModIdentity_2 : Expr :=
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
elab "natModIdentity_2" : term => return natModIdentity_2

#testOptimize [ "NatModIdentity_2" ] ∀ (m n y : Nat), (m * n) % (n * m) < y ===> natModIdentity_2

-- (x + (100 - (y + 250))) % x ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatModIdentity_3" ] ∀ (x y : Nat), (x + (100 - (y + 250))) % x < y ===> natModIdentity_1


-- x % (x + ((298 - (x + 350)) % y)) ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatModIdentity_4" ] ∀ (x y : Nat), x % (x + ((298 - (x + 350)) % y)) < y ===> natModIdentity_1



/-! Test cases to ensure that simplification rule `n1 % n2 ==> 0 (if n1 =ₚₜᵣ n2)`
    is not wrongly applied.
-/
-- x % y ===> Nat.mod x y
#testOptimize [ "NatModIdentityUnchanged_1" ] ∀ (x y z : Nat), x % y < z ===>
                                              ∀ (x y z : Nat), Nat.mod x y < z

-- (m * n) % (n * x) ===> Nat.mod (Nat.mul m n) (Nat.mul n x)
#testOptimize [ "NatModIdentityUnchanged_2" ] ∀ (m n x y : Nat), (m * n) % (n * x) < y ===>
                                              ∀ (m n x y : Nat), Nat.mod (Nat.mul m n) (Nat.mul n x) < y

-- (y + (100 - (y + 250))) % x ===> Nat.mod y x
#testOptimize [ "NatModIdentityUnchanged_3" ] ∀ (x y z : Nat), (y + (100 - (y + 250))) % x < z ===>
                                              ∀ (x y z : Nat), Nat.mod y x < z

-- x % (y + ((298 - (x + 350)) % x)) ===> Nat.mod x y
#testOptimize [ "NatModIdentityUnchanged_4" ] ∀ (x y z : Nat), x % (y + ((298 - (x + 350)) % x)) < z ===>
                                              ∀ (x y z : Nat), Nat.mod x y < z


/-! Test cases for the following simplification rules:
      - `(m * n) % m ==> 0`
      - `(n * m) % m ==> 0`
-/

-- (x * y) % y ===> 0
-- TODO: remove unused quantifier when COI performed on forall
def natMulModReduce_1 : Expr :=
 (Lean.Expr.forallE `z
   (Lean.Expr.const `Nat [])
   (Lean.Expr.app
     (Lean.Expr.app
       (Lean.Expr.app
         (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
         (Lean.Expr.const `instLTNat []))
       (Lean.Expr.lit (Lean.Literal.natVal 0)))
     (Lean.Expr.bvar 0))
   (Lean.BinderInfo.default))
elab "natMulModReduce_1" : term => return natMulModReduce_1

#testOptimize [ "NatMulModReduce_1" ] ∀ (x y z : Nat), (x * y) % y < z ===> natMulModReduce_1

-- (x * y) % y = 0 ===> True
#testOptimize [ "NatMulModReduce_2" ] ∀ (x y : Nat), (x * y) % y = 0 ===> True

-- (y * x) % y ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulModReduce_3" ] ∀ (y x z : Nat), (y * x) % y < z ===> natMulModReduce_1

-- (y * x) % y = 0 ===> True
#testOptimize [ "NatMulModReduce_4" ] ∀ (y x : Nat), (y * x) % y = 0 ===> True

-- (y * x) % (y + 0) = 0 ===> True
#testOptimize [ "NatMulModReduce_5" ] ∀ (y x : Nat), (y * x) % (y + 0) = 0 ===> True

-- (y * x) % (y + (z - z)) = 0 ===> True
#testOptimize [ "NatMulModReduce_6" ] ∀ (y x z : Nat), (y * x) % (y + (z - z)) = 0 ===> True

-- ((y + 0) * x) % (y + (z - z)) = 0 ===> True
#testOptimize [ "NatMulModReduce_7" ] ∀ (y x z : Nat), ((y + 0) * x) % (y + (z - z)) = 0 ===> True



/-! Test cases to ensure that the following simplification rules are not wrongly applied
      - `(m * n) % m ==> 0`
      - `(n * m) % m ==> 0`
-/

-- (x * y) % z ===> (x * y) % z
#testOptimize [ "NatMulModReduceUnchanged_1" ] ∀ (x y z : Nat), (x * y) % z < z ===>
                                               ∀ (x y z : Nat), Nat.mod (Nat.mul x y) z < z

-- (y * x) % z ===> (y * x) % z
#testOptimize [ "NatMulModReduceUnchanged_2" ] ∀ (y x z : Nat), (y * x) % z < z ===>
                                               ∀ (y x z : Nat), Nat.mod (Nat.mul y x) z < z

-- (y * x) % (y + z) ===> Nat.div (Nat.mul x y) (Nat.add y z)
#testOptimize [ "NatMulModReduceUnchanged_3" ] ∀ (x y z : Nat), (y * x) % (y + z) < z ===>
                                               ∀ (x y z : Nat), Nat.mod (Nat.mul x y) (Nat.add y z) < z



/-! Test cases to ensure that `Nat.div` is preserved when expected and is not a commutative operator. -/
-- x % y ===> x % y
#testOptimize [ "NatModVar_1" ] ∀ (x y z : Nat), x % y < z ===> ∀ (x y z : Nat), Nat.mod x y < z

-- x % y = x % y ===> True
#testOptimize [ "NatModVar_2" ] ∀ (x y : Nat), x % y = x % y ===> True

-- x % (y % 0) ===> x % y
#testOptimize [ "NatModVar_3" ] ∀ (x y z : Nat), x % (y % 0) < z ===> ∀ (x y z : Nat), Nat.mod x y < z

-- (x % 0) % y ===> x % y
#testOptimize [ "NatModVar_4" ] ∀ (x y z : Nat), (x % 0) % y < z ===> ∀ (x y z : Nat), Nat.mod x y < z

-- (x % 0) % (y % y) = x % (y % y) ===> True
#testOptimize [ "NatModVar_5" ] ∀ (x y : Nat), (x % 0) % (y % y) = x % (y % y) ===> True

-- (x % 10) % y = (x % (15 - 5)) % y ===> True
#testOptimize [ "NatModVar_6" ] ∀ (x y : Nat), (x % 10) % y = (x % (15 - 5)) % y ===> True

-- (x % 10) % y ===> (x % 10) % y
def natModVar_7 : Expr :=
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
              (Lean.Expr.const `Nat.mod [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.mod []) (Lean.Expr.bvar 2))
                (Lean.Expr.lit (Lean.Literal.natVal 10))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.bvar 0))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natModVar_7" : term => return natModVar_7

#testOptimize [ "NatModVar_7" ] ∀ (x y z : Nat), (x % 10) % y < z ===> natModVar_7


/-! Test cases to ensure that constant propagation is properly performed
    when `Nat.mod` operands are reduced to constant values via optimizaton. -/

variable (x : Nat)
variable (y : Nat)
variable (z : Nat)

-- (((x * y) % y) - x) % z ===> 0
def natModReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natModReduce_1" : term => return natModReduce_1

#testOptimize [ "NatModReduce_1" ] (((x * y) % y) - x) % z ===>  natModReduce_1


-- (30 + (x % 1)) % ((((120 * x) % 12) % 10) - x) ===> 30
def natModReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 30)
elab "natModReduce_2" : term => return natModReduce_2

#testOptimize [ "NatModReduce_2" ]  (30 + (x % 1)) % ((((120 * x) % 12) % 10) - x) ===> natModReduce_2

end Test.OptimizeNatMod
