import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatMul

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.mul -/

/-! Test cases for `reduceApp` rule on ``Nat.mul. -/

-- 0 * 432 ===> 0
def natMulCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natMulCst_1" : term => return natMulCst_1

#testOptimize [ "NatMulCst_1" ] (0 : Nat) * 432 ===> natMulCst_1

-- 432 * 0 ===> 0
#testOptimize [ "NatMulCst_2" ] 432 * (0 : Nat) ===> natMulCst_1

def natMulCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 432)
elab "natMulCst_3" : term => return natMulCst_3

-- 432 * 1 ===> 32
#testOptimize [ "NatMulCst_3" ] 432 * (1 : Nat) ===> natMulCst_3

-- 1 * 432 ===> 32
#testOptimize [ "NatMulCst_4" ] 1 * (432 : Nat) ===> natMulCst_3

-- 34 * 432 ===> 14688
def natMulCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 14688)
elab "natMulCst_5" : term => return natMulCst_5

#testOptimize [ "NatMulCst_5" ] (34 : Nat) * 432 ===> natMulCst_5


/-! Test cases for simplification rule `0 * n ==> 0`. -/

-- x * 0 ===> 0
def natMulZero_1 : Expr :=
(Lean.Expr.forallE `y
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.const `instLENat []))
      (Lean.Expr.lit (Lean.Literal.natVal 0)))
    (Lean.Expr.bvar 0))
  (Lean.BinderInfo.default))
elab "natMulZero_1" : term => return natMulZero_1

#testOptimize [ "NatMulZero_1" ] ∀ (x y : Nat), x * 0 ≤ y ===> natMulZero_1

-- 0 * x ===> 0
#testOptimize [ "NatMulZero_2" ] ∀ (x y : Nat), 0 * x ≤ y ===> natMulZero_1

-- 0 * x = 0 ===> True
#testOptimize [ "NatMulZero_3" ] ∀ (x : Nat), 0 * x = 0 ===> True

-- x * Nat.zero ===> 0
#testOptimize [ "NatMulZero_4" ] ∀ (x y : Nat), x * Nat.zero ≤ y ===> natMulZero_1

-- Nat.zero * x ===> 0
#testOptimize [ "NatMulZero_5" ] ∀ (x y : Nat), Nat.zero * x ≤ y ===> natMulZero_1

-- Nat.zero * x = 0 ===> True
#testOptimize [ "NatMulZero_6" ] ∀ (x : Nat), Nat.zero * x = 0 ===> True

-- (10 - 10) * x ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulZero_7" ] ∀ (x y : Nat), (10 - 10) * x ≤ y ===> natMulZero_1

-- x * (10 - 123) ===> 0
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulZero_8" ] ∀ (x y : Nat), x * (10 - 123) ≤ y ===> natMulZero_1

-- x * (y - y) = 0 ===> True
#testOptimize [ "NatMulZero_9" ] ∀ (x y : Nat), x * (y - y) = 0 ===> True


/-! Test cases for simplification rule `1 * n ==> n`. -/

-- 1 * n ===> n
#testOptimize [ "NatMulOne_1" ] ∀ (x y : Nat), x * 1 ≤ y ===> ∀ (x y : Nat), x ≤ y

-- n * 1 ===> n
#testOptimize [ "NatMulOne_2" ] ∀ (x y : Nat), 1 * x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- 1 * x = x ===> True
#testOptimize [ "NatMulOne_3" ] ∀ (x : Nat), 1 * x = x ===> True

-- (10 - 9) * x ===> x
#testOptimize [ "NatMulOne_4" ] ∀ (x y : Nat), (10 - 9) * x < y ===> ∀ (x y : Nat), x < y

-- ((((Nat.succ y) - 1) - y) + 1) * x ===> x
#testOptimize [ "NatMulOne_5" ] ∀ (x y z : Nat), ((((Nat.succ y) - 1) - y) + 1) * x < z ===>
                                ∀ (x z : Nat), x < z



/-! Test cases to ensure that the following simplification rules are not wrongly applied:
      - `0 * n ==> 0`
      - `1 * n ==> n`
-/

-- x * 10 ===> 10 * x
-- TODO: remove unused quantifier when COI performed on forall
def natMulCstUnchanged_1 : Expr :=
Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `y
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
          (Lean.Expr.bvar 1)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "natMulCstUnchanged_1" : term => return natMulCstUnchanged_1

#testOptimize [ "NatMulCstUnchanged_1" ] ∀ (x y : Nat), x * 10 ≤ y ===> natMulCstUnchanged_1

-- (100 - 90) * x ===> 10 * x
-- TODO: remove unused quantifier when COI performed on forall
#testOptimize [ "NatMulCstUnchanged_2" ] ∀ (x y : Nat), (100 - 90) * x ≤ y ===> natMulCstUnchanged_1

-- x * (y - z) ===> Nat.mul x (Nat.sub y z)
#testOptimize [ "NatMulCstUnchanged_3" ] ∀ (x y z m : Nat), x * (y - z) < m ===>
                                         ∀ (x y z m : Nat), Nat.mul x (Nat.sub y z) < m


/-! Test cases for simplification rule `N1 * (N2 * n) ===> (N1 "*" N2) * n`. -/

-- 10 * (20 * x) = 200 * x ===> True
#testOptimize [ "NatMulCstProp_1" ] ∀ (x : Nat), 10 * (20 * x) = 200 * x ===> True

-- 10 * (x * 20) = x * 200 ===> True
#testOptimize [ "NatMulCstProp_2" ] ∀ (x : Nat), 10 * (x * 20) = x * 200 ===> True

-- (x * 20) * 10 = 30 * x ===> True
#testOptimize [ "NatMulCstProp_3" ] ∀ (x : Nat), (x * 20) * 10 = 200 * x ===> True

-- (20 * x) * 10 = x * 30 ===> True
#testOptimize [ "NatMulCstProp_4" ] ∀ (x : Nat), (20 * x) * 10 = x * 200 ===> True

-- 10 * (20 * x) ===> (200 * x)
def natAddCstProp_5 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 200)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_5" : term => return natAddCstProp_5

#testOptimize [ "NatMulCstProp_5" ] ∀ (x y : Nat), 10 * (20 * x) < y ===> natAddCstProp_5

-- 10 * (2 * (40 * x)) = 800 * x ===> True
#testOptimize [ "NatMulCstProp_6" ] ∀ (x : Nat), 10 * (2 * (40 * x)) = 800 * x ===> True

-- 10 * (2 * (x * 40)) = 800 * x ===> True
#testOptimize [ "NatMulCstProp_7" ] ∀ (x : Nat), 10 * (2 * (x * 40)) = 800 * x ===> True

-- 10 * (20 * (x - 10)) = 200 * (x - 10) ===> True
#testOptimize [ "NatMulCstProp_8" ] ∀ (x : Nat), 10 * (20 * (x - 10)) = 200 * (x - 10)===> True

-- 10 * (20 * (10 - x)) = 200 * (10 - x) ===> True
#testOptimize [ "NatMulCstProp_9" ] ∀ (x : Nat), 10 * (20 * (10 - x)) = 200 * (10 - x) ===> True

-- 10 * (2 * (5 * (x * 25))) = 2500 * x ===> True
#testOptimize [ "NatMulCstProp_10" ] ∀ (x : Nat), 10 * (2 * (5 * (x * 25))) = 2500 * x ===> True

-- 10 * (20 * ((x - 3) - 7)) = 200 * (x - 10) ===> True
#testOptimize [ "NatMulCstProp_11" ] ∀ (x : Nat), 10 * (20 * ((x - 3) - 7)) = 200 * (x - 10) ===> True

-- 10 * (20 * (100 - (x + 190))) = 0 ===> True
#testOptimize [ "NatMulCstProp_12" ] ∀ (x : Nat), 10 * (20 * (100 - (x + 190))) = 0 ===> True


/-! Test cases to ensure that simplification rule `N1 * (N2 * n) ===> (N1 "*" N2) * n` is not
    wrongly applied.
-/

-- 40 * (x * y) ===> 40 * (x * y)
-- Must remain unchanged
def natMulCstPropUnchanged_1 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.mul [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natMulCstPropUnchanged_1" : term => return natMulCstPropUnchanged_1

#testOptimize [ "NatMulCstPropUnchanged_1" ] ∀ (x y : Nat), 40 * (x * y) < y ===> natMulCstPropUnchanged_1


-- 40 * (x - y) ===> 40 * (x - y)
-- Must remain unchanged
def natMulCstPropUnchanged_2 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.mul [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natMulCstPropUnchanged_2" : term => return natMulCstPropUnchanged_2

#testOptimize [ "NatMulCstPropUnchanged_2" ] ∀ (x y : Nat), 40 * (x - y) < y ===> natMulCstPropUnchanged_2


-- 40 * (x + y) ===> 40 * (x + y)
-- Must remain unchanged
def natMulCstPropUnchanged_3 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.mul [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natMulCstPropUnchanged_3" : term => return natMulCstPropUnchanged_3

#testOptimize [ "NatMulCstPropUnchanged_3" ] ∀ (x y : Nat), 40 * (x + y) < y ===> natMulCstPropUnchanged_3



/-! Test cases for normalization rule `n1 * n2 ==> n2 * n1 (if n2 <ₒ n1)`. -/

-- x * y = x * y ===> True
#testOptimize [ "NatMulCommut_1" ] ∀ (x y : Nat), x * y = x * y ===> True

-- x * y = y * x ===> True
#testOptimize [ "NatMulCommut_2" ] ∀ (x y : Nat), x * y = y * x ===> True

-- x * 10 = 10 * x ===> True
#testOptimize [ "NatMulCommut_3" ] ∀ (x : Nat), x * 10 = 10 * x ===> True

-- y * x ===> x * y (with `x` declared first)
#testOptimize [ "NatMulCommut_4" ] ∀ (x y z : Nat), z < y * x ===> ∀ (x y z : Nat), z < Nat.mul x y

-- x * 40 ===> 40 * x
def natMulCommut_5 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `y
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 40)))
          (Lean.Expr.bvar 1)))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natMulCommut_5" : term => return natMulCommut_5

#testOptimize [ "NatMulCommut_5" ] ∀ (x y : Nat), y < x * 40 ===> natMulCommut_5

-- (x * (y * 20)) * z = z * ((y * 20) * x) ===> True
#testOptimize [ "NatMulCommut_6" ] ∀ (x y z : Nat), (x * (y * 20)) * z = z * ((y * 20) * x) ===> True

--- (x - y) * (p + q) ===> (p + q) * (x - y)
#testOptimize [ "NatMulCommut_7" ] ∀ (x y z p q : Nat), (x - y) * (p + q) < z ===>
                                   ∀ (x y z p q : Nat), Nat.mul (Nat.add p q) (Nat.sub x y) < z

--- (x - y) * (p + q) = (p + q) * (x - y) ===> True
#testOptimize [ "NatMulCommut_8" ] ∀ (x y p q : Nat), (x - y) * (p + q) = (p + q) * (x - y) ===> True


/-! Test cases to ensure that `Nat.mul` is preserved when expected. -/

-- x * (y * 1) = x * y ===> True
#testOptimize [ "NatMulVar_1" ] ∀ (x y : Nat), x * (y * 1) = x * y ===> True

-- (x * 1) * y = x * y ===> True
#testOptimize [ "NatMulVar_2" ] ∀ (x y : Nat), (x * 1) * y = x * y ===> True

-- (x * 1) * (y * 1) = y * x ===> True
#testOptimize [ "NatMulVar_3" ] ∀ (x y : Nat), (x * 1) * (y * 1) = y * x ===> True

-- x * y < 10 ===> x * y < 10
def natAddVar_4 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1))
             (Lean.Expr.bvar 0)))
         (Lean.Expr.lit (Lean.Literal.natVal 10)))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddVar_4" : term => return natAddVar_4

#testOptimize [ "NatMulVar_4" ] ∀ (x y : Nat), x * y < 10 ===> natAddVar_4


/-! Test cases to ensure that `reduceApp` is properly called
    when `Nat.mul` operands are reduced to constant values via optimization. -/

opaque x : Nat
opaque y : Nat

-- (100 * (30 - ((180 - (x * 1)) - 150))) * ((320 - (y + 400)) - y) ===> 0
#testOptimize [ "NatMulReduce_1" ] (100 * (30 - ((180 - (x * 1)) - 150))) * ((320 - (y + 400)) - y) ===> natMulCst_1

-- (100 * (((180 - (x * 40)) - 150) - 30)) * ((((20 - y) - 50) * 24) + 1) ===> 100
def natMulReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "natMulReduce_2" : term => return natMulReduce_2

#testOptimize [ "NatMulReduce_2" ] (100 + (((180 - (x * 40)) - 150) - 30)) * ((((20 - y) - 50) * 24) + 1) ===> natMulReduce_2


end Test.OptimizeNatMul
