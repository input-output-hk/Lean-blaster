import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatAdd

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.add -/

/-! Test cases for `reduceApp` rule on ``Nat.add. -/

-- 0 + 10 ===> 10
def natAddCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 10)
elab "natAddCst_1" : term => return natAddCst_1

-- 12 + 0 ===> 12
def natAddCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 12)
elab "natAddCst_2" : term => return natAddCst_2

#testOptimize [ "NatAddCst_2" ] (12 : Nat) + 0 ===> natAddCst_2

-- 123 + 50 ===> 173
def natAddCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 173)
elab "natAddCst_3" : term => return natAddCst_3

#testOptimize [ "NatAddCst_3" ] (123 : Nat) + 50 ===> natAddCst_3


/-! Test cases for simplification rule `0 + n ===> n`. -/

-- x + 0 ===> x
#testOptimize [ "NatAddZero_1" ] ∀ (x y : Nat), x + 0 ≤ y ===> ∀ (x y : Nat), x ≤ y

-- 0 + x ===> x
#testOptimize [ "NatAddZero_2" ] ∀ (x y : Nat), 0 + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x + Nat.zero ===> x
#testOptimize [ "NatAddZero_3" ] ∀ (x y : Nat), x + Nat.zero ≤ y ===> ∀ (x y : Nat), x ≤ y

-- Nat.zero + x ===> x
#testOptimize [ "NatAddZero_4" ] ∀ (x y : Nat), Nat.zero + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- (10 - 10) + x ===> x
#testOptimize [ "NatAddZero_5" ] ∀ (x y : Nat), (10 - 10) + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x + (10 - 123) ===> x
#testOptimize [ "NatAddZero_6" ] ∀ (x y : Nat), x + (10 - 123) ≤ y ===> ∀ (x y : Nat), x ≤ y


-- 1 + x ===> 1 + x
def natAddZeroUnchanged_1 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 1)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddZeroUnchanged_1" : term => return natAddZeroUnchanged_1

#testOptimize [ "NatAddZeroUnchanged_1" ] ∀ (x y : Nat), (1 + x) < y ===> natAddZeroUnchanged_1

-- (27 - 26) + x ===> 1 + x
#testOptimize [ "NatAddZeroUnchanged_2" ] ∀ (x y : Nat), (27 - 26) + x < y ===> natAddZeroUnchanged_1

-- (Nat.zero + 1) + x ===> 1 + x
#testOptimize [ "NatAddZeroUnchanged_3" ] ∀ (x y : Nat), (Nat.zero + 1) + x < y ===> natAddZeroUnchanged_1

-- (127 + 40) + x ===> 167 + x
def natAddZeroUnchanged_4 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 167)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddZeroUnchanged_4" : term => return natAddZeroUnchanged_4

#testOptimize [ "NatAddZeroUnchanged_4" ] ∀ (x y : Nat), (127 + 40) + x < y ===> natAddZeroUnchanged_4


/-! Test cases for simplification rule `N1 + (N2 + n) ===> (N1 "+" N2) + n`. -/

-- 10 + (20 + x) = 30 + x ===> True
#testOptimize [ "NatAddCstProp_1" ] ∀ (x : Nat), 10 + (20 + x) = 30 + x ===> True

-- 10 + (x + 20) = x + 30 ===> True
#testOptimize [ "NatAddCstProp_2" ] ∀ (x : Nat), 10 + (x + 20) = x + 30 ===> True

-- (x + 20) + 10 = 30 + x ===> True
#testOptimize [ "NatAddCstProp_3" ] ∀ (x : Nat), (x + 20) + 10 = 30 + x ===> True

-- (20 + x) + 10 = x + 30 ===> True
#testOptimize [ "NatAddCstProp_4" ] ∀ (x : Nat), (20 + x) + 10 = x + 30 ===> True

-- 10 + (20 + x) ===> (30 + x)
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 30)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_5" : term => return natAddCstProp_5

#testOptimize [ "NatAddCstProp_5" ] ∀ (x y : Nat), 10 + (20 + x) < y ===> natAddCstProp_5

-- 10 + (20 + (40 + x)) = 70 + x ===> True
#testOptimize [ "NatAddCstProp_6" ] ∀ (x : Nat), 10 + (20 + (40 + x)) = 70 + x ===> True

-- 10 + (20 + (x + 40)) = 70 + x ===> True
#testOptimize [ "NatAddCstProp_7" ] ∀ (x : Nat), 10 + (20 + (x + 40)) = 70 + x ===> True

-- 10 + (20 + (x - 10)) = 20 + x ===> True
#testOptimize [ "NatAddCstProp_8" ] ∀ (x : Nat), 10 + (20 + (x - 10)) = 20 + x ===> True

-- 10 + (20 + (10 - x)) = 40 - x ===> True
#testOptimize [ "NatAddCstProp_9" ] ∀ (x : Nat), 10 + (20 + (10 - x)) = 40 - x ===> True

-- 10 + (20 + (15 + (x + 25))) = 70 + x ===> True
#testOptimize [ "NatAddCstProp_10" ] ∀ (x : Nat), 10 + (20 + (15 + (x + 25))) = 70 + x ===> True

-- 10 + (20 + ((x - 3) - 7)) = 20 + x ===> True
#testOptimize [ "NatAddCstProp_11" ] ∀ (x : Nat), 10 + (20 + ((x - 3) - 7)) = 20 + x ===> True

-- 10 + (20 + (100 - (x + 90))) = 40 - x ===> True
#testOptimize [ "NatAddCstProp_12" ] ∀ (x : Nat), 10 + (20 + (100 - (x + 90))) = 40 - x ===> True


/-! Test cases for simplification rule `N1 + (N2 - n) ===> (N1 "+" N2) - n`. -/

-- 10 + (20 - x) = 30 - x ===> True
#testOptimize [ "NatAddCstProp_13" ] ∀ (x : Nat), 10 + (20 - x) = 30 - x ===> True

-- 10 + (20 - x) ===> 30 - x
def natAddCstProp_14 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 30)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_14" : term => return natAddCstProp_14

#testOptimize [ "NatAddCstProp_14" ] ∀ (x y : Nat), 10 + (20 - x) < y  ===> natAddCstProp_14

-- 10 + (20 - (x + 10)) = 20 - x ===> True
#testOptimize [ "NatAddCstProp_15" ] ∀ (x : Nat), 10 + (20 - (x + 10)) = 20 - x ===> True

-- 10 + (20 - (10 + x)) = 20 - x ===> True
#testOptimize [ "NatAddCstProp_16" ] ∀ (x : Nat), 10 + (20 - (10 + x)) = 20 - x ===> True

-- 10 + (20 - (40 + x)) = 10 ===> True
#testOptimize [ "NatAddCstProp_17" ] ∀ (x : Nat), 10 + (20 - (40 + x)) = 10 ===> True

-- 10 + (20 - (10 - x)) = 20 + x ===> True
#testOptimize [ "NatAddCstProp_18" ] ∀ (x : Nat), 10 + (20 - (10 - x)) = 20 + x ===> True

-- 10 + (20 - (50 - x)) = 10 + x ===> True
#testOptimize [ "NatAddCstProp_19" ] ∀ (x : Nat), 10 + (20 - (50 - x)) = 10 + x ===> True

-- 10 + (20 - (x - 50)) = 80 - x ===> True
#testOptimize [ "NatAddCstProp_20" ] ∀ (x : Nat), 10 + (20 - (x - 50)) = 80 - x ===> True

-- 10 + (20 - ((x + 3) + 7)) = 20 - x ===> True
#testOptimize [ "NatAddCstProp_21" ] ∀ (x : Nat), 10 + (20 - ((x + 3) + 7)) = 20 - x ===> True

-- 10 + (20 - (15 + (x + 25))) = 10 ===> True
#testOptimize [ "NatAddCstProp_22" ] ∀ (x : Nat), 10 + (20 - (15 + (x + 25))) = 10 ===> True

-- 10 + (20 - (67 - (x + 57))) = 20 + x ===> True
#testOptimize [ "NatAddCstProp_23" ] ∀ (x : Nat), 10 + (20 - (67 - (x + 57))) = 20 + x ===> True

-- 10 + (20 - (35 + (15 - x))) = 10 + x ===> True
#testOptimize [ "NatAddCstProp_24" ] ∀ (x : Nat), 10 + (20 - (35 + (15 - x))) = 10 + x ===> True

-- 10 + (20 - ((x - 32) - 18)) = 80 - x ===> True
#testOptimize [ "NatAddCstProp_25" ] ∀ (x : Nat), 10 + (20 - ((x - 32) - 18)) = 80 - x ===> True


/-! Test cases for simplification rule `N1 + (n - N2) ===> (N1 "-" N2) + n`. -/

-- 100 + (x - 25) = 75 + x ===> True
#testOptimize [ "NatAddCstProp_26" ] ∀ (x : Nat), 100 + (x - 25) = 75 + x ===> True

-- 100 + (x - 25) ===> 75 + x
def natAddCstProp_27 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 75)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_27" : term => return natAddCstProp_27

#testOptimize [ "NatAddCstProp_27" ] ∀ (x y : Nat), 100 + (x - 25) < y ===> natAddCstProp_27

-- 100 + (x - 100) = x ===> True
#testOptimize [ "NatAddCstProp_28" ] ∀ (x : Nat), 100 + (x - 100) = x ===> True

-- 100 + (x - 125) = x ===> True
#testOptimize [ "NatAddCstProp_29" ] ∀ (x : Nat), 100 + (x - 125) = x ===> True

-- 100 + ((x + 30) - 20) = 110 + x
#testOptimize [ "NatAddCstProp_30" ] ∀ (x : Nat), 100 + ((x + 30) - 20) = 110 + x ===> True

-- 100 + ((30 + x) - 20) = 110 + x
#testOptimize [ "NatAddCstProp_31" ] ∀ (x : Nat), 100 + ((30 + x) - 20) = 110 + x ===> True

-- 100 + ((x + 30) - 140) = 100 + x
#testOptimize [ "NatAddCstProp_33" ] ∀ (x : Nat), 100 + ((x + 30) - 140) = 100 + x ===> True

-- 100 + ((x - 50) - 40) = 10 + x
#testOptimize [ "NatAddCstProp_34" ] ∀ (x : Nat), 100 + ((x - 50) - 40) = 10 + x ===> True

-- 100 + ((x - 50) - 70) = x
#testOptimize [ "NatAddCstProp_35" ] ∀ (x : Nat), 100 + ((x - 50) - 70) = x ===> True

-- 100 + ((120 - x) - 50) = 170 - x
#testOptimize [ "NatAddCstProp_36" ] ∀ (x : Nat), 100 + ((120 - x) - 50) = 170 - x ===> True

-- 100 + ((120 - x) - 150) = 100
#testOptimize [ "NatAddCstProp_37" ] ∀ (x : Nat), 100 + ((120 - x) - 150) = 100 ===> True

-- 100 + (((x + 10) + 20) - 20) = 110 + x
#testOptimize [ "NatAddCstProp_38" ] ∀ (x : Nat), 100 + (((x + 10) + 20) - 20) = 110 + x ===> True

-- 100 + ((130 - (100 - x)) - 20) = 110 + x
#testOptimize [ "NatAddCstProp_39" ] ∀ (x : Nat), 100 + ((130 - (100 - x)) - 20) = 110 + x ===> True

-- 100 + (((x + 130) - 100) - 140) = 100 + x
#testOptimize [ "NatAddCstProp_40" ] ∀ (x : Nat), 100 + (((x + 130) - 100) - 140) = 100 + x ===> True

-- 100 + (((x - 20) - 30) - 40) = 10 + x
#testOptimize [ "NatAddCstProp_41" ] ∀ (x : Nat), 100 + (((x - 20) - 30) - 40) = 10 + x ===> True

-- 100 + ((50 + (70 - x)) - 50) = 170 - x
#testOptimize [ "NatAddCstProp_42" ] ∀ (x : Nat), 100 + ((50 + (70 - x)) - 50) = 170 - x ===> True

-- 100 + ((180 - (x + 40)) - 150) = 100
#testOptimize [ "NatAddCstProp_43" ] ∀ (x : Nat), 100 + ((180 - (x + 40)) - 150) = 100 ===> True


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `N1 + (N2 + n) ===> (N1 "+" N2) + n`
     - `N1 + (N2 - n) ===> (N1 "+" N2) - n`
     - `N1 + (n - N2) ===> (N1 "-" N2) + n`
-/

-- 40 + (x + y) ===> 40 + (x + y)
-- Must remain unchanged
def natAddCstProp_44 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_44" : term => return natAddCstProp_44

#testOptimize [ "NatAddCstProp_44" ] ∀ (x y : Nat), 40 + (x + y) < y ===> natAddCstProp_44


-- 40 + (x - y) ===> 40 + (x - y)
-- Must remain unchanged
def natAddCstProp_45 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_45" : term => return natAddCstProp_45

#testOptimize [ "NatAddCstProp_45" ] ∀ (x y : Nat), 40 + (x - y) < y ===> natAddCstProp_45


-- 40 + (x * y) ===> 40 + (x * y)
-- Must remain unchanged
def natAddCstProp_46 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add [])
               (Lean.Expr.lit (Lean.Literal.natVal 40)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCstProp_46" : term => return natAddCstProp_46

#testOptimize [ "NatAddCstProp_46" ] ∀ (x y : Nat), 40 + (x * y) < y ===> natAddCstProp_46


/-! Test cases for normalization rule `n1 + n2 ==> n2 + n1 (if n2 <ₒ n1)`. -/

-- x + y = x + y ===> True
#testOptimize [ "NatAddCommut_1" ] ∀ (x y : Nat), x + y = x + y ===> True

-- x + y = y + x ===> True
#testOptimize [ "NatAddCommut_2" ] ∀ (x y : Nat), x + y = y + x ===> True

-- x + 10 = 10 + x ===> True
#testOptimize [ "NatAddCommut_3" ] ∀ (x : Nat), x + 10 = 10 + x ===> True

-- y + x ===> x + y (with `x` declared first)
#testOptimize [ "NatAddCommut_4" ] ∀ (x y z : Nat), z < y + x ===> ∀ (x y z : Nat), z < Nat.add x y

-- x + 40 ===> 40 + x
def natAddCommut_5 : Expr :=
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
          (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 40)))
          (Lean.Expr.bvar 1)))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddCommut_5" : term => return natAddCommut_5

#testOptimize [ "NatAddCommut_5" ] ∀ (x y : Nat), y < x + 40 ===> natAddCommut_5

-- (x + (y + 20)) + z = z + ((y + 20) + x) ===> True
#testOptimize [ "NatAddCommut_6" ] ∀ (x y z : Nat), (x + (y + 20)) + z = z + ((y + 20) + x) ===> True

--- (x - y) + (p + q) ===> (p + q) + (x - y)
#testOptimize [ "NatAddCommut_7" ] ∀ (x y z p q : Nat), (x - y) + (p + q) < z ===>
                                   ∀ (x y z p q : Nat), Nat.add (Nat.add p q) (Nat.sub x y) < z

--- (x - y) + (p + q) = (p + q) + (x - y) ===> True
#testOptimize [ "NatAddCommut_8" ] ∀ (x y p q : Nat), (x - y) + (p + q) = (p + q) + (x - y) ===> True


/-! Test cases to ensure that `Nat.add` is preserved when expected. -/

-- x + (y + 0) = y + x ===> True
#testOptimize [ "NatAddVar_1" ] ∀ (x y : Nat), x + (y + 0) = y + x ===> True

-- (x + 0) + y = y + x ===> True
#testOptimize [ "NatAddVar_2" ] ∀ (x y : Nat), (x + 0) + y = y + x ===> True

-- (x + 0) + (y + 0) = y + x ===> True
#testOptimize [ "NatAddVar_3" ] ∀ (x y : Nat), (x + 0) + (y + 0) = y + x ===> True

-- x + y < 10 ===> x + y < 10
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.bvar 1))
             (Lean.Expr.bvar 0)))
         (Lean.Expr.lit (Lean.Literal.natVal 10)))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natAddVar_4" : term => return natAddVar_4

#testOptimize [ "NatAddVar_4" ] ∀ (x y : Nat), x + y < 10 ===> natAddVar_4


/-! Test cases to ensure that `reduceApp` is properly called
    when `Nat.add` operands are reduced to constant values
    via optimization. -/

opaque x : Nat
opaque y : Nat

-- (100 + ((180 - (x + 40)) - 150)) + ((200 - y) - 320) ===> 100
def natAddReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "natAddReduce_1" : term => return natAddReduce_1

#testOptimize [ "NatAddReduce_1" ] (100 + ((180 - (x + 40)) - 150)) + ((200 - y) - 320) ===> natAddReduce_1

def natAddReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 124)
elab "natAddReduce_2" : term => return natAddReduce_2

-- (100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24) ===> 124
#testOptimize [ "NatAddReduce_2" ] (100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24)  ===> natAddReduce_2

end Test.OptimizeNatAdd
