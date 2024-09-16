import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatSub

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.sub -/


/-! Test cases for `reduceApp` rule  on ``Nat.sub. -/

-- 123 - 50 ===> 73
def natSubCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 73)
elab "natSubCst_1" : term => return natSubCst_1

#testOptimize [ "NatSubCst_1" ] (123 : Nat) - 50 ===> natSubCst_1

-- 123 - 0 ===> 123
def natSubCst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 123)
elab "natSubCst_2" : term => return natSubCst_2

#testOptimize [ "NatSubCst_2" ] (123 : Nat) - 0 ===> natSubCst_2

def natSubCst_3 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natSubCst_3" : term => return natSubCst_3
-- 0 - 1 ===> 0
#testOptimize [ "NatSubCst_3" ] (0 : Nat) - 1 ===> natSubCst_3

-- 0 - 5 ===> 0
#testOptimize [ "NatSubCst_4" ] (0 : Nat) - 5 ===> natSubCst_3

-- 123 - 124 ===> 0
#testOptimize [ "NatSubCst_5" ] (123 : Nat) - 124 ===> natSubCst_3

-- 123 - 300 ===> 0
#testOptimize [ "NatSubCst_6" ] (123 : Nat) - 300 ===> natSubCst_3


/-! Test cases for simplification rule `n1 - n2 ==> 0 (if n1 =ₚₜᵣ n2)`. -/

-- x - x ===> 0
def natSubReduceZero_1 : Expr :=
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

elab "natSubReduceZero_1" : term => return natSubReduceZero_1

#testOptimize [ "NatSubReduceZero_1" ] ∀ (x y : Nat), y > x - x ===> natSubReduceZero_1

-- x - x = 0 ===> True
#testOptimize [ "NatSubReduceZero_2" ] ∀ (x : Nat), x - x = 0 ===> True

-- (x + y) - (y + x) = 0 ===> True
#testOptimize [ "NatSubReduceZero_3" ] ∀ (x y : Nat), (x + y) - (y + x) = 0 ===> True

-- (x - y) - (x - y) = 0 ===> True
#testOptimize [ "NatSubReduceZero_4" ] ∀ (x y : Nat), (x - y) - (x - y) = 0 ===> True

-- (x + 0) - x = 0 ===> True
#testOptimize [ "NatSubReduceZero_5" ] ∀ (x : Nat), (x + 0) - x = 0 ===> True

-- x - (x + 0) = 0 ===> True
#testOptimize [ "NatSubReduceZero_6" ] ∀ (x : Nat), x - (x + 0) = 0 ===> True

-- ((x + 100) - 200) - x = 0 ===> True
#testOptimize [ "NatSubReduceZero_7" ] ∀ (x : Nat), ((x + 100) - 200) - x = 0 ===> True

-- x - ((x + 100) - 200) = 0 ===> True
#testOptimize [ "NatSubReduceZero_8" ] ∀ (x : Nat), x - ((x + 100) - 200) = 0 ===> True



/-! Test cases to ensure that simplification rule `n1 - n2 ==> 0 (if n1 =ₚₜᵣ n2)` is not wrongly applied. -/

-- x - y ===> Nat.sub x y
#testOptimize [ "NatSubReduceZeroUnchanged_1" ] ∀ (x y z : Nat), z > x - y ===>
                                                ∀ (x y z : Nat), Nat.sub x y < z
-- (x + y) - z ===> Nat.sub (Nat.add x y) z
#testOptimize [ "NatSubReduceZeroUnchanged_2" ] ∀ (x y z m : Nat), (x + y) - z < m ===>
                                                ∀ (x y z m : Nat), Nat.sub (Nat.add x y) z < m

-- (x - y) - z ===> Nat.sub (Nat.sub x y) z
#testOptimize [ "NatSubReduceZeroUnchanged_3" ] ∀ (x y z m : Nat), (x - y) - z < m ===>
                                                ∀ (x y z m : Nat), Nat.sub (Nat.sub x y) z < m

-- ((y + 100) - 200) - x ===> Nat.sub y x
#testOptimize [ "NatSubReduceZeroUnchanged_4" ] ∀ (x y z : Nat), ((y + 100) - 200) - x < z ===>
                                                ∀ (x y z : Nat), Nat.sub y x < z


/-! Test cases for simplification rule `0 - n ===> 0`. -/

-- 0 - x = 0 ===> True
#testOptimize [ "NatSubLeftZero_1" ] ∀ (x : Nat), 0 - x = 0 ===> True

-- 0 - x ===> 0
#testOptimize [ "NatSubLeftZero_2" ] ∀ (x y : Nat), (0 - x) + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- Nat.zero - x = 0 ===> True
#testOptimize [ "NatSubLeftZero_3" ] ∀ (x : Nat), Nat.zero - x = 0 ===> True

-- Nat.zero - x ===> 0
#testOptimize [ "NatSubLeftZero_4" ] ∀ (x y : Nat), (Nat.zero - x) + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- (27 - 27) - x ===> 0
#testOptimize [ "NatSubLeftZero_5" ] ∀ (x y : Nat), ((27 - 27) - x) + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- (127 - 145) - x ===> 0
#testOptimize [ "NatSubLeftZero_6" ] ∀ (x y : Nat), ((127 - 145) - x) + x ≤ y ===> ∀ (x y : Nat), x ≤ y

-- 1 - x ===> 1 - x
def natSubLeftZeroUnchanged_1 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 1)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubLeftZeroUnchanged_1" : term => return natSubLeftZeroUnchanged_1

#testOptimize [ "NatSubLeftZeroUnchanged_1" ] ∀ (x y : Nat), (1 - x) < y ===> natSubLeftZeroUnchanged_1

-- (27 - 26) - x ===> 1 - x
#testOptimize [ "NatSubLeftZeroUnchanged_2" ] ∀ (x y : Nat), (27 - 26) - x < y ===> natSubLeftZeroUnchanged_1

-- (Nat.zero + 1) - x ===> 1 - x
#testOptimize [ "NatSubLeftZeroUnchanged_3" ] ∀ (x y : Nat), (Nat.zero + 1) - x < y ===> natSubLeftZeroUnchanged_1

-- (127 - 40) - x ===> 87 - x
def natSubLeftZeroUnchanged_4 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 87)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubLeftZeroUnchanged_4" : term => return natSubLeftZeroUnchanged_4

#testOptimize [ "NatSubLeftZeroUnchanged_4" ] ∀ (x y : Nat), (127 - 40) - x < y ===> natSubLeftZeroUnchanged_4


/-! Test cases for simplification rule `n - 0 ===> n`. -/

-- x - 0 = x ===> x
#testOptimize [ "NatSubRightZero_1" ] ∀ (x : Nat), x - 0 = x ===> True

-- x - Nat.zero = x ===> x
#testOptimize [ "NatSubRightZero_2" ] ∀ (x : Nat), x - Nat.zero = x ===> True

-- x - 0 ===> x
#testOptimize [ "NatSubRightZero_3" ] ∀ (x y : Nat), x - 0 ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x - Nat.zero ===> x
#testOptimize [ "NatSubRightZero_4" ] ∀ (x y : Nat), x - Nat.zero ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x - 0 ===> x
#testOptimize [ "NatSubRightZero_5" ] ∀ (x y : Nat), x - 0 ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x - (27 - 27) ===> x
#testOptimize [ "NatSubRightZero_6" ] ∀ (x y : Nat), x - (27 - 27) ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x - (27 - 145) ===> x
#testOptimize [ "NatSubRightZero_7" ] ∀ (x y : Nat), x - (27 - 145) ≤ y ===> ∀ (x y : Nat), x ≤ y

-- x - 1 ===> x - 1
def natSubRightZeroUnchanged_1 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
             (Lean.Expr.lit (Lean.Literal.natVal 1))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubRightZeroUnchanged_1" : term => return natSubRightZeroUnchanged_1

#testOptimize [ "NatSubRightZeroUnchanged_1" ] ∀ (x y : Nat), (x - 1) < y ===> natSubRightZeroUnchanged_1

-- x - (127 - 126) ===> x - 1
#testOptimize [ "NatSubRightZeroUnchanged_2" ] ∀ (x y : Nat), x - (127 - 126) < y ===> natSubRightZeroUnchanged_1

-- x - (Nat.zero + 1) ===> x - 1
#testOptimize [ "NatSubRightZeroUnchanged_3" ] ∀ (x y : Nat), x - (Nat.zero + 1) < y ===> natSubRightZeroUnchanged_1

-- x - (127 - 40) ===> x - 87
def natSubRightZeroUnchanged_4 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
             (Lean.Expr.lit (Lean.Literal.natVal 87))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubRightZeroUnchanged_4" : term => return natSubRightZeroUnchanged_4

#testOptimize [ "NatSubRightZeroUnchanged_4" ] ∀ (x y : Nat), x - (127 - 40) < y ===> natSubRightZeroUnchanged_4


/-! Test cases for simplification rule `N1 - (N2 - n) ===> (N1 "-" N2) + n`. -/

-- 120 - (50 - x) = 70 + x ===> True
#testOptimize [ "NatSubCstProp_1" ] ∀ (x : Nat), 120 - (50 - x) = 70 + x ===> True

-- 120 - (50 - x) ===> 70 + x
def natSubCstProp_2 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 70)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_2" : term => return natSubCstProp_2

#testOptimize [ "NatSubCstProp_2" ] ∀ (x y : Nat), 120 - (50 - x) < y ===> natSubCstProp_2

-- 120 - (150 - x)) = x ===> True
#testOptimize [ "NatSubCstProp_3" ] ∀ (x : Nat), 120 - (150 - x) = x ===> True

-- 120 - (40 - (30 - x)) = 110 - x ===> True
#testOptimize [ "NatSubCstProp_4" ] ∀ (x : Nat), 120 - (40 - (30 - x)) = 110 - x ===> True

-- 120 - (40 - (x + 30)) = 110 + x ===> True
#testOptimize [ "NatSubCstProp_5" ] ∀ (x : Nat), 120 - (40 - (x + 30)) = 110 + x ===> True

-- 120 - (40 - (50 + x)) = 120 ===> True
#testOptimize [ "NatSubCstProp_6" ] ∀ (x : Nat), 120 - (40 - (50 + x)) = 120 ===> True

-- 420 - (40 - (x - 150)) = 230 + x ===> True
#testOptimize [ "NatSubCstProp_7" ] ∀ (x : Nat), 420 - (40 - (x - 150)) = 230 + x ===> True

-- 120 - (40 - (x - 150)) = x ===> True
#testOptimize [ "NatSubCstProp_8" ] ∀ (x : Nat), 120 - (40 - (x - 150)) = x ===> True

-- 120 - (40 - (10 - (x - 20))) = 110 - x ===> True
#testOptimize [ "NatSubCstProp_9" ] ∀ (x : Nat), 120 - (40 - (10 - (x - 20))) = 110 - x ===> True

-- 120 - (40 - (50 - (20 - x))) = 110 + x ===> True
#testOptimize [ "NatSubCstProp_10" ] ∀ (x : Nat), 120 - (40 - (50 - (20 - x))) = 110 + x ===> True

-- 120 - (40 - (20 + (30 + x))) = 120 ===> True
#testOptimize [ "NatSubCstProp_11" ] ∀ (x : Nat), 120 - (40 - (20 + (30 + x))) = 120 ===> True

-- 420 - (40 - ((x - 50) - 100)) = 230 + x ===> True
#testOptimize [ "NatSubCstProp_12" ] ∀ (x : Nat), 420 - (40 - ((x - 50) - 100)) = 230 + x ===> True

-- 120 - (40 - ((x - 10) - 400)) = x ===> True
#testOptimize [ "NatSubCstProp_13" ] ∀ (x : Nat), 120 - (40 - ((x - 10) - 400)) = x ===> True


/-! Test cases for simplification rule `N1 - (n - N2) ===> (N1 "+" N2) - n`. -/

-- 120 - (x - 50) = 170 - x ===> True
#testOptimize [ "NatSubCstProp_14" ] ∀ (x : Nat), 120 - (x - 50) = 170 - x ===> True

-- 120 - (x - 50) ===> 170 - x
def natSubCstProp_15 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 170)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_15" : term => return natSubCstProp_15

#testOptimize [ "NatSubCstProp_15" ] ∀ (x y : Nat), 120 - (x - 50) < y ===> natSubCstProp_15

-- 120 - ((x - 10) - 50) = 180 - x ===> True
#testOptimize [ "NatSubCstProp_16" ] ∀ (x : Nat), 120 - ((x - 10) - 50) = 180 - x ===> True

-- 120 - ((60 - x) - 50) = 110 + x ===> True
#testOptimize [ "NatSubCstProp_17" ] ∀ (x : Nat), 120 - ((60 - x) - 50) = 110 + x ===> True

-- 120 - ((10 - x) - 50) = 120 ===> True
#testOptimize [ "NatSubCstProp_18" ] ∀ (x : Nat), 120 - ((10 - x) - 50) = 120 ===> True

-- 120 - ((x + 100) - 50) = 70 - x ===> True
#testOptimize [ "NatSubCstProp_19" ] ∀ (x : Nat), 120 - ((x + 100) - 50) = 70 - x ===> True

-- 120 - ((100 + x) - 50) = 70 - x ===> True
#testOptimize [ "NatSubCstProp_20" ] ∀ (x : Nat), 120 - ((100 + x) - 50) = 70 - x ===> True

-- 120 - ((10 + x) - 50) = 120 - x ===> True
#testOptimize [ "NatSubCstProp_21" ] ∀ (x : Nat), 120 - ((10 + x) - 50) = 120 - x ===> True


-- 120 - (((x - 3) - 7) - 50) = 180 - x ===> True
#testOptimize [ "NatSubCstProp_22" ] ∀ (x : Nat), 120 - (((x - 3) - 7) - 50) = 180 - x ===> True

-- 120 - ((20 + (40 - x)) - 50) = 110 + x ===> True
#testOptimize [ "NatSubCstProp_23" ] ∀ (x : Nat), 120 - ((20 + (40 - x)) - 50) = 110 + x ===> True

-- 120 - ((50 - (x + 40)) - 50) = 120 ===> True
#testOptimize [ "NatSubCstProp_24" ] ∀ (x : Nat), 120 - ((10 - (x + 40)) - 50) = 120 ===> True

-- 120 - ((200 - (100 - x)) - 50) = 70 - x ===> True
#testOptimize [ "NatSubCstProp_25" ] ∀ (x : Nat), 120 - ((200 - (100 - x)) - 50) = 70 - x ===> True

-- 120 - ((40 - (30 + x)) - 50) = 120 ===> True
#testOptimize [ "NatSubCstProp_26" ] ∀ (x : Nat), 120 - ((40 - (30 + x)) - 50) = 120 ===> True


/-! Test cases for simplification rule `N1 - (N2 + n) ===> (N1 "-" N2) - n`. -/

-- 120 - (40 + x) = 80 - x ===> True
#testOptimize [ "NatSubCstProp_27" ] ∀ (x : Nat), 120 - (40 + x) = 80 - x ===> True

-- 120 - (40 + x) ===> 80 - x
def natSubCstProp_28 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 80)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_28" : term => return natSubCstProp_28

#testOptimize [ "NatSubCstProp_28" ] ∀ (x y : Nat), 120 - (40 + x) < y ===> natSubCstProp_28

-- 120 - (x + 40) = 80 - x ===> True
#testOptimize [ "NatSubCstProp_29" ] ∀ (x : Nat), 120 - (x + 40) = 80 - x ===> True

-- 120 - (140 + x) = 0 ===> True
#testOptimize [ "NatSubCstProp_30" ] ∀ (x : Nat), 120 - (140 + x) = 0 ===> True

-- 120 - (10 + (30 + x)) = 80 - x ===> True
#testOptimize [ "NatSubCstProp_31" ] ∀ (x : Nat), 120 - (10 + (30 + x)) = 80 - x ===> True

-- 120 - (10 + (x + 30)) = 80 - x ===> True
#testOptimize [ "NatSubCstProp_32" ] ∀ (x : Nat), 120 - (10 + (x + 30)) = 80 - x ===> True

-- 120 - (10 + (50 - x)) = 60 + x ===> True
#testOptimize [ "NatSubCstProp_33" ] ∀ (x : Nat), 120 - (10 + (50 - x)) = 60 + x ===> True

-- 120 - (10 + (150 - x)) = x ===> True
#testOptimize [ "NatSubCstProp_34" ] ∀ (x : Nat), 120 - (10 + (150 - x)) = x ===> True

-- 120 - (25 + (x - 5)) = 100 - x ===> True
#testOptimize [ "NatSubCstProp_35" ] ∀ (x : Nat), 120 - (25 + (x - 5)) = 100 - x ===> True

-- 120 - (25 + (x - 35)) = 120 - x ===> True
#testOptimize [ "NatSubCstProp_36" ] ∀ (x : Nat), 120 - (25 + (x - 35)) = 120 - x ===> True

-- 120 - (10 + (5 + (25 + x))) = 80 - x ===> True
#testOptimize [ "NatSubCstProp_37" ] ∀ (x : Nat), 120 - (10 + (5 + (25 + x))) = 80 - x ===> True

-- 120 - (10 + (150 - (100 + x))) = 60 + x ===> True
#testOptimize [ "NatSubCstProp_38" ] ∀ (x : Nat), 120 - (10 + (150 - (100 + x))) = 60 + x ===> True

-- 120 - (10 + (50 - (x - 100))) = x ===> True
#testOptimize [ "NatSubCstProp_39" ] ∀ (x : Nat), 120 - (10 + (50 - (x - 100))) = x ===> True

-- 120 - (25 + ((x - 3) - 2)) = 100 - x ===> True
#testOptimize [ "NatSubCstProp_40" ] ∀ (x : Nat), 120 - (25 + ((x - 3) - 2)) = 100 - x ===> True


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `N1 - (N2 - n) ===> (N1 "-" N2) + n`
     - `N1 - (n - N2) ===> (N1 "+" N2) - n`
     - `N1 - (N2 + n) ===> (N1 "-" N2) - n`
-/

-- 120 - (x - y) ===> 120 - (x - y)
-- Must remain unchanged
def natSubCstProp_41 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 120)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_41" : term => return natSubCstProp_41

#testOptimize [ "NatSubCstProp_41" ] ∀ (x y : Nat), 120 - (x - y) < y ===> natSubCstProp_41

-- 120 - (x + y) ===> 120 - (x + y)
-- Must remain unchanged
def natSubCstProp_42 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 120)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_42" : term => return natSubCstProp_42

#testOptimize [ "NatSubCstProp_42" ] ∀ (x y : Nat), 120 - (x + y) < y ===> natSubCstProp_42

-- 120 - (x * y) ===> 120 - (x * y)
-- Must remain unchanged
def natSubCstProp_43 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 120)))
             (Lean.Expr.app
               (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1))
               (Lean.Expr.bvar 0))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_43" : term => return natSubCstProp_43

#testOptimize [ "NatSubCstProp_43" ] ∀ (x y : Nat), 120 - (x * y) < y ===> natSubCstProp_43


/-! Test cases for simplification rule `(N1 - n) - N2 ===> (N1 "-" N2) - n`. -/

-- (20 - x) - 10 = 10 - x ===> True
#testOptimize [ "NatSubCstProp_44" ] ∀ (x : Nat), (20 - x) - 10 = 10 - x ===> True

-- (20 - x) - 10 ===> 10 - x
def natSubCstProp_45 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_45" : term => return natSubCstProp_45

#testOptimize [ "NatSubCstProp_45" ] ∀ (x y : Nat), (20 - x) - 10 < y ===> natSubCstProp_45

-- (45 - x) - 125 = 0 ===> True
#testOptimize [ "NatSubCstProp_46" ] ∀ (x : Nat), (45 - x) - 125 = 0 ===> True

-- (20 - (5 - x)) - 10 = 5 + x ===> True
#testOptimize [ "NatSubCstProp_47" ] ∀ (x : Nat), (20 - (5 - x)) - 10 = 5 + x ===> True

-- (20 - (x - 5)) - 10 = 15 - x ===> True
#testOptimize [ "NatSubCstProp_48" ] ∀ (x : Nat), (20 - (x - 5)) - 10 = 15 - x ===> True

-- (20 - (x + 5)) - 10 = 5 - x ===> True
#testOptimize [ "NatSubCstProp_49" ] ∀ (x : Nat), (20 - (x + 5)) - 10 = 5 - x ===> True

-- (20 - (3 + x)) - 10 = 7 - x ===> True
#testOptimize [ "NatSubCstProp_50" ] ∀ (x : Nat), (20 - (3 + x)) - 10 = 7 - x ===> True

-- (20 - (15 - (x + 10))) - 10 = 5 + x ===> True
#testOptimize [ "NatSubCstProp_51" ] ∀ (x : Nat), (20 - (15 - (x + 10))) - 10 = 5 + x ===> True

-- (20 - ((x - 1) - 4)) - 10 = 15 - x ===> True
#testOptimize [ "NatSubCstProp_52" ] ∀ (x : Nat), (20 - ((x - 1) - 4)) - 10 = 15 - x ===> True

-- (20 - ((x + 25) - 20)) - 10 = 5 - x ===> True
#testOptimize [ "NatSubCstProp_53" ] ∀ (x : Nat), (20 - ((x + 25) - 20)) - 10 = 5 - x ===> True

-- (20 - (100 - (150 - x))) - 10 = 10 - x ===> True
#testOptimize [ "NatSubCstProp_54" ] ∀ (x : Nat), (20 - (100 - (150 - x))) - 10 = 10 - x ===> True


/-! Test cases for simplification rule `(n - N1) - N2 ===> n - (N1 "+" N2)`. -/

-- (x - 20) - 10 = x - 30 ===> True
#testOptimize [ "NatSubCstProp_55" ] ∀ (x : Nat), (x - 20) - 10 = x - 30 ===> True

-- (x - 20) - 10 ===> x - 30
def natSubCstProp_56 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
             (Lean.Expr.lit (Lean.Literal.natVal 30))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_56" : term => return natSubCstProp_56

#testOptimize [ "NatSubCstProp_56" ] ∀ (x y : Nat), (x - 20) - 10 < y ===> natSubCstProp_56

-- ((x - 100) - 45) - 125 = x - 270 ===> True
#testOptimize [ "NatSubCstProp_57" ] ∀ (x : Nat), ((x - 100) - 45) - 125 = x - 270 ===> True

-- ((200 - x) - 45) - 125 = 30 - x ===> True
#testOptimize [ "NatSubCstProp_58" ] ∀ (x : Nat), ((200 - x) - 45) - 125 = 30 - x ===> True

-- ((100 - x) - 45) - 125 = 0 ===> True
#testOptimize [ "NatSubCstProp_59" ] ∀ (x : Nat), ((100 - x) - 45) - 125 = 0 ===> True

-- ((275 + x) - 45) - 125 = 105 + x ===> True
#testOptimize [ "NatSubCstProp_60" ] ∀ (x : Nat), ((275 + x) - 45) - 125 = 105 + x ===> True

-- ((30 + x) - 45) - 125 = x - 125 ===> True
#testOptimize [ "NatSubCstProp_61" ] ∀ (x : Nat), ((30 + x) - 45) - 125 = x - 125 ===> True

-- ((x + 220) - 45) - 125 = x + 50 ===> True
#testOptimize [ "NatSubCstProp_62" ] ∀ (x : Nat), ((x + 220) - 45) - 125 = x + 50 ===> True

-- ((x + 120) - 45) - 125 = x ===> True
#testOptimize [ "NatSubCstProp_63" ] ∀ (x : Nat), ((x + 120) - 45) - 125 = x ===> True

-- (((x - 60) - 40) - 45) - 125 = x - 270 ===> True
#testOptimize [ "NatSubCstProp_64" ] ∀ (x : Nat), (((x - 60) - 40) - 45) - 125 = x - 270 ===> True

-- ((100 - (x - 100)) - 45) - 125 = 30 - x ===> True
#testOptimize [ "NatSubCstProp_65" ] ∀ (x : Nat), ((100 - (x - 100)) - 45) - 125 = 30 - x ===> True

-- ((100 - (x + 40)) - 45) - 125 = 0 ===> True
#testOptimize [ "NatSubCstProp_66" ] ∀ (x : Nat), ((100 - (x + 40)) - 45) - 125 = 0 ===> True

-- ((375 - (100 - x)) - 45) - 125 = 105 + x ===> True
#testOptimize [ "NatSubCstProp_67" ] ∀ (x : Nat), ((375 - (100 - x)) - 45) - 125 = 105 + x ===> True

-- ((10 + (x + 20)) - 45) - 125 = x - 125 ===> True
#testOptimize [ "NatSubCstProp_68" ] ∀ (x : Nat), ((10 + (x + 20)) - 45) - 125 = x - 125 ===> True

-- (((x + 20) + 200) - 45) - 125 = x + 50 ===> True
#testOptimize [ "NatSubCstProp_69" ] ∀ (x : Nat), (((x + 20) + 200) - 45) - 125 = x + 50 ===> True

-- (((x + 120) - 40) - 45) - 125 = x ===> True
#testOptimize [ "NatSubCstProp_70" ] ∀ (x : Nat), (((x + 120) - 40) - 45) - 125 = x ===> True


/-! Test cases for simplification rule `(N1 + n) - N2 ===> (N1 "-" N2) + n`. -/

-- (100 + x) - 20 = 80 + x
#testOptimize [ "NatSubCstProp_71" ] ∀ (x : Nat), (100 + x) - 20 = 80 + x ===> True

-- (100 + x) - 20 ===> 80 + x
def natSubCstProp_72 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 80)))
             (Lean.Expr.bvar 1)))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_72" : term => return natSubCstProp_72

#testOptimize [ "NatSubCstProp_72" ] ∀ (x y : Nat), (100 + x) - 20 < y ===> natSubCstProp_72

-- (100 + x) - 120 = x ===> True
#testOptimize [ "NatSubCstProp_73" ] ∀ (x : Nat), (100 + x) - 120 = x ===> True

-- (x + 150) - 120 = 30 + x ===> True
#testOptimize [ "NatSubCstProp_74" ] ∀ (x : Nat), (x + 150) - 120 = 30 + x ===> True

-- (50 + (100 + x)) - 120 = 30 + x ===> True
#testOptimize [ "NatSubCstProp_75" ] ∀ (x : Nat), (50 + (100 + x)) - 120 = 30 + x ===> True

-- (50 + (x + 100)) - 120 = 30 + x ===> True
#testOptimize [ "NatSubCstProp_76" ] ∀ (x : Nat), (50 + (100 + x)) - 120 = 30 + x ===> True

-- (50 + (100 - x)) - 120 = 30 - x ===> True
#testOptimize [ "NatSubCstProp_77" ] ∀ (x : Nat), (50 + (100 - x)) - 120 = 30 - x ===> True

-- (50 + (60 - x)) - 120 = 0 ===> True
#testOptimize [ "NatSubCstProp_78" ] ∀ (x : Nat), (50 + (60 - x)) - 120 = 0 ===> True

-- (150 + (x - 20)) - 120 = 10 + x ===> True
#testOptimize [ "NatSubCstProp_79" ] ∀ (x : Nat), (150 + (x - 20)) - 120 = 10 + x ===> True

-- (70 + (x - 20)) - 120 = x ===> True
#testOptimize [ "NatSubCstProp_80" ] ∀ (x : Nat), (70 + (x - 20)) - 120 = x ===> True

-- (50 + (40 + (x + 60))) - 120 = 30 + x ===> True
#testOptimize [ "NatSubCstProp_81" ] ∀ (x : Nat), (50 + (40 + (x + 60))) - 120 = 30 + x ===> True

-- (50 + (70 - (x - 30))) - 120 = 30 - x ===> True
#testOptimize [ "NatSubCstProp_82" ] ∀ (x : Nat), (50 + (70 - (x - 30))) - 120 = 30 - x ===> True

-- (50 + (80 - (x + 20))) - 120 = 0 ===> True
#testOptimize [ "NatSubCstProp_83" ] ∀ (x : Nat), (50 + (80 - (x + 20))) - 120 = 0 ===> True

-- (150 + ((x - 2) - 18)) - 120 = 10 + x ===> True
#testOptimize [ "NatSubCstProp_84" ] ∀ (x : Nat), (150 + ((x - 2) - 18)) - 120 = 10 + x ===> True

-- (70 + (x + 10) - 30)) - 120 = x ===> True
#testOptimize [ "NatSubCstProp_85" ] ∀ (x : Nat), (70 + ((x + 10) - 30)) - 120 = x ===> True


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `(N1 - n) - N2 ===> (N1 "-" N2) - n`
     - `(n - N1) - N2 ===> n - (N1 "+" N2)`
     - `(N1 + n) - N2 ===> (N1 "-" N2) + n`
-/

-- (x - y) - 120 ===> (x - y) - 120
-- Must remain unchanged
def natSubCstProp_86 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub [])
               (Lean.Expr.app
                 (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 1))
                 (Lean.Expr.bvar 0)))
             (Lean.Expr.lit (Lean.Literal.natVal 120))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_86" : term => return natSubCstProp_86

#testOptimize [ "NatSubCstProp_86" ] ∀ (x y : Nat), (x - y) - 120 < y ===> natSubCstProp_86

-- (x + y) - 120 ===> (x + y) - 120
-- Must remain unchanged
def natSubCstProp_87 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub [])
               (Lean.Expr.app
                 (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.bvar 1))
                 (Lean.Expr.bvar 0)))
             (Lean.Expr.lit (Lean.Literal.natVal 120))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_87" : term => return natSubCstProp_87

#testOptimize [ "NatSubCstProp_87" ] ∀ (x y : Nat), (x + y) - 120 < y ===> natSubCstProp_87

-- (x * y) - 120  ===> (x * y) - 120
-- Must remain unchanged
def natSubCstProp_88 : Expr :=
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
             (Lean.Expr.app (Lean.Expr.const `Nat.sub [])
               (Lean.Expr.app
                 (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.bvar 1))
                 (Lean.Expr.bvar 0)))
             (Lean.Expr.lit (Lean.Literal.natVal 120))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubCstProp_88" : term => return natSubCstProp_88

#testOptimize [ "NatSubCstProp_88" ] ∀ (x y : Nat), (x * y) - 120 < y ===> natSubCstProp_88


/-! Test cases to ensure that `Nat.sub` is preserved when expected and is not a commutative operator. -/

-- x - y ===> x - y
#testOptimize [ "NatSubVar_1" ] ∀ (x y z : Nat), x - y < z ===> ∀ (x y z : Nat), Nat.sub x y < z

-- x - y = x - y ===> True
#testOptimize [ "NatSubVar_2" ] ∀ (x y : Nat), x - y = x - y ===> True

-- x - (y - 0) ===> x - y
#testOptimize [ "NatSubVar_3" ] ∀ (x y z : Nat), x - (y - 0) < z ===> ∀ (x y z : Nat), Nat.sub x y < z

-- (x - 0) - y ===> x - y
#testOptimize [ "NatSubVar_4" ] ∀ (x y z : Nat), (x - 0) - y < z ===> ∀ (x y z : Nat), Nat.sub x y < z

-- (x - 0) - (y - 0) = x - y ===> True
#testOptimize [ "NatSubVar_5" ] ∀ (x y : Nat), (x - 0) - (y - 0) = x - y ===> True

-- (x - 10) - y = (x - 10) - y ===> True
#testOptimize [ "NatSubVar_6" ] ∀ (x y : Nat), (x - 10) - y = (x - 10) - y ===> True

-- (x - 10) - y ===> (x - 10) - y
def natSubVar_7 : Expr :=
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
              (Lean.Expr.const `Nat.sub [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.bvar 2))
                (Lean.Expr.lit (Lean.Literal.natVal 10))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.bvar 0))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natSubVar_7" : term => return natSubVar_7

#testOptimize [ "NatSubVar_7" ] ∀ (x y z : Nat), (x - 10) - y < z ===> natSubVar_7


/-! Test cases to ensure that `reduceApp` is properly called
    when `Nat.add` operands are reduced to constant values
    via optimization. -/

opaque x : Nat
opaque y : Nat

-- (100 + ((180 - (x + 40)) - 150)) - ((200 - y) - 320) ===> 100
def natSubReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "natSubReduce_1" : term => return natSubReduce_1

#testOptimize [ "NatSubReduce_1" ] (100 + ((180 - (x + 40)) - 150)) - ((200 - y) - 320) ===> natSubReduce_1

def natSubReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 76)
elab "natSubReduce_2" : term => return natSubReduce_2

-- (100 + ((180 - (x + 40)) - 150)) - (((20 - y) - 50) + 24) ===> 76
#testOptimize [ "NatSubReduce_2" ] (100 + ((180 - (x + 40)) - 150)) - (((20 - y) - 50) + 24)  ===> natSubReduce_2

end Test.OptimizeNatSub
