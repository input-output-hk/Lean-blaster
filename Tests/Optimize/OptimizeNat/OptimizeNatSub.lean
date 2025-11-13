import Lean
import Tests.Utils

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

-- x - (x + (100 - (200 + x))) = 0 ===> True
#testOptimize [ "NatSubReduceZero_7" ] ∀ (x : Nat), x - (x + (100 - (200 + x))) = 0 ===> True


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

-- (y + (100 - (200 + x))) - x ===> Nat.sub y x
#testOptimize [ "NatSubReduceZeroUnchanged_4" ] ∀ (x y z : Nat), (y + (100 - (200 + x))) - x < z ===>
                                                ∀ (x y z : Nat), Nat.sub y x < z


/-! Test cases for simplification rule `0 - n ===> 0`. -/

-- 0 - x = 0 ===> True
#testOptimize [ "NatSubLeftZero_1" ] ∀ (x : Nat), 0 - x = 0 ===> True

-- 0 - x ===> 0
#testOptimize [ "NatSubLeftZero_2" ] ∀ (x y : Nat), (0 - x) + x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- Nat.zero - x = 0 ===> True
#testOptimize [ "NatSubLeftZero_3" ] ∀ (x : Nat), Nat.zero - x = 0 ===> True

-- Nat.zero - x ===> 0
#testOptimize [ "NatSubLeftZero_4" ] ∀ (x y : Nat), (Nat.zero - x) + x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- (27 - 27) - x ===> 0
#testOptimize [ "NatSubLeftZero_5" ] ∀ (x y : Nat), ((27 - 27) - x) + x ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- (127 - 145) - x ===> 0
#testOptimize [ "NatSubLeftZero_6" ] ∀ (x y : Nat), ((127 - 145) - x) + x ≤ y ===> ∀ (x y : Nat), ¬ y < x

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
#testOptimize [ "NatSubRightZero_3" ] ∀ (x y : Nat), x - 0 ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- x - Nat.zero ===> x
#testOptimize [ "NatSubRightZero_4" ] ∀ (x y : Nat), x - Nat.zero ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- x - 0 ===> x
#testOptimize [ "NatSubRightZero_5" ] ∀ (x y : Nat), x - 0 ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- x - (27 - 27) ===> x
#testOptimize [ "NatSubRightZero_6" ] ∀ (x y : Nat), x - (27 - 27) ≤ y ===> ∀ (x y : Nat), ¬ y < x

-- x - (27 - 145) ===> x
#testOptimize [ "NatSubRightZero_7" ] ∀ (x y : Nat), x - (27 - 145) ≤ y ===> ∀ (x y : Nat), ¬ y < x

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


/-! Test cases for simplification rule `N1 - (N2 + n) ===> (N1 "-" N2) - n`. -/

-- 120 - (40 + x) = 80 - x ===> True
#testOptimize [ "NatSubAdd_1" ] ∀ (x : Nat), 120 - (40 + x) = 80 - x ===> True

-- 120 - (40 + x) ===> 80 - x
def natSubAdd_2 : Expr :=
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

elab "natSubAdd_2" : term => return natSubAdd_2

#testOptimize [ "NatSubAdd_2" ] ∀ (x y : Nat), 120 - (40 + x) < y ===> natSubAdd_2

-- 120 - (x + 40) = 80 - x ===> True
#testOptimize [ "NatSubAdd_3" ] ∀ (x : Nat), 120 - (x + 40) = 80 - x ===> True

-- 120 - (140 + x) = 0 ===> True
#testOptimize [ "NatSubAdd_4" ] ∀ (x : Nat), 120 - (140 + x) = 0 ===> True

-- 120 - (10 + (30 + x)) = 80 - x ===> True
#testOptimize [ "NatSubAdd_5" ] ∀ (x : Nat), 120 - (10 + (30 + x)) = 80 - x ===> True

-- 120 - (10 + (x + 30)) = 80 - x ===> True
#testOptimize [ "NatSubAdd_6" ] ∀ (x : Nat), 120 - (10 + (x + 30)) = 80 - x ===> True

-- 120 - (10 - (50 + x)) = 120 ===> True
#testOptimize [ "NatSubAdd_7" ] ∀ (x : Nat), 120 - (10 - (50 + x)) = 120 ===> True

-- (250 - (150 + x)) - 20 = 80 - x ===> True
#testOptimize [ "NatSubAdd_8" ] ∀ (x : Nat), (250 - (150 + x)) - 20 = 80 - x ===> True

-- 120 - (10 + (5 + (25 + x))) = 80 - x ===> True
#testOptimize [ "NatSubAdd_9" ] ∀ (x : Nat), 120 - (10 + (5 + (25 + x))) = 80 - x ===> True

-- 120 - (10 + (150 - (100 + x))) = 110 - (50 - x) ===> True
#testOptimize [ "NatSubAdd_10" ] ∀ (x : Nat), 120 - (10 + (150 - (100 + x))) = 110 - (50 - x) ===> True

-- 120 - (10 + (50 - (x + 100))) = 110 ===> True
#testOptimize [ "NatSubAdd_11" ] ∀ (x : Nat), 120 - (10 + (50 - (x + 100))) = 110 ===> True

-- 120 - (25 + ((x - 3) - 2)) = 95 - (x - 5) ===> True
#testOptimize [ "NatSubAdd_12" ] ∀ (x : Nat), 120 - (25 + ((x - 3) - 2)) = 95 - (x - 5) ===> True


/-! Test cases to ensure that simplification rule `N1 - (N2 + n) ===> (N1 "-" N2) - n`
    is not applied wrongly.
-/

-- 120 - (x - y) ===> 120 - (x - y)
-- Must remain unchanged
def natSubAddUnchanged_1 : Expr :=
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

elab "natSubAddUnchanged_1" : term => return natSubAddUnchanged_1

#testOptimize [ "NatSubAddUnchanged_1" ] ∀ (x y : Nat), 120 - (x - y) < y ===> natSubAddUnchanged_1

-- 120 - (x + y) ===> 120 - (x + y)
-- Must remain unchanged
def natSubAddUnchanged_2 : Expr :=
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

elab "natSubAddUnchanged_2" : term => return natSubAddUnchanged_2

#testOptimize [ "NatSubAddUnchanged_2" ] ∀ (x y : Nat), 120 - (x + y) < y ===> natSubAddUnchanged_2

-- 120 - (x * y) ===> 120 - (x * y)
-- Must remain unchanged
def natSubAddUnchanged_3 : Expr :=
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

elab "natSubAddUnchanged_3" : term => return natSubAddUnchanged_3

#testOptimize [ "NatSubAddUnchanged_3" ] ∀ (x y : Nat), 120 - (x * y) < y ===> natSubAddUnchanged_3

-- 120 - (30 - x) ===> 120 - (30 - x)
-- Must remain unchanged
def natSubAddUnchanged_4 : Expr :=
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
               (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 30)))
               (Lean.Expr.bvar 1))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubAddUnchanged_4" : term => return natSubAddUnchanged_4

#testOptimize [ "NatSubAddUnchanged_4" ] ∀ (x y : Nat), 120 - (30 - x) < y ===> natSubAddUnchanged_4

/-! Test cases for simplification rule `(N1 - n) - N2 ===> (N1 "-" N2) - n`. -/

-- (20 - x) - 10 = 10 - x ===> True
#testOptimize [ "NatSubSubLeft_1" ] ∀ (x : Nat), (20 - x) - 10 = 10 - x ===> True

-- (20 - x) - 10 ===> 10 - x
def natSubSubLeft_2 : Expr :=
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

elab "natSubSubLeft_2" : term => return natSubSubLeft_2

#testOptimize [ "NatSubSubLeft_2" ] ∀ (x y : Nat), (20 - x) - 10 < y ===> natSubSubLeft_2

-- (45 - x) - 125 = 0 ===> True
#testOptimize [ "NatSubSubLeft_3" ] ∀ (x : Nat), (45 - x) - 125 = 0 ===> True

-- ((20 - x) - 5) - 10 = 5 - x ===> True
#testOptimize [ "NatSubSubLeft_4" ] ∀ (x : Nat), ((20 - x) - 5) - 10 = 5 - x ===> True

-- 10 - ((20 - x) - 5) = 10 - (15 - x) ===> True
#testOptimize [ "NatSubSubLeft_5" ] ∀ (x : Nat), 10 - ((20 - x) - 5) = 10 - (15 - x) ===> True

-- (20 - (3 + x)) - 10 = 7 - x ===> True
#testOptimize [ "NatSubSubLeft_6" ] ∀ (x : Nat), (20 - (3 + x)) - 10 = 7 - x ===> True

-- 20 - ((15 - (x + 10)) - 2) = 20 - (3 - x) ===> True
#testOptimize [ "NatSubSubLeft_7" ] ∀ (x : Nat), (20 - ((15 - (x + 10)) - 2)) = 20 - (3 - x) ===> True

-- 20 - (((30 - x) - 4) - 10) = 20 - (16 - x) ===> True
#testOptimize [ "NatSubSubLeft_8" ] ∀ (x : Nat), 20 - (((30 - x) - 4) - 10) = 20 - (16 - x) ===> True

-- ((200 - (150 + x)) - 20) - 10 = 20 - x ===> True
#testOptimize [ "NatSubSubLeft_9" ] ∀ (x : Nat), ((200 - (150 + x)) - 20) - 10 = 20 - x ===> True


/-! Test cases for simplification rule `(n - N1) - N2 ===> n - (N1 "+" N2)`. -/

-- (x - 20) - 10 = x - 30 ===> True
#testOptimize [ "NatSubSubRight_1" ] ∀ (x : Nat), (x - 20) - 10 = x - 30 ===> True

-- (x - 20) - 10 ===> x - 30
def natSubSubRight_2 : Expr :=
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

elab "natSubSubRight_2" : term => return natSubSubRight_2

#testOptimize [ "NatSubSubRight_2" ] ∀ (x y : Nat), (x - 20) - 10 < y ===> natSubSubRight_2

-- ((x - 100) - 45) - 125 = x - 270 ===> True
#testOptimize [ "NatSubSubRight_3" ] ∀ (x : Nat), ((x - 100) - 45) - 125 = x - 270 ===> True

-- ((200 - x) - 45) - 125 = 30 - x ===> True
#testOptimize [ "NatSubSubRight_4" ] ∀ (x : Nat), ((200 - x) - 45) - 125 = 30 - x ===> True

-- ((100 - x) - 45) - 125 = 0 ===> True
#testOptimize [ "NatSubSubRight_5" ] ∀ (x : Nat), ((100 - x) - 45) - 125 = 0 ===> True

-- ((x - 200) - 45) - ((125 - x) - 130) = x - 245 ===> True
#testOptimize [ "NatSubSubRight_6" ] ∀ (x : Nat), ((x - 200) - 45) - ((125 - x) - 130) = x - 245 ===> True

-- (((x - 60) - 40) - 45) - 125 = x - 270 ===> True
#testOptimize [ "NatSubSubRight_7" ] ∀ (x : Nat), (((x - 60) - 40) - 45) - 125 = x - 270 ===> True

-- (100 - ((x - 100) - 45)) = 100 - (x - 145) ===> True
#testOptimize [ "NatSubSubRight_8" ] ∀ (x : Nat), (100 - ((x - 100) - 45)) = 100 - (x - 145) ===> True


/-! Test cases for simplification rule `(N1 + n) - N2 ===> (N1 "-" N2) + n` (if N1 ≥ N2). -/

-- (100 + x) - 20 = 80 + x
#testOptimize [ "NatAddSub_1" ] ∀ (x : Nat), (100 + x) - 20 = 80 + x ===> True

-- (100 + x) - 20 ===> 80 + x
def natAddSub_2 : Expr :=
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

elab "natAddSub_2" : term => return natAddSub_2

#testOptimize [ "NatAddSub_2" ] ∀ (x y : Nat), (100 + x) - 20 < y ===> natAddSub_2

-- (120 + x) - 120 = x ===> True
#testOptimize [ "NatAddSub_3" ] ∀ (x : Nat), (120 + x) - 120 = x ===> True

-- ((200 + x) - 120) - 20 = 60 + x ===> True
#testOptimize [ "NatAddSub_4" ] ∀ (x : Nat), ((200 + x) - 120) - 20 = 60 + x ===> True

-- (50 + (100 + x)) - 120 = 30 + x ===> True
#testOptimize [ "NatAddSub_5" ] ∀ (x : Nat), (50 + (100 + x)) - 120 = 30 + x ===> True

-- (50 + (40 + (x + 60))) - 120 = 30 + x ===> True
#testOptimize [ "NatAddSub_6" ] ∀ (x : Nat), (50 + (40 + (x + 60))) - 120 = 30 + x ===> True

-- (((230 + x) - 20) - 120) - 40 = 50 + x ===> True
#testOptimize [ "NatAddSub_7" ] ∀ (x : Nat), (((230 + x) - 20) - 120) - 40 = 50 + x ===> True

-- (((x + 180) - 100) - 20) + 120 = 180 + x ===> True
#testOptimize [ "NatAddSub_8" ] ∀ (x : Nat), (((x + 180) - 100) - 20) + 120 = 180 + x ===> True

/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `(N1 - n) - N2 ===> (N1 "-" N2) - n`
     - `(n - N1) - N2 ===> n - (N1 "+" N2)`
     - `(N1 + n) - N2 ===> (N1 "-" N2) + n` (if N1 ≥ N2)
-/

-- (x - y) - 120 ===> (x - y) - 120
-- Must remain unchanged
def natSubSubUnchanged_1 : Expr :=
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

elab "natSubSubUnchanged_1" : term => return natSubSubUnchanged_1

#testOptimize [ "NatSubSunUnchanged_1" ] ∀ (x y : Nat), (x - y) - 120 < y ===> natSubSubUnchanged_1

-- (x + y) - 120 ===> (x + y) - 120
-- Must remain unchanged
def natSubSubUnchanged_2 : Expr :=
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

elab "natSubSubUnchanged_2" : term => return natSubSubUnchanged_2

#testOptimize [ "NatSubSunUnchanged_2" ] ∀ (x y : Nat), (x + y) - 120 < y ===> natSubSubUnchanged_2

-- (x * y) - 120  ===> (x * y) - 120
-- Must remain unchanged
def natSubSubUnchanged_3 : Expr :=
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

elab "natSubSubUnchanged_3" : term => return natSubSubUnchanged_3

#testOptimize [ "NatSubSunUnchanged_3" ] ∀ (x y : Nat), (x * y) - 120 < y ===> natSubSubUnchanged_3

-- 100 - (10 - x) ===> 100 - (10 - x)
-- Must remain unchanged
def natSubSubUnchanged_4 : Expr :=
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
               (Lean.Expr.lit (Lean.Literal.natVal 100)))
               (Lean.Expr.app
                 (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
                 (Lean.Expr.bvar 1))))
         (Lean.Expr.bvar 0))
     (Lean.BinderInfo.default))
    (Lean.BinderInfo.default)

elab "natSubSubUnchanged_4" : term => return natSubSubUnchanged_4

#testOptimize [ "NatSubSunUnchanged_4" ] ∀ (x y : Nat), 100 - (10 - x) < y ===> natSubSubUnchanged_4


-- (100 + x) - 101 ===> (100 + x) - 101
-- Must remain unchanged
def natSubSubUnchanged_5 : Expr :=
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
            (Lean.Expr.const `Nat.sub [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 100)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 101))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natSubSubUnchanged_5" : term => return natSubSubUnchanged_5

#testOptimize [ "NatSubSunUnchanged_5" ] ∀ (x y : Nat), (100 + x) - 101 < y ===> natSubSubUnchanged_5

-- (100 + x) - 180 ===> (100 + x) - 180
-- Must remain unchanged
def natSubSubUnchanged_6 : Expr :=
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
            (Lean.Expr.const `Nat.sub [])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 100)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.lit (Lean.Literal.natVal 180))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "natSubSubUnchanged_6" : term => return natSubSubUnchanged_6

#testOptimize [ "NatSubSunUnchanged_6" ] ∀ (x y : Nat), (100 + x) - 180 < y ===> natSubSubUnchanged_6


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


/-! Test cases to ensure that constant propagation is properly performed
    when `Nat.sub` operands are reduced to constant values via optimization.
-/

variable (x : Nat)
variable (y : Nat)

-- (100 + ((180 - (x + 40)) - 150)) - ((200 - y) - 320) ===> 100
def natSubReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "natSubReduce_1" : term => return natSubReduce_1

#testOptimize [ "NatSubReduce_1" ] (100 + ((180 - (x + 40)) - 150)) - ((200 - y) - 320) ===> natSubReduce_1

def natSubReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 76)
elab "natSubReduce_2" : term => return natSubReduce_2

-- (100 + ((180 - (x + 40)) - 150)) - (((20 - y) - 50) + 24) ===> 76
#testOptimize [ "NatSubReduce_2" ] (100 + ((180 - (x + 40)) - 150)) - (((20 - y) - 50) + 24)  ===> natSubReduce_2

end Test.OptimizeNatSub
