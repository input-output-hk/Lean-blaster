import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatAdd

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.add -/

/-! Test cases for `reduceApp` rule on ``Nat.add. -/

-- 0 + 10 ===> 10
def natAddCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 10)
elab "natAddCst_1" : term => return natAddCst_1

#testOptimize [ "NatAddCst_1" ] (0 : Nat) + 10 ===> natAddCst_1

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



/-! Test cases to ensure that simplification rules `0 + n ===> n` is not wrongly applied. -/

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

-- 10 + ((x + 20) - 10) = 20 + x ===> True
#testOptimize [ "NatAddCstProp_8" ] ∀ (x : Nat), 10 + ((x + 20) - 10) = 20 + x ===> True

-- 10 + (20 + (15 + (x + 25))) = 70 + x ===> True
#testOptimize [ "NatAddCstProp_9" ] ∀ (x : Nat), 10 + (20 + (15 + (x + 25))) = 70 + x ===> True

-- 10 + (20 + ((x + 10) - 7)) = 33 + x ===> True
#testOptimize [ "NatAddCstProp_10" ] ∀ (x : Nat), 10 + (20 + ((x + 10) - 7)) = 33 + x ===> True

-- 100 + ((180 - (x + 40)) - 150) = 100
#testOptimize [ "NatAddCstProp_11" ] ∀ (x : Nat), 100 + ((180 - (x + 40)) - 150) = 100 ===> True


/-! Test cases to ensure that simplification rule `N1 + (N2 + n) ===> (N1 "+" N2) + n`
    is not wrongly applied.
-/

-- 40 + (x + y) ===> 40 + (x + y)
-- Must remain unchanged
def natAddCstPropUnchanged_1 : Expr :=
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

elab "natAddCstPropUnchanged_1" : term => return natAddCstPropUnchanged_1

#testOptimize [ "NatAddCstPropUnchanged_1" ] ∀ (x y : Nat), 40 + (x + y) < y ===> natAddCstPropUnchanged_1


-- 40 + (x - y) ===> 40 + (x - y)
-- Must remain unchanged
def natAddCstPropUnchanged_2 : Expr :=
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

elab "natAddCstPropUnchanged_2" : term => return natAddCstPropUnchanged_2

#testOptimize [ "NatAddCstPropUnchanged_2" ] ∀ (x y : Nat), 40 + (x - y) < y ===> natAddCstPropUnchanged_2


-- 40 + (x * y) ===> 40 + (x * y)
-- Must remain unchanged
def natAddCstPropUnchanged_3 : Expr :=
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

elab "natAddCstPropUnchanged_3" : term => return natAddCstPropUnchanged_3

#testOptimize [ "NatAddCstPropUnchanged_3" ] ∀ (x y : Nat), 40 + (x * y) < y ===> natAddCstPropUnchanged_3


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

variable (x : Nat)
variable (y : Nat)

-- (100 + ((180 - (x + 40)) - 150)) + ((200 - y) - 320) ===> 100
def natAddReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 100)
elab "natAddReduce_1" : term => return natAddReduce_1

#testOptimize [ "NatAddReduce_1" ] (100 + ((180 - (x + 40)) - 150)) + ((200 - y) - 320) ===> natAddReduce_1

def natAddReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 124)
elab "natAddReduce_2" : term => return natAddReduce_2

-- (100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24) ===> 124
#testOptimize [ "NatAddReduce_2" ] (100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24)  ===> natAddReduce_2

end Test.OptimizeNatAdd
