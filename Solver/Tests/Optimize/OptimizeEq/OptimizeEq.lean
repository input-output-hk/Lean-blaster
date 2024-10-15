import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeEq

/-! ## Test objectives to validate normalization and simplification rules on ``Eq -/

-- False = True ===> False
#testOptimize [ "EqFalseTrue" ] False = True ===> False

-- True = False ===> False
#testOptimize [ "EqTrueFalse" ] True = False ===> False

-- False = a ===> ¬ a
#testOptimize [ "EqFalseLeft" ] ∀ (a : Prop), False = a ===> ∀ (a : Prop), ¬ a

-- a = False ===> ¬ a
#testOptimize [ "EqFalseRight" ] ∀ (a : Prop), a = False ===> ∀ (a : Prop), ¬ a

-- True = a ===> a
#testOptimize [ "EqTrueLeft" ] ∀ (a : Prop), True = a ===> ∀ (a : Prop), a

-- a = True ===> a
#testOptimize [ "EqTrueRight" ] ∀ (a : Prop), a = True ===> ∀ (a : Prop), a

-- a = a ===> True
#testOptimize [ "EqReflexive_1" ] ∀ (a : Prop), a = a ===> True

-- a = (a ∨ a)  ===> True
#testOptimize [ "EqReflexive_2" ] ∀ (a : Prop), a = (a ∨ a) ===> True

-- (a ∨ a) = a ===> True
#testOptimize [ "EqReflexive_3" ] ∀ (a : Prop), (a ∨ a) = a ===> True

-- ((b ∧ ¬ b) ∨ a) = a ===> True
#testOptimize [ "EqReflexive_4" ] ∀ (a b : Prop), ((b ∧ ¬ b) ∨ a) = a ===> True

-- (if c then a else b) = if c then a else b ===> True
#testOptimize [ "EqReflexive_5" ] ∀ (c : Bool) (a b : Prop), (if c then a else b) = if c then a else b ===> True

-- a = ¬ a ===> False
#testOptimize [ "EqNeq_1" ] ∀ (a : Prop), (a = ¬ a) ===> False

-- ¬ a = a ===> False
#testOptimize [ "EqNeq_2" ] ∀ (a : Prop), (¬ a = a) ===> False

-- a = (¬ (¬ a)) ===> True
#testOptimize [ "EqNeq_3" ] ∀ (a : Prop), (a = ¬ (¬ a)) ===> True

-- a = (¬ (¬ (¬ a))) ===> False
#testOptimize [ "EqNeq_4" ] ∀ (a : Prop), (a = ¬ (¬ (¬ a))) ===> False

-- a = ¬ b ===> a = ¬ b
#testOptimize [ "EqNeq_5" ] ∀ (a b : Prop), a = (¬ b) ===> ∀ (a b : Prop), a = (¬ b)

-- ¬ b = a ===> ¬ b = a
-- NOTE: reordering applied on operands
#testOptimize [ "EqNeq_6" ] ∀ (a b : Prop), (¬ b) = a ===> ∀ (a b : Prop), a = (¬ b)

-- a = !a ===> False
#testOptimize [ "EqNot_1" ] ∀ (a : Bool), a = !a ===> False

-- !a = a ===> False
#testOptimize [ "EqNot_2" ] ∀ (a : Bool), (!a) = a ===> False

-- a = (! (! a)) ===> True
#testOptimize [ "EqNot_3" ] ∀ (a : Bool), a = ! (!a) ===> True

-- a = (! (! (! a))) ===> False
#testOptimize [ "EqNot_4" ] ∀ (a : Bool), (a = ! (! (! a))) ===> False

-- a = ! b ===> a = ! b
#testOptimize [ "EqNot_5" ] ∀ (a b : Bool), a = !b ===> ∀ (a b : Bool), a = !b

-- ! b = a ===> ! b = a
-- NOTE: reordering applied on operands
#testOptimize [ "EqNot_6" ] ∀ (a b : Bool), (!b) = a ===> ∀ (a b : Bool), a = !b


-- a = b ===> a = b
#testOptimize [ "EqDiff_1" ] ∀ (a b : Prop), a = b ===> ∀ (a b : Prop), a = b

-- a = (a ∧ b) ===> a = (a ∧ b)
#testOptimize [ "EqDiff_2" ] ∀ (a b : Prop), a = (a ∧ b) ===> ∀ (a b : Prop), a = (a ∧ b)

-- (a ∧ b) = a ===> a = (a ∧ b)
#testOptimize [ "EqDiff_3" ] ∀ (a b : Prop), (a ∧ b) = a ===> ∀ (a b : Prop), a = (a ∧ b)


-- true = false ===> False
#testOptimize [ "EqConstructor_1" ] true = false ===> False

-- true = true ===> True
#testOptimize [ "EqConstructor_2" ] true = true ===> True

-- List.nil = List.nil ===> True
#testOptimize [ "EqConstructor_3" ] List.nil = List.nil ===> True

-- List.nil = [1, 2, 3, 4] ===> False
#testOptimize [ "EqConstructor_4" ] List.nil = [1, 2, 3, 4] ===> False

opaque a : Nat
opaque b : Nat
opaque c : Nat
-- List.nil = [a, b, c] ===> False
#testOptimize [ "EqConstructor_5" ] List.nil = [a, b, c] ===> False

-- [b, a, c] = [a, b, c] ===> [b, a, c] = [a, b, c]
-- Must remain uchanged as we don't know if a = b
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_6" ] [b, a, c] = [a, b, c] ===> [a, b, c] = [b, a, c]

-- [b, a, c] = [a, b] ===> False
#testOptimize [ "EqConstructor_7" ] [b, a, c] = [a, b] ===> False

-- [b, a, c] = [b, a, c] ===> True
#testOptimize [ "EqConstructor_8" ] [b, a, c] = [b, a, c] ===> True

inductive Color where
  | red : Color
  | blue : Color
  | yellow : Color

#testOptimize [ "EqConstructor_9" ] Color.red = Color.red ===> True
#testOptimize [ "EqConstructor_10" ] Color.red = Color.blue ===> False
#testOptimize [ "EqConstructor_11" ] Color.red = Color.yellow ===> False

-- x = Color.red ===> x = Color.red
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_12" ] ∀ (x : Color), x = Color.red ===> ∀ (x : Color), Color.red = x

-- List.nil : List α = List.nil : List α ===> True
#testOptimize [ "EqConstructor_13" ] ∀ (α : Type), (List.nil : List α) = (List.nil : List α) ===> True

-- List.nil = [x, y, z] ===> False
#testOptimize [ "EqConstructor_14" ] ∀ (α : Type) (x y z : α), List.nil = [x, y, z] ===> False

-- [x, y] = [x, y, z] ===> False
#testOptimize [ "EqConstructor_15" ] ∀ (α : Type) (x y z : α), [x, y] = [x, y, z] ===> False

-- [z, y] = [x, y, z] ===> False
#testOptimize [ "EqConstructor_15" ] ∀ (α : Type) (x y z : α), [z, y] = [x, y, z] ===> False

-- [a + b, c] = [a + b, c, b] ===> False
#testOptimize [ "EqConstructor_16" ] [a + b, c] = [a + b, c, b] ===> False

-- [b + a, c] = [a + c, c] ===> [Nat.add b a, c] = [Nat.add a c, c]
-- Must remain unchanged
-- NOTE: reordering applied on operands
-- NOTE: resolving + to Nat.add
#testOptimize [ "EqConstructor_17" ] [b + a, c] = [a + c, c] ===> [Nat.add a b, c] = [Nat.add a c, c]

-- [f x, y] = [f x, y, z] ==> False
#testOptimize [ "EqConstructor_18" ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, y] = [f x, y, z] ===> False

-- [f x, z] = [f y, z] ==> [f x, z] = [f y, z]
-- Must remain unchanged
#testOptimize [ "EqConstructor_19" ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z] ===>
                                     ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z]

-- [b + a, c] = [a + c, c, b] ===> False
-- Must remain unchanged
#testOptimize [ "EqConstructor_20" ] [b + a, c] = [a + c, c, b] ===> False

-- (10 : Nat) = 10 ===> True
#testOptimize [ "EqNatConstructor_1" ] (10 : Nat) = 10 ===> True

-- 10 = 100 ===> False
#testOptimize [ "EqNatConstructor_2" ] (10 : Nat) = 100 ===> False

-- ∀ (x : Nat), (x = 234) ===> ∀ (x : Nat), (x = 234)
-- NOTE: We here provide the internal representation to ensure that 234 is properly reduced to `Expr.lit (Literal.natVal 234)`
def eqNatConstructor_3 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
        (Lean.Expr.lit (Lean.Literal.natVal 234)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "eqNatConstructor_3" : term => return eqNatConstructor_3

-- [50 - a, b] = [10 - a, b] ===> [Nat.sub 50 a, b] = [Nat.sub 10 a, b]
-- Must remain unchanged
-- NOTE: reordering applied on commutative operators (e.g., Eq)
def eqNatConstructor_4 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
      (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
            (Lean.Expr.const `Test.OptimizeEq.a [])))
       (Lean.Expr.app
         (Lean.Expr.app
           (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
           (Lean.Expr.const `Test.OptimizeEq.b []))
         (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
          (Lean.Expr.const `Test.OptimizeEq.a [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.const `Test.OptimizeEq.b []))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat []))))


elab "eqNatConstructor_4" : term => return eqNatConstructor_4

#testOptimize [ "EqNatConstructor_4" ] [50 - a, b] = [10 - a, b] ===> eqNatConstructor_4

-- [a * 50, b] = [10 * a, b] ===> [Nat.mul 50 a, b] = [Nat.mul 10 a, b]
-- Must remain unchanged
-- NOTE: reordering applied on commutative operators (e.g., Eq)
def eqNatConstructor_5 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
      (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
          (Lean.Expr.const `Test.OptimizeEq.a [])))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        ( Lean.Expr.const `Test.OptimizeEq.b []))
        (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
        (Lean.Expr.const `Test.OptimizeEq.a [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.const `Test.OptimizeEq.b []))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat []))))

elab "eqNatConstructor_5" : term => return eqNatConstructor_5

#testOptimize [ "EqNatConstructor_5" ] [50 * a, b] = [10 * a, b] ===> eqNatConstructor_5

-- [a / 50, b] = [a / 10, b] ===> [Nat.div a 50, b] = [Nat.div a 10, b]
-- Must remain unchanged
def eqNatConstructor_6 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
      (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.app
           (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.const `Test.OptimizeEq.a []))
           (Lean.Expr.lit (Lean.Literal.natVal 10))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `Test.OptimizeEq.b []))
        (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.const `Test.OptimizeEq.a []))
        (Lean.Expr.lit (Lean.Literal.natVal 50))))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.const `Test.OptimizeEq.b []))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat []))))


elab "eqNatConstructor_6" : term => return eqNatConstructor_6

#testOptimize [ "EqNatConstructor_6" ] [a / 50, b] = [a / 10, b] ===> eqNatConstructor_6

-- [a + 50, b] = [a + 10, b] ===> [Nat.add 50 a, b] = [Nat.add 10 a, b]
-- NOTE: Unlike Nat.sub, Nat.mul and Nat.div, we should be able to state that equality
-- in this case must result to ``False.
-- We keep this as is for the time being until more complex simplifications are considered.
def eqNatConstructor_7 : Expr :=
 Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
      (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
          (Lean.Expr.const `Test.OptimizeEq.a [])))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `Test.OptimizeEq.b []))
        (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
 (Lean.Expr.app
   (Lean.Expr.app
     (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
     (Lean.Expr.app
       (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
       (Lean.Expr.const `Test.OptimizeEq.a [])))
   (Lean.Expr.app
     (Lean.Expr.app
       (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
       (Lean.Expr.const `Test.OptimizeEq.b []))
     (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat []))))

elab "eqNatConstructor_7" : term => return eqNatConstructor_7

#testOptimize [ "EqNatConstructor_7" ] [a + 50, b] = [a + 10, b] ===> eqNatConstructor_7

-- 430 : Int = 430 : Int ===> True
#testOptimize [ "EqIntConstructor_1" ] (430 : Int) = 430 ===> True

-- 40 = 2300 ===> False
#testOptimize [ "EqIntConstructor_2" ] (40 : Int) = 2300 ===> False

-- -53 = -53 ===> True
#testOptimize [ "EqIntConstructor_3" ] (-53 : Int) = -53 ===> True

-- -430 = 430 ===> False
#testOptimize [ "EqIntConstructor_4" ] (-430 : Int) = 430 ===> False

-- ∀ (x : Int), (x = 1234) ===> ∀ (x : Int), (x = 1234)
-- NOTE: We here provide the internal representation to ensure that 1234 is properly reduced to `Int.ofNat (Expr.lit (Literal.natVal 1234))`
def eqIntConstructor_5 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
        (Lean.Expr.app (Lean.Expr.const `Int.ofNat []) (Lean.Expr.lit (Lean.Literal.natVal 1234))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "eqIntConstructor_5" : term => return eqIntConstructor_5

#testOptimize [ "EqIntConstructor_5" ] ∀ (x : Int), (x = 1234) ===> eqIntConstructor_5

-- ∀ (x : Int), (x = -453) ===> ∀ (x : Int), (x = -453)
-- NOTE: We here provide the internal representation to ensure that -453 is properly reduced to `Int.negSucc (Expr.lit (Literal.natVal 452))`
def eqIntConstructor_6 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
        (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 452))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "eqIntConstructor_6" : term => return eqIntConstructor_6

#testOptimize [ "EqIntConstructor_6" ] ∀ (x : Int), x = -453 ===> eqIntConstructor_6

-- "xyz" = "xyz" ===> True
#testOptimize [ "EqStrConstructor_1" ] "xyz" = "xyz" ===> True

-- "xyz" = "zxyz" ===> False
#testOptimize [ "EqStrConstructor_2" ] "xyz" = "zxyz" ===> False

-- "xyz" = "xyza" ===> False
#testOptimize [ "EqStrConstructor_3" ] "xyz" = "xyzz" ===> False

-- ∀ (x : String), (x = "xyz") ===> ∀ (x : String), (x = "xyz")
-- NOTE: We here provide the internal representation to ensure that "xyz" is properly reduced to `Expr.lit (Literal.strVal "xyz")`
def eqStrConstructor_4 : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `String [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `String []))
        (Lean.Expr.lit (Lean.Literal.strVal "xyz")))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "eqStrConstructor_4" : term => return eqStrConstructor_4

#testOptimize [ "EqStrConstructor_3" ] ∀ (x : String), x = "xyz" ===> eqStrConstructor_4


-- true = not a ===> false = a
#testOptimize [ "TrueEqNot_1" ] ∀ (a : Bool), true = not a ===> ∀ (a : Bool), false = a

-- true = (not (not a) ===> true = a
#testOptimize [ "TrueEqNot_2" ] ∀ (a : Bool), true = (not (not a)) ===> ∀ (a : Bool), true = a

-- true = (not (not (not a)) ===> false = a
#testOptimize [ "TrueEqNot_3" ] ∀ (a : Bool), true = (not (not (not a))) ===> ∀ (a : Bool), false = a

-- true = e ===> true = e
#testOptimize [ "TrueEqUnchanged_1" ] ∀ (a : Bool), true = a ===> ∀ (a : Bool), true = a

-- a = true ===> true = a
-- NOTE: reordering applied on operands
#testOptimize [ "TrueEqUnchanged_2" ] ∀ (a : Bool), a = true ===> ∀ (a : Bool), true = a


-- false = not a ===> true = a
#testOptimize [ "FalseEqNot_1" ] ∀ (a : Bool), false = not a ===> ∀ (a : Bool), true = a

-- false = (not (not a) ===> false = a
#testOptimize [ "FalseEqNot_2" ] ∀ (a : Bool), false = (not (not a)) ===> ∀ (a : Bool), false = a

-- false = (not (not (not a)) ===> true = a
#testOptimize [ "FalseEqNot_3" ] ∀ (a : Bool), false = (not (not (not a))) ===> ∀ (a : Bool), true = a

-- false = e ===> false = e
#testOptimize [ "FalseEqUnchanged_1" ] ∀ (a : Bool), false = a ===> ∀ (a : Bool), false = a

-- a = false ===> false = a
-- NOTE: reordering applied on operands
#testOptimize [ "FalseEqUnchanged_2" ] ∀ (a : Bool), a = false ===> ∀ (a : Bool), false = a

-- not a = not b ===> a = b
#testOptimize [ "NotEqNot_1" ] ∀ (a b : Bool), not a = not b ===> ∀ (a b : Bool), a = b

-- not a = not (not b) ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_2" ] ∀ (a b : Bool), not a = not (not b) ===> ∀ (a b : Bool), b = not a

-- not a = not (not (not b)) ===> a = b
#testOptimize [ "NotEqNot_3" ] ∀ (a b : Bool), not a = not (not (not b)) ===> ∀ (a b : Bool), a = b

-- not (not a) = not (not b) ===> a = b
#testOptimize [ "NotEqNot_4" ] ∀ (a b : Bool), not (not a) = not (not b) ===> ∀ (a b : Bool), a = b


-- not (not (not a)) = not (not (not b)) ===> a = b
#testOptimize [ "NotEqNot_5" ] ∀ (a b : Bool), not (not (not a)) = not (not (not b)) ===> ∀ (a b : Bool), a = b

-- not (not (not a)) = b ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_6" ] ∀ (a b : Bool), not (not (not a)) = b ===> ∀ (a b : Bool), b = not a

-- not a = b ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqUnchanged_1" ] ∀ (a b : Bool), not a = b ===> ∀ (a b : Bool), b = not a

-- a = not b ===> a = not b
#testOptimize [ "NotEqUnchanged_2" ] ∀ (a b : Bool), a = not b ===> ∀ (a b : Bool), a = not b


-- (¬ a) = ¬ b ===> a = b
#testOptimize [ "NeqEqNeg_1" ] ∀ (a b : Prop), (¬ a) = ¬ b ===> ∀ (a b : Prop), a = b

-- (¬ a) = ¬ (¬ b) ===> (¬ a) = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqNeg_2" ] ∀ (a b : Prop), (¬ a) = ¬ (¬ b) ===> ∀ (a b : Prop), b = ¬ a

-- (¬ a) = ¬ (¬ (¬ b)) ===> a = b
#testOptimize [ "NegEqNeg_3" ] ∀ (a b : Prop), (¬ a) = ¬ (¬ (¬ b)) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ a)) = ¬ (¬ b) ===> a = b
#testOptimize [ "NegEqNeg_4" ] ∀ (a b : Prop), (¬ (¬ a)) = ¬ (¬ b) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) ===> a = b
#testOptimize [ "NegEqNeg_5" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ (¬ a))) = b ===> ¬ a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqNeg_6" ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = b ===> ∀ (a b : Prop), b = ¬ a

-- (¬ a) = b ===> (¬ a) = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqUnchanged_1" ] ∀ (a b : Prop), (¬ a) = b ===> ∀ (a b : Prop), b = ¬ a

-- a = ¬ b ===> a = ¬ b
#testOptimize [ "NegEqUnchanged_2" ] ∀ (a b : Prop), a = ¬ b ===> ∀ (a b : Prop), a = ¬ b

-- ((∀ (x : Int), x > 10)) = (∀ (x : Int), x > 10) ===> True
#testOptimize [ "ForallEq_1" ] (∀ (x : Int), x > 10) = (∀ (x : Int), x > 10) ===> True

-- ((∀ (x : Int), x > 10)) = (∀ (z : Int), z > 10) ===> True
#testOptimize [ "ForallEq_2" ] (∀ (x : Int), x > 10) = (∀ (z : Int), z > 10) ===> True

-- (∀ (y x : Int), x > y) = (∀ (x y: Int), x < y) ===> True
#testOptimize [ "ForallEq_3" ] (∀ (y x : Int), x > y) = (∀ (x y : Int), x < y) ===> True

-- (∀ (x y : Int), x > y) = (∀ (x y: Int), x < y) ===>
-- (∀ (x y : Int), y < x) = (∀ (x y : Int), x < y)
#testOptimize [ "ForallEq_4" ] (∀ (x y : Int), x > y) = (∀ (x y : Int), x < y) ===>
                               (∀ (x y : Int), y < x) = (∀ (x y : Int), x < y)

-- (∀ (y x : Int), x > y) = (∀ (x y: Int), x > y) ===>
-- (∀ (y x : Int), y < x) = (∀ (x y: Int), y < x)
#testOptimize [ "ForallEq_5" ] (∀ (y x : Int), x > y) = (∀ (x y : Int), x > y) ===>
                               (∀ (x y : Int), y < x) = (∀ (y x : Int), y < x)

-- (∀ (x : Int), fun (h : Int) => x > 10 = fun (h : Int) => x > 10) ===> True
#testOptimize [ "LambdaEq_1" ] ∀ (x : Int), (fun (_h : Int) => x > 10) = (fun (_h : Int) => x > 10) ===> True

-- (∀ (x : Int), fun (h1 : Int) => x > 10 = fun (h2 : Int) => x > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "LambdaEq_2" ] (∀ (x : Int), fun (_h1 : Int) => x > 10 = fun (_h2 : Int) => x > 10) ===> True

-- (∀ (x : Int), fun y => x > x = fun z => x > x) ===> True
#testOptimize [ "LambdaEq_3" ] ∀ (x : Int), (fun (y : Int) => x > y) = (fun z => x > z) ===> True

end Test.OptimizeEq
