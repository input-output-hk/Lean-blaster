import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeEq

/-! ## Test objectives to validate normalization and simplification rules on ``Eq -/

-- False = True ===> False
#testOptimize [ "EqFalseTrue", proof ] False = True ===> False

-- True = False ===> False
#testOptimize [ "EqTrueFalse", proof ] True = False ===> False

-- False = a ===> ¬ a
#testOptimize [ "EqFalseLeft", proof ] ∀ (a : Prop), False = a ===> ∀ (a : Prop), ¬ a

-- a = False ===> ¬ a
#testOptimize [ "EqFalseRight", proof ] ∀ (a : Prop), a = False ===> ∀ (a : Prop), ¬ a

-- True = a ===> a
#testOptimize [ "EqTrueLeft", proof ] ∀ (a : Prop), True = a ===> ∀ (a : Prop), a

-- a = True ===> a
#testOptimize [ "EqTrueRight", proof ] ∀ (a : Prop), a = True ===> ∀ (a : Prop), a

-- a = a ===> True
#testOptimize [ "EqReflexive_1", proof ] ∀ (a : Prop), a = a ===> True

-- a = (a ∨ a)  ===> True
#testOptimize [ "EqReflexive_2", proof ] ∀ (a : Prop), a = (a ∨ a) ===> True

-- (a ∨ a) = a ===> True
#testOptimize [ "EqReflexive_3", proof ] ∀ (a : Prop), (a ∨ a) = a ===> True

-- ((b ∧ ¬ b) ∨ a) = a ===> True
#testOptimize [ "EqReflexive_4", proof ] ∀ (a b : Prop), ((b ∧ ¬ b) ∨ a) = a ===> True

-- (if c then a else b) = if c then a else b ===> True
#testOptimize [ "EqReflexive_5", proof ] ∀ (c : Bool) (a b : Prop), (if c then a else b) = if c then a else b ===> True

-- a = ¬ a ===> False
#testOptimize [ "EqNeq_1" , proof] ∀ (a : Prop), (a = ¬ a) ===> False

-- ¬ a = a ===> False
#testOptimize [ "EqNeq_2", proof ] ∀ (a : Prop), (¬ a = a) ===> False

-- a = (¬ (¬ a)) ===> True
#testOptimize [ "EqNeq_3", proof ] ∀ (a : Prop), (a = ¬ (¬ a)) ===> True

-- a = (¬ (¬ (¬ a))) ===> False
#testOptimize [ "EqNeq_4", proof ] ∀ (a : Prop), (a = ¬ (¬ (¬ a))) ===> False

-- a = ¬ b ===> a = ¬ b
#testOptimize [ "EqNeq_5", proof ] ∀ (a b : Prop), a = (¬ b) ===> ∀ (a b : Prop), a = (¬ b)

-- ¬ b = a ===> ¬ b = a
-- NOTE: reordering applied on operands
#testOptimize [ "EqNeq_6", proof ] ∀ (a b : Prop), (¬ b) = a ===> ∀ (a b : Prop), a = (¬ b)

-- a = !a ===> False
#testOptimize [ "EqNot_1", proof ] ∀ (a : Bool), a = !a ===> False

-- !a = a ===> False
#testOptimize [ "EqNot_2", proof ] ∀ (a : Bool), (!a) = a ===> False

-- a = (! (! a)) ===> True
#testOptimize [ "EqNot_3", proof ] ∀ (a : Bool), a = ! (!a) ===> True

-- a = (! (! (! a))) ===> False
#testOptimize [ "EqNot_4", proof ] ∀ (a : Bool), (a = ! (! (! a))) ===> False

-- a = ! b ===> a = ! b
#testOptimize [ "EqNot_5", proof ] ∀ (a b : Bool), a = !b ===> ∀ (a b : Bool), a = !b

-- ! b = a ===> ! b = a
-- NOTE: reordering applied on operands
#testOptimize [ "EqNot_6", proof ] ∀ (a b : Bool), (!b) = a ===> ∀ (a b : Bool), a = !b


-- a = b ===> a = b
#testOptimize [ "EqDiff_1", proof ] ∀ (a b : Prop), a = b ===> ∀ (a b : Prop), a = b

-- a = (a ∧ b) ===> a = (a ∧ b)
#testOptimize [ "EqDiff_2", proof ] ∀ (a b : Prop), a = (a ∧ b) ===> ∀ (a b : Prop), a = (a ∧ b)

-- (a ∧ b) = a ===> a = (a ∧ b)
#testOptimize [ "EqDiff_3", proof ] ∀ (a b : Prop), (a ∧ b) = a ===> ∀ (a b : Prop), a = (a ∧ b)


-- true = false ===> False
#testOptimize [ "EqConstructor_1", proof ] true = false ===> False

-- true = true ===> True
#testOptimize [ "EqConstructor_2", proof ] true = true ===> True

-- List.nil = List.nil ===> True
#testOptimize [ "EqConstructor_3", proof ] ∀ (α : Type), (List.nil : List α) = List.nil ===> True

-- List.nil = [1, 2, 3, 4] ===> False
#testOptimize [ "EqConstructor_4", proof ] List.nil = [1, 2, 3, 4] ===> False

variable (a : Nat)
variable (b : Nat)
variable (c : Nat)
-- List.nil = [a, b, c] ===> False
#testOptimize [ "EqConstructor_5", proof ] List.nil = [a, b, c] ===> False

-- [b, a, c] = [a, b, c] ===> [b, a, c] = [a, b, c]
-- Must remain uchanged as we don't know if a = b
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_6", proof ] [b, a, c] = [a, b, c] ===> [a, b, c] = [b, a, c]

-- [b, a, c] = [a, b] ===> False
#testOptimize [ "EqConstructor_7", proof ] [b, a, c] = [a, b] ===> False

-- [b, a, c] = [b, a, c] ===> True
#testOptimize [ "EqConstructor_8", proof ] [b, a, c] = [b, a, c] ===> True

inductive Color where
  | red : Color
  | blue : Color
  | yellow : Color

#testOptimize [ "EqConstructor_9", proof ] Color.red = Color.red ===> True
#testOptimize [ "EqConstructor_10", proof ] Color.red = Color.blue ===> False
#testOptimize [ "EqConstructor_11", proof ] Color.red = Color.yellow ===> False

-- x = Color.red ===> x = Color.red
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_12", proof ] ∀ (x : Color), x = Color.red ===> ∀ (x : Color), Color.red = x

-- List.nil : List α = List.nil : List α ===> True
#testOptimize [ "EqConstructor_13", proof ] ∀ (α : Type), (List.nil : List α) = (List.nil : List α) ===> True

-- List.nil = [x, y, z] ===> False
#testOptimize [ "EqConstructor_14", proof ] ∀ (α : Type) (x y z : α), List.nil = [x, y, z] ===> False

-- [x, y] = [x, y, z] ===> False
#testOptimize [ "EqConstructor_15", proof ] ∀ (α : Type) (x y z : α), [x, y] = [x, y, z] ===> False

-- [z, y] = [x, y, z] ===> False
#testOptimize [ "EqConstructor_15b", proof ] ∀ (α : Type) (x y z : α), [z, y] = [x, y, z] ===> False

-- [a + b, c] = [a + b, c, b] ===> False
#testOptimize [ "EqConstructor_16", proof ] [a + b, c] = [a + b, c, b] ===> False

-- [b + a, c] = [a + c, c] ===> [Nat.add b a, c] = [Nat.add a c, c]
-- Must remain unchanged
-- NOTE: reordering applied on operands
-- NOTE: resolving + to Nat.add
#testOptimize [ "EqConstructor_17" ] [b + a, c] = [a + c, c] ===> [Nat.add a b, c] = [Nat.add a c, c]

-- [f x, y] = [f x, y, z] ==> False
#testOptimize [ "EqConstructor_18", proof ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, y] = [f x, y, z] ===> False

-- [f x, z] = [f y, z] ==> [f x, z] = [f y, z]
-- Must remain unchanged
#testOptimize [ "EqConstructor_19", proof ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z] ===>
                                     ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z]

-- [b + a, c] = [a + c, c, b] ===> False
#testOptimize [ "EqConstructor_20" ] [b + a, c] = [a + c, c, b] ===> False

-- [x, Color.red] = [x, Color.blue] ===> False
#testOptimize [ "EqConstructor_21", proof ] ∀ (x : Color), [x, Color.red] = [x, Color.blue] ===> False

-- [f x y, z] = [f x y, z, x] ===> False
#testOptimize [ "EqConstructor_22", proof ] ∀ (f : Nat → Nat → Nat) (x y z : Nat), [f x y, z] = [f x y, z, x] ===> False

-- [f x y, z] = [f x y, z, x] ===> False (polymorphic variant)
#testOptimize [ "EqConstructor_23", proof ] ∀ (α : Type) (f : α → α → α) (x y z : α), [f x y, z] = [f x y, z, x] ===> False

-- [x, 1] = [x, 2] ===> False
#testOptimize [ "EqConstructor_24", proof ] ∀ (x : Nat), [x, 1] = [x, 2] ===> False

-- ∀ (p : Nat → Prop) (_h : ∀ x, p x → p (x + 1)) (a b : Nat), [a, b] = [a, b, b] ===>
--   ∀ (p : Nat → Prop), ¬ ∀ (x : Nat), p x → p (Nat.add 1 x)
#testOptimize [ "EqConstructor_25", proof ] (norm-result: 1)
                                     ∀ (p : Nat → Prop) (_h : ∀ x, p x → p (x + 1)) (a b : Nat),
                                       [a, b] = [a, b, b] ===>
                                     ∀ (p : Nat → Prop), ¬ ∀ (x : Nat), p x → p (Nat.add 1 x)

-- (10 : Nat) = 10 ===> True
#testOptimize [ "EqNatConstructor_1", proof ] (10 : Nat) = 10 ===> True

-- 10 = 100 ===> False
#testOptimize [ "EqNatConstructor_2", proof ] (10 : Nat) = 100 ===> False

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

-- ∀ (n m : Nat), [50 - n, m] = [10 - n, m] ===> ∀ (n m : Nat), [Nat.sub 50 n, m] = [Nat.sub 10 n, m]
-- Must remain unchanged
def eqNatConstructor_4 : Expr :=
Lean.Expr.forallE `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Nat.sub []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "eqNatConstructor_4" : term => return eqNatConstructor_4

#testOptimize [ "EqNatConstructor_4", proof ] ∀ (n m : Nat), [50 - n, m] = [10 - n, m] ===> eqNatConstructor_4

-- ∀ (n m : Nat), [n * 50, m] = [10 * n, m] ===> ∀ (n m : Nat), [Nat.mul 50 n, m] = [Nat.mul 10 n, m]
-- Must remain unchanged
def eqNatConstructor_5 : Expr :=
Lean.Expr.forallE `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Nat.mul []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "eqNatConstructor_5" : term => return eqNatConstructor_5

#testOptimize [ "EqNatConstructor_5", proof ] ∀ (n m : Nat), [50 * n, m] = [10 * n, m] ===> eqNatConstructor_5

-- ∀ (n m : Nat), [n / 50, m] = [n / 10, m] ===> ∀ (n m : Nat), [Nat.div n 50, m] = [Nat.div n 10, m]
-- Must remain unchanged
def eqNatConstructor_6 : Expr :=
 Lean.Expr.forallE `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 1))
              (Lean.Expr.lit (Lean.Literal.natVal 10))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Nat.div []) (Lean.Expr.bvar 1))
            (Lean.Expr.lit (Lean.Literal.natVal 50))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "eqNatConstructor_6" : term => return eqNatConstructor_6

#testOptimize [ "EqNatConstructor_6", proof ] ∀ (n m : Nat), [n / 50, m] = [n / 10, m] ===> eqNatConstructor_6

-- ∀ (n m : Nat), [n + 50, m] = [n + 10, m] ===> ∀ (n m : Nat), [Nat.add 50 n, m] = [Nat.add 10 n, m]
-- NOTE: Unlike Nat.sub, Nat.mul and Nat.div, we should be able to state that equality
-- in this case must result to ``False.
-- We keep this as is for the time being until more complex simplifications are considered.
def eqNatConstructor_7 : Expr :=
 Lean.Expr.forallE `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `m
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero]) (Lean.Expr.const `Nat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 10)))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Nat.add []) (Lean.Expr.lit (Lean.Literal.natVal 50)))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)

elab "eqNatConstructor_7" : term => return eqNatConstructor_7

#testOptimize [ "EqNatConstructor_7", proof ] ∀ (n m : Nat), [n + 50, m] = [n + 10, m] ===> eqNatConstructor_7

-- 430 : Int = 430 : Int ===> True
#testOptimize [ "EqIntConstructor_1", proof ] (430 : Int) = 430 ===> True

-- 40 = 2300 ===> False
#testOptimize [ "EqIntConstructor_2", proof ] (40 : Int) = 2300 ===> False

-- -53 = -53 ===> True
#testOptimize [ "EqIntConstructor_3", proof ] (-53 : Int) = -53 ===> True

-- -430 = 430 ===> False
#testOptimize [ "EqIntConstructor_4", proof ] (-430 : Int) = 430 ===> False

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

#testOptimize [ "EqIntConstructor_5", proof ] ∀ (x : Int), (x = 1234) ===> eqIntConstructor_5

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

#testOptimize [ "EqIntConstructor_6", proof ] ∀ (x : Int), x = -453 ===> eqIntConstructor_6

-- "xyz" = "xyz" ===> True
#testOptimize [ "EqStrConstructor_1", proof ] "xyz" = "xyz" ===> True

-- "xyz" = "zxyz" ===> False
#testOptimize [ "EqStrConstructor_2", proof ] "xyz" = "zxyz" ===> False

-- "xyz" = "xyza" ===> False
#testOptimize [ "EqStrConstructor_3", proof ] "xyz" = "xyzz" ===> False

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

#testOptimize [ "EqStrConstructor_4", proof ] ∀ (x : String), x = "xyz" ===> eqStrConstructor_4


-- true = not a ===> false = a
#testOptimize [ "TrueEqNot_1", proof ] ∀ (a : Bool), true = not a ===> ∀ (a : Bool), false = a

-- true = (not (not a) ===> true = a
#testOptimize [ "TrueEqNot_2", proof ] ∀ (a : Bool), true = (not (not a)) ===> ∀ (a : Bool), true = a

-- true = (not (not (not a)) ===> false = a
#testOptimize [ "TrueEqNot_3", proof ] ∀ (a : Bool), true = (not (not (not a))) ===> ∀ (a : Bool), false = a

-- true = e ===> true = e
#testOptimize [ "TrueEqUnchanged_1", proof ] ∀ (a : Bool), true = a ===> ∀ (a : Bool), true = a

-- a = true ===> true = a
-- NOTE: reordering applied on operands
#testOptimize [ "TrueEqUnchanged_2", proof ] ∀ (a : Bool), a = true ===> ∀ (a : Bool), true = a


-- false = not a ===> true = a
#testOptimize [ "FalseEqNot_1", proof ] ∀ (a : Bool), false = not a ===> ∀ (a : Bool), true = a

-- false = (not (not a) ===> false = a
#testOptimize [ "FalseEqNot_2", proof ] ∀ (a : Bool), false = (not (not a)) ===> ∀ (a : Bool), false = a

-- false = (not (not (not a)) ===> true = a
#testOptimize [ "FalseEqNot_3", proof ] ∀ (a : Bool), false = (not (not (not a))) ===> ∀ (a : Bool), true = a

-- false = e ===> false = e
#testOptimize [ "FalseEqUnchanged_1", proof ] ∀ (a : Bool), false = a ===> ∀ (a : Bool), false = a

-- a = false ===> false = a
-- NOTE: reordering applied on operands
#testOptimize [ "FalseEqUnchanged_2", proof ] ∀ (a : Bool), a = false ===> ∀ (a : Bool), false = a

-- not a = not b ===> a = b
#testOptimize [ "NotEqNot_1", proof ] ∀ (a b : Bool), not a = not b ===> ∀ (a b : Bool), a = b

-- not a = not (not b) ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_2", proof ] ∀ (a b : Bool), not a = not (not b) ===> ∀ (a b : Bool), b = not a

-- not a = not (not (not b)) ===> a = b
#testOptimize [ "NotEqNot_3", proof ] ∀ (a b : Bool), not a = not (not (not b)) ===> ∀ (a b : Bool), a = b

-- not (not a) = not (not b) ===> a = b
#testOptimize [ "NotEqNot_4", proof ] ∀ (a b : Bool), not (not a) = not (not b) ===> ∀ (a b : Bool), a = b


-- not (not (not a)) = not (not (not b)) ===> a = b
#testOptimize [ "NotEqNot_5", proof ] ∀ (a b : Bool), not (not (not a)) = not (not (not b)) ===> ∀ (a b : Bool), a = b

-- not (not (not a)) = b ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_6", proof ] ∀ (a b : Bool), not (not (not a)) = b ===> ∀ (a b : Bool), b = not a

-- not a = b ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqUnchanged_1", proof ] ∀ (a b : Bool), not a = b ===> ∀ (a b : Bool), b = not a

-- a = not b ===> a = not b
#testOptimize [ "NotEqUnchanged_2", proof ] ∀ (a b : Bool), a = not b ===> ∀ (a b : Bool), a = not b


-- (¬ a) = ¬ b ===> a = b
#testOptimize [ "NeqEqNeg_1", proof ] ∀ (a b : Prop), (¬ a) = ¬ b ===> ∀ (a b : Prop), a = b

-- (¬ a) = ¬ (¬ b) ===> (¬ a) = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqNeg_2", proof ] ∀ (a b : Prop), (¬ a) = ¬ (¬ b) ===> ∀ (a b : Prop), b = ¬ a

-- (¬ a) = ¬ (¬ (¬ b)) ===> a = b
#testOptimize [ "NegEqNeg_3", proof ] ∀ (a b : Prop), (¬ a) = ¬ (¬ (¬ b)) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ a)) = ¬ (¬ b) ===> a = b
#testOptimize [ "NegEqNeg_4", proof ] ∀ (a b : Prop), (¬ (¬ a)) = ¬ (¬ b) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) ===> a = b
#testOptimize [ "NegEqNeg_5", proof ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = ¬ (¬ (¬ b)) ===> ∀ (a b : Prop), a = b

-- (¬ (¬ (¬ a))) = b ===> ¬ a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqNeg_6", proof ] ∀ (a b : Prop), (¬ (¬ (¬ a))) = b ===> ∀ (a b : Prop), b = ¬ a

-- (¬ a) = b ===> (¬ a) = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqUnchanged_1", proof ] ∀ (a b : Prop), (¬ a) = b ===> ∀ (a b : Prop), b = ¬ a

-- a = ¬ b ===> a = ¬ b
#testOptimize [ "NegEqUnchanged_2", proof ] ∀ (a b : Prop), a = ¬ b ===> ∀ (a b : Prop), a = ¬ b

-- ((∀ (x : Int), x > 10)) = (∀ (x : Int), x > 10) ===> True
#testOptimize [ "ForallEq_1", proof ] (∀ (x : Int), x > 10) = (∀ (x : Int), x > 10) ===> True

-- ((∀ (x : Int), x > 10)) = (∀ (z : Int), z > 10) ===> True
#testOptimize [ "ForallEq_2", proof ] (∀ (x : Int), x > 10) = (∀ (z : Int), z > 10) ===> True

-- (∀ (y x : Int), x > y) = (∀ (x y: Int), x < y) ===> True
#testOptimize [ "ForallEq_3", proof ] (∀ (y x : Int), x > y) = (∀ (x y : Int), x < y) ===> True

-- (∀ (x y : Int), x > y) = (∀ (x y: Int), x < y) ===>
-- (∀ (x y : Int), y < x) = (∀ (x y : Int), x < y)
#testOptimize [ "ForallEq_4", proof ] (∀ (x y : Int), x > y) = (∀ (x y : Int), x < y) ===>
                               (∀ (x y : Int), y < x) = (∀ (x y : Int), x < y)

-- (∀ (y x : Int), x > y) = (∀ (x y: Int), x > y) ===>
-- (∀ (y x : Int), y < x) = (∀ (x y: Int), y < x)
#testOptimize [ "ForallEq_5", proof ] (∀ (y x : Int), x > y) = (∀ (x y : Int), x > y) ===>
                               (∀ (x y : Int), y < x) = (∀ (y x : Int), y < x)

-- (∀ (x : Int), fun (h : Int) => x > 10 = fun (h : Int) => x > 10) ===> True
#testOptimize [ "LambdaEq_1", proof ] ∀ (x : Int), (fun (_h : Int) => x > 10) = (fun (_h : Int) => x > 10) ===> True

-- (∀ (x : Int), fun (h1 : Int) => x > 10 = fun (h2 : Int) => x > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "LambdaEq_2", proof ] (∀ (x : Int), fun (_h1 : Int) => x > 10 = fun (_h2 : Int) => x > 10) ===> True

-- (∀ (x : Int), fun y => x > x = fun z => x > x) ===> True
#testOptimize [ "LambdaEq_3", proof ] ∀ (x : Int), (fun (y : Int) => x > y) = (fun z => x > z) ===> True

end Test.OptimizeEq
