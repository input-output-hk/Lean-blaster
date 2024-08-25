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

-- a = b ===> a = b
-- NOTE: reordering applied on operands
#testOptimize [ "EqDiff_1" ] ∀ (a b : Prop), a = b ===> ∀ (a b : Prop), a = b

-- a = (a ∧ b) ===> a = (a ∧ b)
#testOptimize [ "EqDiff_2" ] ∀ (a b : Prop), a = (a ∧ b) ===> ∀ (a b : Prop), a = (a ∧ b)

-- (a ∧ b) = a ===> (a ∧ b) = a
-- NOTE: reordering applied on operands
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
-- NOTE: reordering applied on operands
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
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_16" ] [a + b, c] = [a + b, c, b] ===> False

-- [b + a, c] = [a + c, c] ===> [Nat.add b a, c] = [Nat.add a c, c]
-- Must remain unchanged
-- NOTE: reordering applied on operands
-- NOTE: resolving + to Nat.add
#testOptimize [ "EqConstructor_17" ] [b + a, c] = [a + c, c] ===> [Nat.add a c, c] = [Nat.add b a, c]

-- [f x, y] = [f x, y, z] ==> False
#testOptimize [ "EqConstructor_18" ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, y] = [f x, y, z] ===> False

-- [f x, z] = [f y, z] ==> [f x, z] = [f y, z]
-- Must remain unchanged
-- NOTE: reordering applied on operands
#testOptimize [ "EqConstructor_19" ] ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z] ===>
                                     ∀ (α : Type) (f : α -> α) (x y z : α), [f x, z] = [f y, z]

-- (10 : Nat) = 10 ===> True
#testOptimize [ "EqNatConstructor_1" ] (10 : Nat) = 10 ===> True

-- 10 = 100 ===> False
#testOptimize [ "EqNatConstructor_2" ] (10 : Nat) = 100 ===> False

-- ∀ (x : Nat), (x = 234) ===> ∀ (x : Nat), (x = 234)
-- NOTE: We here provide the internal representation to ensure that 234 is properly reduced to `Expr.lit (Literal.natVal 234)`
def natConstructor3Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
        (Lean.Expr.lit (Lean.Literal.natVal 234)))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "natConstructor3Result" : term => return natConstructor3Result

#testOptimize [ "EqNatConstructor_3" ] ∀ (x : Nat), (x = 234) ===> natConstructor3Result

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
def intConstructor5Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
        (Lean.Expr.app (Lean.Expr.const `Int.ofNat []) (Lean.Expr.lit (Lean.Literal.natVal 1234))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "intConstructor5Result" : term => return intConstructor5Result

#testOptimize [ "EqIntConstructor_5" ] ∀ (x : Int), (x = 1234) ===> intConstructor5Result

-- ∀ (x : Int), (x = -453) ===> ∀ (x : Int), (x = -453)
-- NOTE: We here provide the internal representation to ensure that -453 is properly reduced to `Int.negSucc (Expr.lit (Literal.natVal 452))`
def intConstructor6Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
        (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 452))))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "intConstructor6Result" : term => return intConstructor6Result

#testOptimize [ "EqIntConstructor_6" ] ∀ (x : Int), x = -453 ===> intConstructor6Result

-- "xyz" = "xyz" ===> True
#testOptimize [ "EqStrConstructor_1" ] "xyz" = "xyz" ===> True

-- "xyz" = "zxyz" ===> False
#testOptimize [ "EqStrConstructor_2" ] "xyz" = "zxyz" ===> False

-- ∀ (x : String), (x = "xyz") ===> ∀ (x : String), (x = "xyz")
-- NOTE: We here provide the internal representation to ensure that "xyz" is properly reduced to `Expr.lit (Literal.strVal "xyz")`
def strConstructor3Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `String [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `String []))
        (Lean.Expr.lit (Lean.Literal.strVal "xyz")))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default)

elab "strConstructor3Result" : term => return strConstructor3Result

#testOptimize [ "EqStrConstructor_3" ] ∀ (x : String), x = "xyz" ===> strConstructor3Result


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
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_1" ] ∀ (a b : Bool), not a = not b ===> ∀ (a b : Bool), a = b

-- not a = not (not b) ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotEqNot_2" ] ∀ (a b : Bool), not a = not (not b) ===> ∀ (a b : Bool), b = not a

-- not a = not (not (not b)) ===> a = b
-- NOTE: reordering applied on operands
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
-- NOTE: reordering applied on operands
#testOptimize [ "NeqEqNeg_1" ] ∀ (a b : Prop), (¬ a) = ¬ b ===> ∀ (a b : Prop), a = b

-- (¬ a) = ¬ (¬ b) ===> (¬ a) = b
-- NOTE: reordering applied on operands
#testOptimize [ "NegEqNeg_2" ] ∀ (a b : Prop), (¬ a) = ¬ (¬ b) ===> ∀ (a b : Prop), b = ¬ a

-- (¬ a) = ¬ (¬ (¬ b)) ===> a = b
-- NOTE: reordering applied on operands
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
#testOptimize [ "ForallEq_1" ] ((∀ (x : Int), x > 10)) = (∀ (x : Int), x > 10) ===> True

-- ((∀ (x : Int), x > 10)) = (∀ (z : Int), z > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "ForallEq_2" ] ((∀ (x : Int), x > 10)) = (∀ (z : Int), z > 10) ===> True

-- (∀ (x : Int), fun h => x > 10 = fun h => x > 10) ===> True
#testOptimize [ "LambdaEq_1" ] (∀ (x : Int), fun _h => x > 10 = fun _h => x > 10) ===> True

-- (∀ (x : Int), fun h1 => x > 10 = fun h2 => x > 10) ===> True
-- NOTE: beq on Forall ignores quantifier name
#testOptimize [ "LambdaEq_2" ] (∀ (x : Int), fun _h1 => x > 10 = fun _h2 => x > 10) ===> True

end Test.OptimizeEq
