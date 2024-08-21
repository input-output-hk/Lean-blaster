import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeBEq
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq -/

-- false == true ===> false
#testOptimize [ "BEqFalseTrue" ] false == true ===> false

-- true == false ===> false
#testOptimize [ "BEqTrueFalse" ] true == false ===> false

-- false == a ===> not a
#testOptimize [ "BEqFalseLeft" ] ∀ (a : Bool), (false == a) = not a ===> True

-- a == false ===> not a
#testOptimize [ "BEqFalseRight" ] ∀ (a : Bool), (a == false) = not a ===> True

-- true == a ===> a
#testOptimize [ "BEqTrueLeft" ] ∀ (a : Bool), (true == a) = a ===> True

-- a == true ===> a
#testOptimize [ "BEqTrueRight" ] ∀ (a : Bool), (a == true) = a ===> True

-- a == a ===> true
#testOptimize [ "BEqReflexive_1" ] ∀ (a : Bool), (a == a) = true ===> True

-- a == (a || a) ===> true
#testOptimize [ "BEqReflexive_2" ] ∀ (a : Bool), (a == (a || a)) = true ===> True

-- (a || a) == a ===> true
#testOptimize [ "BEqReflexive_3" ] ∀ (a : Bool), ((a || a) == a) = true ===> True

-- a == ((b && ! b) || a) ===> true
#testOptimize [ "BEqReflexive_4" ] ∀ (a b : Bool), (((b && ! b) || a) == a) = true ===> True

-- a == ! a ===> false
#testOptimize [ "BEqNeq_1" ] ∀ (a : Bool), (a == ! a) = false ===> True

-- ! a == a ===> false
#testOptimize [ "BEqNeq_2" ] ∀ (a : Bool), (! a == a) = false ===> True

-- a == (! (! a)) ===> true
#testOptimize [ "BEqNeq_3" ] ∀ (a : Bool), (a == ! (! a)) = true ===> True

-- a == (! (! (! a))) ===> false
#testOptimize [ "BEqNeq_4" ] ∀ (a : Bool), (a == ! (! (! a))) = false ===> True

-- a == ! b ===> a == ! b
-- NOTE: We explicitly introduced `true =` to be deterministic
#testOptimize [ "BEqNeq_5" ] ∀ (a b : Bool), a == ! b ===> ∀ (a b : Bool), true = (a == ! b)

-- ! b == a ===> ! b == a
-- NOTE: reordering applied on operands
-- NOTE: We explicitly introduced `true =` to be deterministic
#testOptimize [ "BEqNeq_6" ] ∀ (a b : Bool), (! b) == a ===> ∀ (a b : Bool), true = (a == ! b)

-- a == b ===> a == b
-- NOTE: We explicitly introduced `true =` to be deterministic
#testOptimize [ "BEqDiff_1" ] ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), true = (a == b)

-- a == (a && b) ===> a == (a && b)
-- NOTE: reordering applied on operands
-- NOTE: We explicitly introduced `true =` to be deterministic
#testOptimize [ "BEqDiff_2" ] ∀ (a b : Bool), a == (a && b) ===> ∀ (a b : Bool), true = (a == (b && a))

-- (a && b) == a ===> (a && b) == a
-- NOTE: reordering applied on operands
-- NOTE: We explicitly introduced `true =` to be deterministic
#testOptimize [ "BEqDiff_3" ] ∀ (a b : Bool), (a && b) == a ===> ∀ (a b : Bool), true = (a == (b && a))

-- List.nil = List.nil ===> True
-- NOTE: resolve to `true` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_1" ] (List.nil : List Int) == List.nil ===> true

-- List.nil = [1, 2, 3, 4] ===> False
-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_2" ] List.nil == [1, 2, 3, 4] ===> false

opaque a : Nat
opaque b : Nat
opaque c : Nat

-- List.nil == [a, b, c] ===> false
-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_3" ] List.nil == [a, b, c] ===> false

-- [b, a, c] == [a, b, c] ===> List.beq [b, a, c] [a, b, c]
#testOptimize [ "BEqConstructor_4" ] [b, a, c] == [a, b, c] ===> List.beq [b, a, c] [a, b, c]

-- [b, a, c] == [a, b] ===> List.beq [b, a, c] [a, b]
#testOptimize [ "BEqConstructor_5" ] [b, a, c] == [a, b] ===> List.beq [b, a, c] [a, b]


-- [b, a, c] == [b, a, c] ===> List.beq [b, a, c] [b, a, c]
#testOptimize [ "BEqConstructor_6" ] [b, a, c] == [b, a, c] ===> List.beq [b, a, c] [b, a, c]


inductive Color where
  | red : Color
  | blue : Color
  | yellow : Color
 deriving Repr

def color_leq (x : Color) (y : Color) : Bool :=
  match x, y with
   | Color.red, Color.red => true
   | _, _ => false

-- providing a BEq instance not satisfying refl, symm and trans properties
instance instBEqColor : BEq Color where
  beq a b := color_leq a b


-- NOTE: resolve to `true` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_7" ] Color.red == Color.red ===> true

-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_8" ] Color.red == Color.blue ===> false

-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_9" ] Color.blue == Color.blue ===> false

-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_10" ] Color.yellow == Color.yellow ===> false

-- x = Color.red ===> x = Color.red
-- NOTE: reordering applied on operands
-- TODO: Need to check how we can validate unfolding of match expression
#testOptimize [ "BEqConstructor_11" ] ∀ (x : Color), (x == Color.red) = (x == Color.red) ===> True

-- List.nil : List α == List.nil : List α ===> True
-- NOTE: resolve to `true` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_12" ] ∀ (α : Type), [BEq α] → (List.nil : List α) == (List.nil : List α) ===> True

-- (List.nil == [x, y, z]) = false ===> True
-- NOTE: resolve to `false` via reduction rule (see reduceApp)
#testOptimize [ "BEqConstructor_13" ] ∀ (x y z : Nat), (List.nil == [x, y, z]) = false ===> True

-- [y, x, z] == [x, y, z] ===> true = List.beq [y, x, z] [x, y, z]
#testOptimize [ "BEqConstructor_14" ] ∀ (x y z : Nat), [y, x, z] == [x, y, z] ===> ∀ (x y z : Nat), true = (List.beq [y, x, z] [x, y, z])

-- [x, y] == [x, y, z] ===> true = List.beq [x, y] [x, y, z]
#testOptimize [ "BEqConstructor_15" ] ∀ (α : Type) (x y z : α), [BEq α] → [x, y] == [x, y, z] ===>
                                      ∀ (α : Type) (x y z : α), [BEq α] → true = (List.beq [x, y] [x, y, z])

-- [x, y, z] == [x, y, z] ===> true = List.beq [x, y, z] [x, y, z]
#testOptimize [ "BEqConstructor_16" ] ∀ (x y z : Nat), [x, y, z] == [x, y, z] ===> ∀ (x y z : Nat), true = (List.beq [x, y, z] [x, y, z])


-- (10 : Nat) = 10 ===> true
#testOptimize [ "BEqNatConstructor_1" ] (10 : Nat) == 10 ===> true

-- 10 = 100 ===> false
#testOptimize [ "BEqNatConstructor_2" ] (10 : Nat) == 100 ===> false

-- ∀ (x : Nat), (x == 234) ===> ∀ (x : Nat), (x == 234)
-- NOTE: We here provide the internal representation to ensure that 234 is properly reduced to `Expr.lit (Literal.natVal 234)`.
-- NOTE: We explicitly introduced `true =` to be deterministic.
def natConstructor3Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
        (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `BEq.beq [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instBEqNat []))
          (Lean.Expr.lit (Lean.Literal.natVal 234)))
      (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default)

elab "natConstructor3Result" : term => return natConstructor3Result

#testOptimize [ "BEqNatConstructor_3" ] ∀ (x : Nat), (x == 234) ===> natConstructor3Result

-- 430 : Int == 430 : Int ===> true
#testOptimize [ "BEqIntConstructor_1" ] (430 : Int) == 430 ===> true

-- (40 : Int) == 2300 ===> false
#testOptimize [ "BEqIntConstructor_2" ] (40 : Int) == 2300 ===> false

-- -53 == -53 ===> true
#testOptimize [ "BEqIntConstructor_3" ] (-53 : Int) == -53 ===> true

-- -430 == 430 ===> false
#testOptimize [ "BEqIntConstructor_4" ] (-430 : Int) == 430 ===> false

-- ∀ (x : Int), (x == 1234) ===> ∀ (x : Int), (x == 1234)
-- NOTE: We here provide the internal representation to ensure that 1234 is properly reduced to `Int.ofNat (Expr.lit (Literal.natVal 1234))`.
-- NOTE: We explicitly introduced `true =` to be deterministic.
def intConstructor5Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
        (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `BEq.beq [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero]) (Lean.Expr.const `Int []))
                (Lean.Expr.const `Int.instDecidableEq [])))
          (Lean.Expr.app (Lean.Expr.const `Int.ofNat []) (Lean.Expr.lit (Lean.Literal.natVal 1234))))
          (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default)

elab "intConstructor5Result" : term => return intConstructor5Result

#testOptimize [ "BEqIntConstructor_5" ] ∀ (x : Int), (x == 1234) ===> intConstructor5Result

-- ∀ (x : Int), (x = -453) ===> ∀ (x : Int), (x = -453)
-- NOTE: We here provide the internal representation to ensure that -453 is properly reduced to `Int.negSucc (Expr.lit (Literal.natVal 452))`.
-- NOTE: We explicitly introduced `true =` to be deterministic.
def intConstructor6Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
        (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `BEq.beq [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero]) (Lean.Expr.const `Int []))
                (Lean.Expr.const `Int.instDecidableEq [])))
            (Lean.Expr.app (Lean.Expr.const `Int.negSucc []) (Lean.Expr.lit (Lean.Literal.natVal 452))))
            (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default)

elab "intConstructor6Result" : term => return intConstructor6Result

#testOptimize [ "BEqIntConstructor_6" ] ∀ (x : Int), x == -453 ===> intConstructor6Result

-- "xyz" == "xyz" ===> true
#testOptimize [ "BEqStrConstructor_1" ] "xyz" == "xyz" ===> true

-- "xyz" == "zxyz" ===> false
#testOptimize [ "BEqStrConstructor_2" ] "xyz" == "zxyz" ===> false

-- ∀ (x : String), (x == "xyz") ===> ∀ (x : String), (x == "xyz")
-- NOTE: We here provide the internal representation to ensure that "xyz" is properly reduced to `Expr.lit (Literal.strVal "xyz")`.
-- NOTE: We explicitly introduced `true =` to be deterministic.
def strConstructor3Result : Expr :=
  Lean.Expr.forallE `x
    (Lean.Expr.const `String [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
        (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `BEq.beq [Lean.Level.zero]) (Lean.Expr.const `String []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero]) (Lean.Expr.const `String []))
                (Lean.Expr.const `instDecidableEqString [])))
          (Lean.Expr.lit (Lean.Literal.strVal "xyz")))
          (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default)

elab "strConstructor3Result" : term => return strConstructor3Result

#testOptimize [ "BEqStrConstructor_3" ] ∀ (x : String), x == "xyz" ===> strConstructor3Result

-- true == not a ===> false = a
#testOptimize [ "TrueBEqNot_1" ] ∀ (a : Bool), true == not a ===> ∀ (a : Bool), false = a

-- true == (not (not a) ===> true = a
#testOptimize [ "TrueBEqNot_2" ] ∀ (a : Bool), true == (not (not a)) ===> ∀ (a : Bool), true = a

-- true == (not (not (not a)) ===> false = a
#testOptimize [ "TrueBEqNot_3" ] ∀ (a : Bool), true == (not (not (not a))) ===> ∀ (a : Bool), false = a

-- true == e ===> true = e
#testOptimize [ "TrueBEqUnchanged_1" ] ∀ (a : Bool), true == a ===> ∀ (a : Bool), true = a

-- a == true ===> true = a
#testOptimize [ "TrueBEqUnchanged_2" ] ∀ (a : Bool), a == true ===> ∀ (a : Bool), true = a


-- false == not a ===> true = a
#testOptimize [ "FalseBEqNot_1" ] ∀ (a : Bool), false == not a ===> ∀ (a : Bool), true = a

-- false == (not (not a) ===> false = a
#testOptimize [ "FalseBEqNot_2" ] ∀ (a : Bool), false == (not (not a)) ===> ∀ (a : Bool), false = a

-- false == (not (not (not a)) ===> true = a
#testOptimize [ "FalseBEqNot_3" ] ∀ (a : Bool), false == (not (not (not a))) ===> ∀ (a : Bool), true = a

-- false == e ===> false = e
#testOptimize [ "FalseBEqUnchanged_1" ] ∀ (a : Bool), false == a ===> ∀ (a : Bool), false = a

-- a == false ===> false = a
#testOptimize [ "FalseBEqUnchanged_2" ] ∀ (a : Bool), a == false ===> ∀ (a : Bool), false = a


-- not a == not b ===> a == b
-- NOTE: reordering applied on operands
#testOptimize [ "NotBEqNot_1" ] ∀ (a b : Bool), not a == not b ===> ∀ (a b : Bool), true = (a == b)

-- not a == not (not b) ===> not a == b
-- NOTE: reordering applied on operands
#testOptimize [ "NotBEqNot_2" ] ∀ (a b : Bool), not a == not (not b) ===> ∀ (a b : Bool), true = (b == not a)

-- not a == not (not (not b)) ===> a == b
#testOptimize [ "NotBEqNot_3" ] ∀ (a b : Bool), not a == not (not (not b)) ===> ∀ (a b : Bool), true = (a == b)

-- not (not a) == not (not b) ===> a == b
#testOptimize [ "NotBEqNot_4" ] ∀ (a b : Bool), not (not a) == not (not b) ===> ∀ (a b : Bool), true = (a == b)

-- not (not (not a)) == not (not (not b)) ===> a == b
#testOptimize [ "NotBEqNot_5" ] ∀ (a b : Bool), not (not (not a)) == not (not (not b)) ===> ∀ (a b : Bool), true = (a == b)

-- not (not (not a)) = b ===> not a = b
-- NOTE: reordering applied on operands
#testOptimize [ "NotBEqNot_6" ] ∀ (a b : Bool), not (not (not a)) == b ===> ∀ (a b : Bool), true = (b == not a)


-- not a == b ===> not a == b
-- NOTE: reordering applied on operands
#testOptimize [ "NotBEqUnchanged_1" ] ∀ (a b : Bool), not a == b ===> ∀ (a b : Bool), true = (b == not a)

-- a == not b ===> a == not b
#testOptimize [ "NotBEqUnchanged_2" ] ∀ (a b : Bool), a == not b ===> ∀ (a b : Bool), true = (a == not b)


end Test.OptimizeBEq
