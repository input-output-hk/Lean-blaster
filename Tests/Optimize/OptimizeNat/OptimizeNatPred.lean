import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatPred

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.pred -/

/-! Test cases for `reduceApp` rule on ``Nat.pred. -/

-- Nat.pred Nat.zero ===> 0
def natPredCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "natPredCst_1" : term => return natPredCst_1

#testOptimize [ "NatPredCst_1" ] Nat.pred Nat.zero ===> natPredCst_1

-- Nat.pred Nat.zero = 0 ===> True
#testOptimize [ "NatPredCst_2" ] Nat.pred Nat.zero = 0 ===> True

-- Nat.pred 0 ===> 0
#testOptimize [ "NatPredCst_3" ] Nat.pred 0 ===> natPredCst_1

-- Nat.pred 1 = 0 ===> True
#testOptimize [ "NatPredCst_4" ] Nat.pred 1 = 0 ===> True

-- Nat.pred 10 ===> 9
def natPredCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 9)
elab "natPredCst_5" : term => return natPredCst_5

#testOptimize [ "NatPredCst_5" ] Nat.pred 10 ===> natPredCst_5

-- Nat.pred (Nat.pred 10) ===> 8
def natPredCst_6 : Expr := Lean.Expr.lit (Lean.Literal.natVal 8)
elab "natPredCst_6" : term => return natPredCst_6

#testOptimize [ "NatPredCst_6" ] Nat.pred (Nat.pred 10) ===> natPredCst_6

-- Nat.pred (Nat.pred (Nat.pred 10)) ===> 7
def natPredCst_7 : Expr := Lean.Expr.lit (Lean.Literal.natVal 7)
elab "natPredCst_7" : term => return natPredCst_7

-- Nat.pred (Nat.pred 1)) ===> 0
#testOptimize [ "NatPredCst_8" ] Nat.pred (Nat.pred (Nat.pred 1)) ===> natPredCst_1

-- Nat.pred (10 + 30) ===> 39
def natPredCst_9 : Expr := Lean.Expr.lit (Lean.Literal.natVal 39)
elab "natPredCst_9" : term => return natPredCst_9

#testOptimize [ "NatPredCst_9" ] Nat.pred (10 + 30) ===> natPredCst_9

-- Nat.pred (10 - 30) ===> 0
#testOptimize [ "NatPredCst_10" ] Nat.pred (10 - 30) ===> natPredCst_1

-- Nat.pred (Nat.succ 10) ===> 10
def natPredCst_11 : Expr := Lean.Expr.lit (Lean.Literal.natVal 10)
elab "natPredCst_11" : term => return natPredCst_11

#testOptimize [ "NatPredCst_11" ] Nat.pred (Nat.succ 10) ===> natPredCst_11


/-! Test cases for normalization rule ` ``Nat.pred n ===> n - 1`. -/

-- Nat.pred x = x - 1 ===> True
#testOptimize [ "NatPredNorm_1" ] ∀ (x : Nat), (Nat.pred x) = x - 1 ===> True

-- Nat.pred x = ===> x - 1
def natPredNorm_2 : Expr :=
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
elab "natPredNorm_2" : term => return natPredNorm_2

#testOptimize [ "NatPredNorm_2" ] ∀ (x y : Nat), (Nat.pred x) < y ===> natPredNorm_2

-- Nat.pred (Nat.pred x) = x - 2 ===> True
#testOptimize [ "NatPredNorm_3" ] ∀ (x : Nat), Nat.pred (Nat.pred x) = x - 2 ===> True

-- Nat.pred (Nat.pred (Nat.pred x)) = x -3 ===> True
#testOptimize [ "NatPredNorm_4" ] ∀ (x : Nat), Nat.pred (Nat.pred (Nat.pred x)) = x - 3 ===> True

-- Nat.pred (x + y) = (x + y) - 1 ===> True
#testOptimize [ "NatPredNorm_5" ] ∀ (x y : Nat), Nat.pred (x + y) = (x + y) - 1 ===> True

-- Nat.pred (x - y) = (x - y) + 1 ===> True
#testOptimize [ "NatPredNorm_6" ] ∀ (x y : Nat), Nat.pred (x - y) = (x - y) - 1 ===> True

-- Nat.pred (Nat.succ x) = x ===> True
#testOptimize [ "NatPredNorm_7" ] ∀ (x : Nat), Nat.pred (Nat.succ x) = x ===> True

-- Nat.pred (Nat.pred (x + y)) = (x + y) - 2 ===> True
#testOptimize [ "NatPredNorm_8" ] ∀ (x y : Nat), Nat.pred (Nat.pred (x + y)) = (x + y) - 2 ===> True

-- Nat.pred (Nat.pred (x - y)) = (x - y) - 2 ===> True
#testOptimize [ "NatPredNorm_9" ] ∀ (x y : Nat), Nat.pred (Nat.pred (x - y)) = (x - y) - 2 ===> True

-- Nat.pred (Nat.pred (Nat.succ x)) = x - 1 ===> True
#testOptimize [ "NatPredNorm_10" ] ∀ (x : Nat), Nat.pred (Nat.pred (Nat.succ x)) = x - 1 ===> True


/-! TTest cases to ensure that constant propagation is properly performed
    when `Nat.pred` operand is reduced to constant value via optimization. -/

variable (x : Nat)
variable (y : Nat)

-- Nat.pred (100 + ((180 - (x + 40)) - 150)) ===> 99
def natPredReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 99)
elab "natPredReduce_1" : term => return natPredReduce_1

#testOptimize [ "NatPredReduce_1" ] Nat.pred (100 + ((180 - (x + 40)) - 150)) ===> natPredReduce_1

-- Nat.pred ((100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24)) ===> 123
def natPredReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 123)
elab "natPredReduce_2" : term => return natPredReduce_2

#testOptimize [ "NatPredReduce_2" ] Nat.pred ((100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24))  ===> natPredReduce_2

end Test.OptimizeNatPred
