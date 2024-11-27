import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatSucc

/-! ## Test objectives to validate normalization and simplification rules on ``Nat.succ -/

/-! Test cases for `reduceApp` rule on ``Nat.succ. -/

-- Nat.succ Nat.zero ===> 1
def natSuccCst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "natSuccCst_1" : term => return natSuccCst_1

#testOptimize [ "NatSuccCst_1" ] Nat.succ Nat.zero ===> natSuccCst_1

-- Nat.succ Nat.zero = 1 ===> True
#testOptimize [ "NatSuccCst_2" ] Nat.succ Nat.zero = 1 ===> True

-- Nat.succ 0 ===> 1
#testOptimize [ "NatSuccCst_3" ] Nat.succ 0 ===> natSuccCst_1

-- Nat.succ 0 = 1 ===> True
#testOptimize [ "NatSuccCst_4" ] Nat.succ 0 = 1 ===> True

-- Nat.succ 10 ===> 11
def natSuccCst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 11)
elab "natSuccCst_5" : term => return natSuccCst_5

#testOptimize [ "NatSuccCst_5" ] Nat.succ 10 ===> natSuccCst_5

-- Nat.succ (Nat.succ 10) ===> 12
def natSuccCst_6 : Expr := Lean.Expr.lit (Lean.Literal.natVal 12)
elab "natSuccCst_6" : term => return natSuccCst_6

#testOptimize [ "NatSuccCst_6" ] Nat.succ (Nat.succ 10) ===> natSuccCst_6

-- Nat.succ (Nat.succ (Nat.succ 10)) ===> 13
def natSuccCst_7 : Expr := Lean.Expr.lit (Lean.Literal.natVal 13)
elab "natSuccCst_7" : term => return natSuccCst_7

#testOptimize [ "NatSuccCst_7" ] Nat.succ (Nat.succ (Nat.succ 10)) ===> natSuccCst_7

-- Nat.succ (10 + 20) ===> 31
def natSuccCst_8 : Expr := Lean.Expr.lit (Lean.Literal.natVal 31)
elab "natSuccCst_8" : term => return natSuccCst_8

#testOptimize [ "NatSuccCst_8" ] Nat.succ (10 + 20) ===> natSuccCst_8

-- Nat.succ (Nat.pred 10) ===> 10
def natSuccCst_9 : Expr := Lean.Expr.lit (Lean.Literal.natVal 10)
elab "natSuccCst_9" : term => return natSuccCst_9

#testOptimize [ "NatSuccCst_9" ] Nat.succ (Nat.pred 10) ===> natSuccCst_9


/-! Test cases for normalization rule on ` ``Nat.succ n ===> 1 + n `. -/

-- Nat.succ x = x + 1 ===> True
#testOptimize [ "NatSuccNorm_1" ] ∀ (x : Nat), (Nat.succ x) = x + 1 ===> True

-- Nat.succ x = 1 + x ===> True
#testOptimize [ "NatSuccNorm_2" ] ∀ (x : Nat), (Nat.succ x) = 1 + x ===> True

-- Nat.succ x ===> 1 + x
def natSuccNorm_3 : Expr :=
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
elab "natSuccNorm_3" : term => return natSuccNorm_3

#testOptimize [ "NatSuccNorm_3" ] ∀ (x y : Nat), (Nat.succ x) < y ===> natSuccNorm_3

-- Nat.succ (Nat.succ x) = x + 2 ===> True
#testOptimize [ "NatSuccNorm_4" ] ∀ (x : Nat), Nat.succ (Nat.succ x) = x + 2 ===> True

-- Nat.succ (Nat.succ (Nat.succ x)) = x + 3 ===> True
#testOptimize [ "NatSuccNorm_5" ] ∀ (x : Nat), Nat.succ (Nat.succ (Nat.succ x)) = x + 3 ===> True

-- Nat.succ (x + y) = (x + y) + 1 ===> True
#testOptimize [ "NatSuccNorm_6" ] ∀ (x y : Nat), Nat.succ (x + y) = (x + y) + 1 ===> True

-- Nat.succ (x - y) = (x - y) + 1 ===> True
#testOptimize [ "NatSuccNorm_7" ] ∀ (x y : Nat), Nat.succ (x - y) = (x - y) + 1 ===> True

-- Nat.succ (Nat.succ (x + y)) = 2 + (x + y) ===> True
#testOptimize [ "NatSuccNorm_8" ] ∀ (x y : Nat), Nat.succ (Nat.succ (x + y)) = (x + y) + 2 ===> True

-- Nat.succ (Nat.succ (x - y)) = 2 + (x - y) ===> True
#testOptimize [ "NatSuccNorm_9" ] ∀ (x y : Nat), Nat.succ (Nat.succ (x - y)) = (x - y) + 2 ===> True

-- Nat.succ (Nat.pred (Nat.succ x)) = 1 + x ===> True
#testOptimize [ "NatSuccNorm_10" ] ∀ (x : Nat), Nat.succ (Nat.pred (Nat.succ x)) = 1 + x ===> True


/-! Test cases to ensure that `reduceApp` is properly called
    when `Nat.succ` operand is reduced to constant value via optimization. -/

variable (x : Nat)
variable (y : Nat)

-- Nat.succ (100 + ((180 - (x + 40)) - 150)) ===> 101
def natSuccReduce_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 101)
elab "natSuccReduce_1" : term => return natSuccReduce_1

#testOptimize [ "NatSuccReduce_1" ] Nat.succ (100 + ((180 - (x + 40)) - 150)) ===> natSuccReduce_1

def natSuccReduce_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 125)
elab "natSuccReduce_2" : term => return natSuccReduce_2

-- Nat.succ ((100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24)) ===> 125
#testOptimize [ "NatSuccReduce_2" ] Nat.succ ((100 + ((180 - (x + 40)) - 150)) + (((20 - y) - 50) + 24))  ===> natSuccReduce_2

end Test.OptimizeNatSucc
