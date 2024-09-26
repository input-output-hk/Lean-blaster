import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.NormNatZero

/-! ## Test objectives to validate normalization rules on `Nat.zero` -/

-- Nat.zero ===> Expr.lit (Literal.natVal 0)
def constNatZero_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "constNatZero_1" : term => return constNatZero_1

#testOptimize [ "ConstNatZero_1" ] Nat.zero ===> constNatZero_1

-- (0 : Nat) ===> Expr.lit (Literal.natVal 0)
#testOptimize [ "ConstNatZero_2" ] (0 : Nat) ===> constNatZero_1

-- Nat.zero = 0 ===> True
#testOptimize [ "ConstNatZero_3" ] Nat.zero = 0 ===> True

-- Nat.succ Nat.zero ===> Expr.lit (Literal.natVal 1)
def constNatZero_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "constNatZero_4" : term => return constNatZero_4

#testOptimize [ "ConstNatZero_4" ] Nat.succ Nat.zero ===> constNatZero_4

-- Nat.succ 0 ===> Expr.lit (Literal.natVal 1)
#testOptimize [ "ConstNatZero_5" ] Nat.succ 0 ===> constNatZero_4

-- x < Nat.zero ===> x < Expr.lit (Literal.natVal 0)
def constNatZero_6 : Expr :=
 Lean.Expr.forallE `x
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.const `instLTNat []))
      (Lean.Expr.bvar 0))
    (Lean.Expr.lit (Lean.Literal.natVal 0)))
  (Lean.BinderInfo.default)
elab "constNatZero_6" : term => return constNatZero_6

#testOptimize [ "ConstNatZero_6" ] ∀ (x : Nat), x < Nat.zero ===> constNatZero_6

-- [Nat.zero, Nat.zero] ===> [Expr.lit (Literal.natVal 0), Expr.lit (Literal.natVal 0)]
def constNatZero_7 : Expr :=
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.lit (Lean.Literal.natVal 0)))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `List.cons [Lean.Level.zero]) (Lean.Expr.const `Nat []))
      (Lean.Expr.lit (Lean.Literal.natVal 0)))
    (Lean.Expr.app (Lean.Expr.const `List.nil [Lean.Level.zero]) (Lean.Expr.const `Nat [])))

elab "constNatZero_7" : term => return constNatZero_7

#testOptimize [ "ConstNatZero_7" ] [Nat.zero, Nat.zero] ===> constNatZero_7


end Test.NormNatZero
