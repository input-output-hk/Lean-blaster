import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeNot
/-! ## Test objectives to validate normalization and simplification rules on ``Not -/

/-! Test cases for simplification rule `¬ False ==> True`. -/

-- ¬ False ===> True
#testOptimize [ "NotFalse_1" ] ¬ False ===> True

-- ¬ (true = false) ===> True
#testOptimize [ "NotFalse_2" ] ¬ (true = false) ===> True

-- ¬ ((10 : Nat) = 20) ===> True
#testOptimize [ "NotFalse_3" ] ¬ ((10 : Nat) = 20) ===> True

-- ¬ (¬ True) ===> True
#testOptimize [ "NotFalse_4" ] ¬ (¬ True) ===> True

-- ¬ (¬ a ∧ b) ===> True
#testOptimize [ "NotFalse_5" ] ∀ (a : Prop), ¬ (¬ a ∧ a) ===> True

-- ¬ (Nat.ble (10 : Nat) 0) ===> True
#testOptimize [ "NotFalse_6" ] ¬ (Nat.ble (10 : Nat) 0) ===> True

-- ¬ ((a ∨ (b ∧ ¬ b)) ∧ ¬ a) ==> True
#testOptimize [ "NotFalse_7" ] ∀ (a b : Prop), ¬ ((a ∨ (b ∧ ¬ b)) ∧ ¬ a) ===> True


/-! Test cases for simplification rule `¬ True ==> False`. -/

-- ¬ True ===> False
#testOptimize [ "NotTrue_1" ] ¬ True ===> False

-- ¬ (true = true) ===> False
#testOptimize [ "NotTrue_2" ] ¬ (true = true) ===> False

-- ¬ ((10 : Nat) = 10) ===> False
#testOptimize [ "NotTrue_3" ] ¬ ((10 : Nat) = 10) ===> False

-- ¬ (¬ False) ===> False
#testOptimize [ "NotTrue_4" ] ¬ (¬ False) ===> False

-- ¬ (¬ a ∨ a) ===> False
#testOptimize [ "NotTrue_5" ] ∀ (a : Prop), ¬ (¬ a ∨ a) ===> False

-- ¬ (Nat.blt Nat.zero 10) ===> False
#testOptimize [ "NotTrue_6" ] ¬ (Nat.blt Nat.zero 10) ===> False

-- ¬ ((a ∨ (b ∧ ¬ b)) ∨ ¬ a) ==> False
#testOptimize [ "NotTrue_7" ] ∀ (a b : Prop), ¬ ((a ∨ (b ∧ ¬ b)) ∨ ¬ a) ===> False


/-! Test cases for simplification rule `¬ (¬ e) ==> e`. -/

-- ¬ (¬ a) ===> a
#testOptimize [ "Not_1" ] ∀ (a : Prop), ¬ (¬ a) ===> ∀ (a : Prop), a

-- ¬ (¬ a) = a ===> True
#testOptimize [ "Not_2" ] ∀ (a : Prop), ¬ (¬ a) = a ===> True

-- ¬ (¬ (¬ a)) ===> ¬ a
#testOptimize [ "Not_3" ] ∀ (a : Prop), ¬ (¬ (¬ a)) ===> ∀ (a : Prop), ¬ a

-- ¬ (¬ (¬ (¬ a))) ===> a
#testOptimize [ "Not_4" ] ∀ (a : Prop), ¬ (¬ (¬ (¬ a))) ===> ∀ (a : Prop), a

-- ¬ (¬ (a ∧ b)) ===> a ∧ b
#testOptimize [ "Not_5" ] ∀ (a b : Prop), ¬ (¬ (a ∧ b)) ===> ∀ (a b : Prop), a ∧ b

-- ¬ (¬ (a = b)) ===> a = b
#testOptimize [ "Not_6" ] ∀ (a b : Prop), ¬ (¬ (a = b)) ===> ∀ (a b : Prop), a = b

-- ¬ (false = a) ===> a (with Type(a) = Prop)
-- NOTE: `false = a` is interpreted as `(false = true) = a`, which is in turn reduced to
--       `False = a` and then to `¬ a`.
#testOptimize [ "Not_7" ]  ∀ (a : Prop), ¬ (false = a) ===> ∀ (a : Prop), a


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `¬ False ==> True`
     - `¬ True ==> False`
     - `¬ (¬ e) ==> e`
-/

-- ¬ a ===> ¬ a
#testOptimize [ "NotUnchanged_1" ] ∀ (a : Prop), ¬ a ===> ∀ (a : Prop), ¬ a

-- ¬ (a ∧ b) ===> ¬ (a ∧ b)
#testOptimize [ "NotUnchanged_2" ] ∀ (a b : Prop), ¬ (a ∧ b) ===> ∀ (a b : Prop), ¬ (a ∧ b)

-- ¬ (a ∨ b) ===> ¬ (a ∨ b)
#testOptimize [ "NotUnchanged_3" ] ∀ (a b : Prop), ¬ (a ∨ b) ===> ∀ (a b : Prop), ¬ (a ∨ b)

-- ¬ (a → b) ===> ¬ (a → b)
#testOptimize [ "NotUnchanged_4" ] ∀ (a b : Prop), ¬ (a → b) ===> ∀ (a b : Prop), ¬ (a → b)

-- ¬ (if c then a else b) ===> ¬ ((false = c → b) ∧ (true = c → a))
#testOptimize [ "NotUnchanged_5" ] ∀ (c : Bool) (a b : Prop), ¬ (if c then a else b) ===>
                                   ∀ (c : Bool) (a b : Prop), ¬ ((false = c → b) ∧ (true = c → a))

-- ¬ ((¬ a) ∧ b) ===> ¬ ((¬ a) ∧ b)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotUnchanged_6" ] ∀ (a b : Prop), ¬ ((¬ a) ∧ b) ===> ∀ (a b : Prop), ¬ (b ∧ ¬ a)

-- ¬ ((¬ a) = b) ===> ¬ ((¬ a) = b)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotUnchanged_7" ] ∀ (a b : Prop), ¬ ((¬ a) = b) ===> ∀ (a b : Prop), ¬ (b = ¬ a)


/-! Test cases for simplification rule `¬ (false = e) ==> true = e`. -/

-- ¬ (false = a) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_1" ] ∀ (a : Bool), ¬ (false = a) ===> ∀ (a : Bool), true = a

-- (¬ (false = a)) = (true = a) ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_2" ] ∀ (a : Bool), (¬ (false = a)) = (true = a) ===> True

-- ¬ (a = false) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_3" ] ∀ (a : Bool), ¬ (a = false) ===> ∀ (a : Bool), true = a

-- (¬ (false = a)) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_4" ] ∀ (a : Bool), (¬ (false = a)) = a ===> True

-- ¬ (a = false) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_5" ] ∀ (a : Bool), (¬ (a = false)) = a ===> True

-- ¬ (a = (b && ! b)) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_6" ] ∀ (a b : Bool), ¬ (a = (b && !b)) ===> ∀ (a : Bool), true = a

-- ¬ (a = (b && ! b)) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_7" ] ∀ (a b : Bool), (¬ (a = (b && !b))) = a ===> True

-- ¬ (!a) ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_8" ] ∀ (a : Bool), (¬ !a) ===> ∀ (a : Bool), true = a

-- let x := a || a in
-- let y := ! a || ! x in
-- ¬ y ===> true = a (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_9" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; ¬ y ===> ∀ (a : Bool), true = a

-- let x := a || a in
-- let y := ! a || ! x in
-- (¬ y) = a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_10" ] ∀ (a : Bool), let x := a || a; let y := !a || !x; (¬ y) = a ===> True


/-! Test cases for simplification rule `¬ (true = e) ==> false = e`. -/

-- ¬ (true = a) ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_1" ] ∀ (a : Bool), ¬ (true = a) ===> ∀ (a : Bool), false = a

-- (¬ (true = a)) = (false = a) ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_2" ] ∀ (a : Bool), (¬ (true = a)) = (false = a) ===> True

-- ¬ (a = true) ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_3" ] ∀ (a : Bool), ¬ (a = true) ===> ∀ (a : Bool), false = a

-- ¬ (true = a) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_4" ] ∀ (a : Bool), (¬ (true = a)) = not a ===> True

-- ¬ (a = false) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_5" ] ∀ (a : Bool), (¬ (a = true)) = not a ===> True

-- ¬ (a = (b || ! b)) ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_6" ] ∀ (a b : Bool), ¬ (a = (b || !b)) ===> ∀ (a : Bool), false = a

-- ¬ (a = (b || ! b)) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_7" ] ∀ (a b : Bool), (¬ (a = (b || !b))) = not a ===> True

-- ¬ a ===> false = a  (with Type(a) = Bool)
#testOptimize [ "NotEqFalse_8" ] ∀ (a : Bool), ¬ a ===> ∀ (a : Bool), false = a

-- let x := a && a in
-- let y := a || x in
-- ¬ y ===> false = a (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_9" ] ∀ (a : Bool), let x := a && a; let y := a || x; ¬ y ===> ∀ (a : Bool), false = a

-- let x := a && a in
-- let y := a || x in
-- (¬ y) = not a ===> True (with Type(a) = Bool)
#testOptimize [ "NotEqTrue_10" ] ∀ (a : Bool), let x := a && a; let y := a || x; (¬ y) = not a ===> True


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `¬ (false = e) ==> true = e`
     - `¬ (true = e) ==> false = e`
-/

-- ¬ (a = b) ===> ¬ (a = b) (with Type(a) = Type(b) = Bool)
#testOptimize [ "NotEqBoolCstUnchanged_1" ] ∀ (a b : Bool), ¬ (a = b) ===> ∀ (a b : Bool), ¬ (a = b)

-- ¬ ((!a) = b) ===> ¬ ((!a) = b) (with Type(a) = Type(b) = Bool)
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotEqBoolCstUnchanged_2" ] ∀ (a b : Bool), ¬ ((!a) = b) ===> ∀ (a b : Bool), ¬ (b = !a)


end Tests.OptimizeNot
