import Lean
import Tests.Utils

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

-- ¬ (if c then a else b) ===> ¬ (Blaster.dite' (true = c) (λ _ => a) (λ _ => b))
#testOptimize [ "NotUnchanged_5" ]
  ∀ (c : Bool) (a b : Prop), ¬ (if c then a else b) ===>
  ∀ (c : Bool) (a b : Prop), ¬ (Blaster.dite' (true = c) (λ _ => a) (λ _ => b))

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


/-! Test cases for normalization rule `¬ (0 < e) ==> 0 = e` (with Type(e) = Nat). -/

-- ¬ (0 < n) ===> 0 = n
#testOptimize [ "NotZeroLt_1" ] (norm-result: 1) ∀ (n : Nat), ¬ (0 < n) ===> ∀ (n : Nat), 0 = n

-- ¬ (n > 0) ===> 0 = n
#testOptimize [ "NotZeroLt_2" ] (norm-result: 1) ∀ (n : Nat), ¬ (n > 0) ===> ∀ (n : Nat), 0 = n

-- ¬ (0 < n + m) ===> 0 = Nat.add n m
#testOptimize [ "NotZeroLt_3" ] (norm-result: 1) ∀ (n m : Nat), ¬ (0 < n + m) ===> ∀ (n m : Nat), 0 = Nat.add n m

-- (¬ (0 < n)) = (0 = n) ===> True
#testOptimize [ "NotZeroLt_4" ] ∀ (n : Nat), (¬ (0 < n)) = (0 = n) ===> True

-- ¬ (0 < n) → n = 0 ===> True
-- NOTE: the normalized hypothesis `0 = n` rewrites `n` to `0` in the conclusion
#testOptimize [ "NotZeroLt_5" ] ∀ (n : Nat), ¬ (0 < n) → n = 0 ===> True

-- ¬ (0 < n) → n + m = m ===> True
#testOptimize [ "NotZeroLt_6" ] ∀ (n m : Nat), ¬ (0 < n) → n + m = m ===> True

-- ¬ (0 < 5) ===> False
#testOptimize [ "NotZeroLt_7" ] ¬ ((0 : Nat) < 5) ===> False

-- ¬ (0 < 0) ===> True
#testOptimize [ "NotZeroLt_8" ] ¬ ((0 : Nat) < 0) ===> True

-- let x := n + 1; ¬ (0 < x) ===> False
#testOptimize [ "NotZeroLt_9" ] ∀ (n : Nat), let x := n + 1; ¬ (0 < x) ===> False

-- ¬ (¬ (0 < n)) ===> 0 < n
#testOptimize [ "NotZeroLt_10" ] (norm-result: 1) ∀ (n : Nat), ¬ (¬ (0 < n)) ===> ∀ (n : Nat), 0 < n


/-! Test cases for normalization rule `¬ (0 = e) ==> 0 < e` (with Type(e) = Nat). -/

-- ¬ (0 = n) ===> 0 < n
#testOptimize [ "NotZeroEq_1" ] (norm-result: 1) ∀ (n : Nat), ¬ (0 = n) ===> ∀ (n : Nat), 0 < n

-- ¬ (n = 0) ===> 0 < n
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotZeroEq_2" ] (norm-result: 1) ∀ (n : Nat), ¬ (n = 0) ===> ∀ (n : Nat), 0 < n

-- n ≠ 0 ===> 0 < n
#testOptimize [ "NotZeroEq_3" ] (norm-result: 1) ∀ (n : Nat), n ≠ 0 ===> ∀ (n : Nat), 0 < n

-- ¬ (n + m = 0) ===> 0 < Nat.add n m
#testOptimize [ "NotZeroEq_4" ] (norm-result: 1) ∀ (n m : Nat), ¬ (n + m = 0) ===> ∀ (n m : Nat), 0 < Nat.add n m

-- (¬ (0 = n)) = (0 < n) ===> True
#testOptimize [ "NotZeroEq_5" ] ∀ (n : Nat), (¬ (0 = n)) = (0 < n) ===> True

-- ¬ (0 = n) → 0 < n ===> True
#testOptimize [ "NotZeroEq_6" ] ∀ (n : Nat), ¬ (0 = n) → 0 < n ===> True

-- ¬ (0 = n) → ¬ (0 < n) ===> 0 = n
-- NOTE: the normalized hypothesis `0 < n` reduces the conclusion to `False`,
--       and `0 < n → False` is then normalized to `¬ (0 < n)` and finally to `0 = n`.
#testOptimize [ "NotZeroEq_7" ] (norm-result: 1) ∀ (n : Nat), ¬ (0 = n) → ¬ (0 < n) ===> ∀ (n : Nat), 0 = n

-- ¬ (0 = n) → n = 0 ===> 0 = n
#testOptimize [ "NotZeroEq_8" ] (norm-result: 1) ∀ (n : Nat), ¬ (0 = n) → n = 0 ===> ∀ (n : Nat), 0 = n

-- ¬ (0 = 5) ===> True
#testOptimize [ "NotZeroEq_9" ] ¬ ((0 : Nat) = 5) ===> True

-- ¬ (0 = 0) ===> False
#testOptimize [ "NotZeroEq_10" ] ¬ ((0 : Nat) = 0) ===> False


/-! Test cases to ensure that the following normalization rules are not applied wrongly:
     - `¬ (0 < e) ==> 0 = e` (with Type(e) = Nat)
     - `¬ (0 = e) ==> 0 < e` (with Type(e) = Nat)
-/

-- ¬ (1 < n) ===> ¬ (1 < n)
#testOptimize [ "NotZeroNatUnchanged_1" ] (norm-result: 1) ∀ (n : Nat), ¬ (1 < n) ===> ∀ (n : Nat), ¬ (1 < n)

-- ¬ (m < n) ===> ¬ (m < n)
#testOptimize [ "NotZeroNatUnchanged_2" ] ∀ (n m : Nat), ¬ (m < n) ===> ∀ (n m : Nat), ¬ (m < n)

-- ¬ (1 = n) ===> ¬ (1 = n)
#testOptimize [ "NotZeroNatUnchanged_3" ] (norm-result: 1) ∀ (n : Nat), ¬ (1 = n) ===> ∀ (n : Nat), ¬ (1 = n)

-- ¬ (n = m) ===> ¬ (n = m)
#testOptimize [ "NotZeroNatUnchanged_4" ] ∀ (n m : Nat), ¬ (n = m) ===> ∀ (n m : Nat), ¬ (n = m)

-- ¬ (0 < i) ===> ¬ (0 < i) (with Type(i) = Int)
#testOptimize [ "NotZeroIntUnchanged_5" ] (norm-result: 1) ∀ (i : Int), ¬ (0 < i) ===> ∀ (i : Int), ¬ (0 < i)

#testOptimize [ "NotZeroIntUnchanged_6" ] (norm-result: 1) ∀ (i : Int), ¬ (0 = i) ===> ∀ (i : Int), ¬ (0 = i)


/-! Test cases for simplification rules:
     - `¬ (¬ e1 ∧ ¬ e2) ==> e1 ∨ e2`
     - `¬ (¬ e1 ∨ ¬ e2) ==> e1 ∧ e2`
-/

-- ¬ (¬ a ∧ ¬ b) ===> a ∨ b
#testOptimize [ "NotDeMorgan_1" ] ∀ (a b : Prop), ¬ (¬ a ∧ ¬ b) ===> ∀ (a b : Prop), a ∨ b

-- ¬ (¬ a ∨ ¬ b) ===> a ∧ b
#testOptimize [ "NotDeMorgan_2" ] ∀ (a b : Prop), ¬ (¬ a ∨ ¬ b) ===> ∀ (a b : Prop), a ∧ b

-- (¬ (¬ a ∧ ¬ b)) = (a ∨ b) ===> True
#testOptimize [ "NotDeMorgan_3" ] ∀ (a b : Prop), (¬ (¬ a ∧ ¬ b)) = (a ∨ b) ===> True

-- (¬ (¬ a ∨ ¬ b)) = (a ∧ b) ===> True
#testOptimize [ "NotDeMorgan_4" ] ∀ (a b : Prop), (¬ (¬ a ∨ ¬ b)) = (a ∧ b) ===> True

-- ¬ (¬ a ∧ ¬ a) ===> a
#testOptimize [ "NotDeMorgan_5" ] ∀ (a : Prop), ¬ (¬ a ∧ ¬ a) ===> ∀ (a : Prop), a

-- ¬ (¬ a ∨ ¬ a) ===> a
#testOptimize [ "NotDeMorgan_6" ] ∀ (a : Prop), ¬ (¬ a ∨ ¬ a) ===> ∀ (a : Prop), a

-- ¬ (¬ (a ∨ b) ∧ ¬ c) ===> c ∨ a ∨ b
-- NOTE: reordering applied on commutative operators
#testOptimize [ "NotDeMorgan_7" ] ∀ (a b c : Prop), ¬ (¬ (a ∨ b) ∧ ¬ c) ===> ∀ (a b c : Prop), c ∨ a ∨ b

-- ¬ (¬ (¬ a ∧ ¬ b)) ===> ¬ (a ∨ b)
#testOptimize [ "NotDeMorgan_8" ] ∀ (a b : Prop), ¬ (¬ (¬ a ∧ ¬ b)) ===> ∀ (a b : Prop), ¬ (a ∨ b)

-- ¬ (¬ a ∧ ¬ b) → a ∨ b ===> True
#testOptimize [ "NotDeMorgan_9" ] ∀ (a b : Prop), ¬ (¬ a ∧ ¬ b) → a ∨ b ===> True

-- ¬ (¬ a ∨ ¬ b) → a ===> True
#testOptimize [ "NotDeMorgan_10" ] ∀ (a b : Prop), ¬ (¬ a ∨ ¬ b) → a ===> True

-- let x := ¬ a; let y := ¬ b; ¬ (x ∧ y) ===> a ∨ b
#testOptimize [ "NotDeMorgan_11" ] ∀ (a b : Prop), let x := ¬ a; let y := ¬ b; ¬ (x ∧ y) ===> ∀ (a b : Prop), a ∨ b

-- ¬ (¬ a ∧ ¬ b) ===> true = (a || b) (with Type(a) = Type(b) = Bool)
#testOptimize [ "NotDeMorgan_12" ] ∀ (a b : Bool), ¬ (¬ a ∧ ¬ b) ===> ∀ (a b : Bool), true = (a || b)

-- ¬ (¬ a ∨ ¬ b) ===> true = (a && b) (with Type(a) = Type(b) = Bool)
#testOptimize [ "NotDeMorgan_13" ] ∀ (a b : Bool), ¬ (¬ a ∨ ¬ b) ===> ∀ (a b : Bool), true = (a && b)

-- ¬ (¬ (1 < n) ∧ ¬ (1 < m)) ===> 1 < n ∨ 1 < m
#testOptimize [ "NotDeMorgan_14" ] (norm-result: 1)
  ∀ (n m : Nat), ¬ (¬ (1 < n) ∧ ¬ (1 < m)) ===> ∀ (n m : Nat), 1 < n ∨ 1 < m


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `¬ (¬ e1 ∧ ¬ e2) ==> e1 ∨ e2`
     - `¬ (¬ e1 ∨ ¬ e2) ==> e1 ∧ e2`
-/

-- ¬ (a ∨ ¬ b) ===> ¬ (a ∨ ¬ b)
#testOptimize [ "NotDeMorganUnchanged_1" ] ∀ (a b : Prop), ¬ (a ∨ ¬ b) ===> ∀ (a b : Prop), ¬ (a ∨ ¬ b)

-- ¬ (¬ a → ¬ b) ===> ¬ (¬ a → ¬ b)
#testOptimize [ "NotDeMorganUnchanged_2" ] ∀ (a b : Prop), ¬ (¬ a → ¬ b) ===> ∀ (a b : Prop), ¬ (¬ a → ¬ b)

-- ¬ (¬ a ∧ ¬ b ∧ ¬ c) ===> ¬ (¬ a ∧ ¬ b ∧ ¬ c)
-- NOTE: the rule only applies when both operands are negations (`¬ b ∧ ¬ c` is not)
-- NOTE: test case can be reduced to `a ∨ b ∨ c` by extending the de-morgan rule
#testOptimize [ "NotDeMorganUnchanged_3" ]
  ∀ (a b c : Prop), ¬ (¬ a ∧ ¬ b ∧ ¬ c) ===> ∀ (a b c : Prop), ¬ (¬ a ∧ ¬ b ∧ ¬ c)

-- ¬ (¬ (0 < n) ∨ ¬ (0 < m)) ===> ¬ (0 = n ∨ 0 = m)
-- NOTE: `¬ (0 < e) ==> 0 = e` is applied on the operands first, hence the operands are no longer negations
#testOptimize [ "NotDeMorganUnchanged_4" ] (norm-result: 1)
  ∀ (n m : Nat), ¬ (¬ (0 < n) ∨ ¬ (0 < m)) ===> ∀ (n m : Nat), ¬ (0 = n ∨ 0 = m)


end Tests.OptimizeNot
