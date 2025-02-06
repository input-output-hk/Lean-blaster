import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.DecideEq

/-! ## Test objectives to validate `Decidable.decide` simplification rules on `Eq`. -/


/-! Test cases for simplification rule `true = (a == b) ==> a = b (if isCompatibleBeqType Type(a))`. -/

variable (p : Bool)
variable (q : Bool)

-- true = (p == q) ===> p = q (with Type(p) = Bool)
#testOptimize [ "EqTrueBeq_1"] true = (p == q) ===> p = q

variable (n : Nat)
variable (m : Nat)

-- true = (n == m) ===> n = m (with Type(n) = Nat)
#testOptimize [ "EqTrueBeq_2"] true = (n == m) ===> n = m

variable (x : Int)
variable (y : Int)

-- true = (x == y) ===> x = y (with Type(x) = Int)
#testOptimize [ "EqTrueBeq_3"] true = (x == y) ===> x = y

variable (s : String)
variable (t : String)

-- true = (s == t) ===> s = t (with Type(s) = String)
#testOptimize [ "EqTrueBeq_4"] true = (s == t) ===> s = t

-- (true = (p == q)) = (p = q) ===> True (with Type(p) = Bool)
#testOptimize [ "EqTrueBeq_5"] (true = (p == q)) = (p = q) ===> True

-- (true = (n == m)) = (n = m) ===> True (with Type(n) = Nat)
#testOptimize [ "EqTrueBeq_6"] (true = (n == m)) = (n = m) ===> True

-- (true = (x == y)) = (x = y) ===> True (with Type(x) = Int)
#testOptimize [ "EqTrueBeq_7"] (true = (x == y)) = (x = y) ===> True

-- (true = (s == t)) = (s = t) ===> True (with Type(s) = String)
#testOptimize [ "EqTrueBeq_8"] (true = (s == t)) = (s = t) ===> True


/-! Test cases to ensure that simplification rule `true = (a == b) ==> (a = b) (if isCompatibleBeqType Type(a))`
    is not applied wrongly.
-/

-- ∀ (α : Type) (xs ys : List α), [BEq α] → true = (xs == ys) ===>
-- ∀ (α : Type) (xs ys : List α), [BEq α] → true = (List.beq xs ys)
#testOptimize [ "EqTrueBeqUnchanged_1"] ∀ (α : Type) (xs ys : List α), [BEq α] → true = (xs == ys) ===>
                                        ∀ (α : Type) (xs ys : List α), [BEq α] → true = (List.beq xs ys)

inductive Color where
  | transparent : Color
  | red : Color → Color
  | blue : Color → Color
  | yellow : Color → Color
 deriving Repr

-- ∀ (rb ry : Color), [BEq Color] → true = (rb == ry) ===>
-- ∀ (rb ry : Color), [BEq Color] → true = (rb == ry)
#testOptimize [ "EqTrueBeqUnchanged_2"] ∀ (rb ry : Color), [BEq Color] → true = (rb == ry) ===>
                                        ∀ (rb ry : Color), [BEq Color] → true = (rb == ry)


/-! Test cases for simplification rule `false = (a == b) ==> ¬ (a = b) (if isCompatibleBeqType Type(a))`. -/

-- false = (p == q) ===> ¬ (p = q) (with Type(p) = Bool)
#testOptimize [ "EqFalseBeq_1"] false = (p == q) ===> ¬ (p = q)

-- false = (n == m) ===> ¬ (n = m) (with Type(n) = Nat)
#testOptimize [ "EqFalseBeq_2"] false = (n == m) ===> ¬ (n = m)

-- false = (x == y) ===> ¬ (x = y) (with Type(x) = Int)
#testOptimize [ "EqFalseBeq_3"] false = (x == y) ===> ¬ (x = y)

-- false = (s == t) ===> ¬ (s = t) (with Type(s) = String)
#testOptimize [ "EqFalseBeq_4"] false = (s == t) ===> ¬ (s = t)

-- (false = (p == q)) = ¬ (p = q) ===> True (with Type(p) = Bool)
#testOptimize [ "EqFalseBeq_5"] (false = (p == q)) = ¬ (p = q) ===> True

-- (false = (n == m)) = ¬ (n = m) ===> True (with Type(n) = Nat)
#testOptimize [ "EqFalseBeq_6"] (false = (n == m)) = ¬ (n = m) ===> True

-- (false = (x == y)) = ¬ (x = y) ===> True (with Type(x) = Int)
#testOptimize [ "EqFalseBeq_7"] (false = (x == y)) = ¬ (x = y) ===> True

-- (false = (s == t)) = ¬ (s = t) ===> True (with Type(s) = String)
#testOptimize [ "EqFalseBeq_8"] (false = (s == t)) = ¬ (s = t) ===> True


/-! Test cases to ensure that simplification rule `false = (a == b) ==> ¬ (a = b) (if isCompatibleBeqType Type(a))`
    is not applied wrongly.
-/

-- ∀ (α : Type) (xs ys : List α), [BEq α] → false = (xs == ys) ===>
-- ∀ (α : Type) (xs ys : List α), [BEq α] → false = (List.beq xs ys)
#testOptimize [ "EqFalseBeqUnchanged_1"] ∀ (α : Type) (xs ys : List α), [BEq α] → false = (xs == ys) ===>
                                         ∀ (α : Type) (xs ys : List α), [BEq α] → false = (List.beq xs ys)

-- ∀ (rb ry : Color), [BEq Color] → false = (rb == ry) ===>
-- ∀ (rb ry : Color), [BEq Color] → false = (rb == ry)
#testOptimize [ "EqFalseBeqUnchanged_2"] ∀ (rb ry : Color), [BEq Color] → false = (rb == ry) ===>
                                         ∀ (rb ry : Color), [BEq Color] → false = (rb == ry)


/-! Test cases for simplification rule:
    `c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if isCompatibleBeqType Type(a))`
-/

-- p = m == n ===> (true = p) = (n = m)
#testOptimize [ "EqBoolBeq_1" ] p = (m == n) ===> (true = p) = (n = m)

-- p = m == n ===> (true = p) = (n = m)
#testOptimize [ "EqBoolBeq_2" ] (m == n) = p ===> (true = p) = (n = m)

-- (!p) = (m == n) ===> (false = p) = (n = m)
#testOptimize [ "EqBoolBeq_3" ] (!p) = (m == n) ===> (false = p) = (n = m)

-- (m == n) = !p ===> (false = p) = (n = m)
#testOptimize [ "EqBoolBeq_4" ] (m == n) = !p ===> (false = p) = (n = m)

-- (x == y) = (m == n) ===> (x = y) = (n = m)
#testOptimize [ "EqBoolBeq_5" ] (x == y) = (m == n) ===> (x = y) = (n = m)

-- (x != y) = (m == n) ===> (¬ (x = y)) = (n = m)
#testOptimize [ "EqBoolBeq_6" ] (x != y) = (m == n) ===> (¬ (x = y)) = (n = m)

-- (m == n) = (x != y) ===> (¬ (x = y)) = (n = m)
#testOptimize [ "EqBoolBeq_7" ] (m == n) = (x != y) ===> (¬ (x = y)) = (n = m)

-- (m == n) = (n != m) ===> False
#testOptimize [ "EqBoolBeq_8" ] (m == n) = (n != m) ===> False

-- (n != m) = (m == n) ===> False
#testOptimize [ "EqBoolBeq_9" ] (n != m) = (m == n) ===> False

-- (n != m) = (m = n) ===> False
#testOptimize [ "EqBoolBeq_10" ] (n != m) = (m = n) ===> False

-- (n ≠ m) = (m == n) ===> False
#testOptimize [ "EqBoolBeq_11" ] (n ≠ m) = (m == n) ===> False

-- (n = m) = (m == n) ===> True
#testOptimize [ "EqBoolBeq_12" ] (n = m) = (m == n) ===> True

-- (n ≠ m) = (m != n) ===> True
#testOptimize [ "EqBoolBeq_13" ] (n ≠ m) = (m != n) ===> True

-- ((x ≠ y) = (m != n)) = (p == q) ===> ((x = y) = (n = m)) = (p = q)
#testOptimize [ "EqBoolBeq_14" ] ((x ≠ y) = (m != n)) = (p == q) ===> ((x = y) = (n = m)) = (p = q)


-- (p = (m == n)) = ((n = m) = p) ===> True
#testOptimize [ "EqBoolBeq_15" ] (p = (m == n)) = ((n = m) = p) ===> True

-- ((!p) = (m == n)) = ((n = m) = (false = p)) ===> True
#testOptimize [ "EqBoolBeq_16" ] ((!p) = (m == n)) = ((n = m) = (false = p)) ===> True

-- ((x == y) = (m == n)) = ((n = m) = (y = x)) ===> True
#testOptimize [ "EqBoolBeq_17" ] ((x == y) = (m == n)) = ((n = m) = (y = x)) ===> True

-- ((x != y) = (m == n)) = ((n = m) = (x ≠ y)) ===> True
#testOptimize [ "EqBoolBeq_18" ] ((x != y) = (m == n)) = ((n = m) = (x ≠ y)) ===> True

-- ((m == n) = (x != y)) =((x ≠ y) = (n = m)) ===> True
#testOptimize [ "EqBoolBeq_19" ] ((m == n) = (x != y)) =((x ≠ y) = (n = m)) ===> True

-- (((x ≠ y) = (m != n)) = (p == q)) = ((q = p) = ((n = m) = (y = x))) ===> True
#testOptimize [ "EqBoolBeq_20" ] (((x ≠ y) = (m != n)) = (p == q)) = ((q = p) = ((n = m) = (y = x))) ===> True

-- ∀ (x y : Int) (b c : Bool), ((x < y) == b) = c ===>
-- ∀ (x y : Int) (b c : Bool), ((true = b) = (x < y)) = (true = c)
#testOptimize [ "EqBoolBeq_21"] ∀ (x y : Int) (b c : Bool), ((x < y) == b) = c ===>
                                ∀ (x y : Int) (b c : Bool), ((true = b) = (x < y)) = (true = c)

-- ∀ (x y : Int) (b c : Bool), (((x < y) == b) = c) = (((x < y) = b) = c) ===> True
#testOptimize [ "EqBoolBeq_22"] ∀ (x y : Int) (b c : Bool),
                                  (((x < y) == b) = c) = (((x < y) = b) = c) ===> True


/-! Test cases to ensure that simplification rule
    `c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if isCompatibleBeqType Type(a))` is not applied wrongly.
-/

-- ∀ (α : Type) (xs ys : List α), [BEq α] → p = (xs == ys) ===>
-- ∀ (α : Type) (xs ys : List α), [BEq α] → p = (List.beq xs ys)
#testOptimize [ "EqBoolBeqUnchanged_1"] ∀ (α : Type) (xs ys : List α), [BEq α] → p = (xs == ys) ===>
                                        ∀ (α : Type) (xs ys : List α), [BEq α] → p = (List.beq xs ys)

-- ∀ (α : Type) (xs ys : List α), [BEq α] → (xs == ys) = !p ===>
-- ∀ (α : Type) (xs ys : List α), [BEq α] → (!p) = (List.beq xs ys)
#testOptimize [ "EqBoolBeqUnchanged_2"] ∀ (α : Type) (xs ys : List α), [BEq α] → (xs == ys) = !p ===>
                                        ∀ (α : Type) (xs ys : List α), [BEq α] → (!p) = (List.beq xs ys)

-- ∀ (rb ry : Color), [BEq Color] → false = (rb == ry) ===>
-- ∀ (rb ry : Color), [BEq Color] → false = (rb == ry)
#testOptimize [ "EqBooBeqUnchanged_3"] ∀ (rb ry : Color), [BEq Color] → p = (rb == ry) ===>
                                       ∀ (rb ry : Color), [BEq Color] → p = (rb == ry)



/-! Test cases for simplification rule `(B1 = a) = (B2 = b) ==> NOP(B1, a) = NOP(B2, b)`. -/

-- (true = p) = (true = q) ===> p = q
#testOptimize [ "EqBoolEqBool_1"] (true = p) = (true = q) ===> p = q

-- (true = p) = (false = q) ===> p = !q
#testOptimize [ "EqBoolEqBool_2"] (true = p) = (false = q) ===> p = !q

-- (false = p) = (true = q) ===> q = !p
#testOptimize [ "EqBoolEqBool_3"] (false = p) = (true = q) ===> q = !p

-- (false = p) = (false = q) ===> p = q
#testOptimize [ "EqBoolEqBool_4"] (false = p) = (false = q) ===> p = q

-- (false = p) = (true = p) ===> False
#testOptimize [ "EqBoolEqBool_5"] (false = p) = (true = p) ===> False

-- (true = p) = q ===> p = q
#testOptimize [ "EqBoolEqBool_6"] (true = p) = q ===> p = q

-- (true = p) = ¬ q ===> p = !q
#testOptimize [ "EqBoolEqBool_7"] (true = p) = ¬ q ===> p = !q

-- ¬ p = true = q ===> q = !p
#testOptimize [ "EqBoolEqBool_8"] ¬ p = true = q ===> q = !p

-- ¬ p = true = p ===> False
#testOptimize [ "EqBoolEqBool_9"] ¬ p = true = p ===> False

-- ¬ p = false = p ===> True
#testOptimize [ "EqBoolEqBool_10"] ¬ p = false = p ===> True

-- p = (false = p) ===> False
#testOptimize [ "EqBoolEqBool_11"] p = (false = p) ===> False

-- p = (true = p) ===> True
#testOptimize [ "EqBoolEqBool_12"] p = (true = p) ===> True

-- (true = (p == q)) = (true = (x == y)) ===> (p = q) = (x = y)
#testOptimize [ "EqBoolEqBool_13"] (true = (p == q)) = (true = (x == y)) ===> (p = q) = (x = y)

-- (true = (p == q)) = (p ≠ q) ===> False
#testOptimize [ "EqBoolEqBool_14"] (true = (p == q)) = (p ≠ q) ===> False

-- (p ∧ ((x < y) ∨ ¬ (y > x))) = ¬ p ===> False
#testOptimize [ "EqBoolEqBool_15"] (p ∧ ((x < y) ∨ ¬ (y > x))) = ¬ p ===> False

-- (p ∧ ((x < y) ∨ ¬ (y > x))) = (¬ (¬ (¬ p ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ q ∨ q))) ===> False
#testOptimize [ "EqBoolEqBool_16"] (p ∧ ((x < y) ∨ ¬ (y > x))) =
                                   (¬ (¬ (¬ p ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ q ∨ q))) ===> False

-- (¬ (p ∧ ((x < y) ∨ ¬ (y > x)))) = ¬ q ===> p = q
#testOptimize [ "EqBoolEqBool_17"] (¬ (p ∧ ((x < y) ∨ ¬ (y > x)))) = ¬ q ===> p = q

-- (p ∧ ((x < y) ∨ ¬ (y > x))) = (¬ (¬ (¬ q ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ p ∨ p))) ===> p = !q
#testOptimize [ "EqBoolEqBool_18"] (p ∧ ((x < y) ∨ ¬ (y > x))) =
                                   (¬ (¬ (¬ q ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ p ∨ p))) ===> p = !q

-- ((true = p) = (true = q)) = (q = p) ===> True
#testOptimize [ "EqBoolEqBool_19"] ((true = p) = (true = q)) = (q = p) ===> True

-- ((true = p) = (false = q)) = ((!q) = p) ===> True
#testOptimize [ "EqBoolEqBool_20"] ((true = p) = (false = q)) = ((!q) = p) ===> True

-- ((false = p) = (true = q)) = (q = !p) ===> True
#testOptimize [ "EqBoolEqBool_21"] ((false = p) = (true = q)) = (q = !p) ===> True

-- ((false = p) = (false = q)) = (q = p) ===> True
#testOptimize [ "EqBoolEqBool_22"] ((false = p) = (false = q)) = (q = p) ===> True

-- ((true = p) = q) = (q = p) ===> True
#testOptimize [ "EqBoolEqBool_23"] ((true = p) = q) = (q = p) ===> True

-- ((true = p) = ¬ q) = ((!q) = p) ===> True
#testOptimize [ "EqBoolEqBool_24"] ((true = p) = ¬ q) = ((!q) = p) ===> True

-- (¬ p = true = q) = (q = !p) ===> True
#testOptimize [ "EqBoolEqBool_25"] (¬ p = true = q) = (q = !p) ===> True

-- ((true = (p == q)) = (true = (x == y))) = ((y = x) = (q = p)) ===> True
#testOptimize [ "EqBoolEqBool_26"] ((true = (p == q)) = (true = (x == y))) = ((y = x) = (q = p)) ===> True

-- ((¬ (p ∧ ((x < y) ∨ ¬ (y > x)))) = ¬ q) = (q = p) ===> True
#testOptimize [ "EqBoolEqBool_27"] ((¬ (p ∧ ((x < y) ∨ ¬ (y > x)))) = ¬ q) = (q = p) ===> True

-- ((p ∧ ((x < y) ∨ ¬ (y > x))) = (¬ (¬ (¬ q ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ p ∨ p)))) = ((!q) = p) ===> True
#testOptimize [ "EqBoolEqBool_28"] ((p ∧ ((x < y) ∨ ¬ (y > x))) = (¬ (¬ (¬ q ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ p ∨ p)))) = ((!q) = p) ===> True


/-! Test cases to ensure that simplification rule `(B1 = a) = (B2 = b) ==> NOP(B1, a) = NOP(B2, b)`
    is not applied wrongly.
-/

-- (true = p) = (x < y) ===> (true = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_1"] (true = p) = (x < y) ===> (true = p) = (x < y)

-- (false = p) = (x < y) ===> (false = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_2"] (false = p) = (x < y) ===> (false = p) = (x < y)

-- p = (x < y) ===> (true = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_3"] p = (x < y) ===> (true = p) = (x < y)

-- (¬ p) = (x < y) ===> (false = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_4"]  (¬ p) = (x < y) ===> (false = p) = (x < y)

-- (x < y) = (true = p) ===> (true = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_5"] (x < y) = (true = p) ===> (true = p) = (x < y)

-- (x < y) = (false = p) ===> (false = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_6"] (x < y) = (false = p) ===> (false = p) = (x < y)

-- (x < y) = p ===> (true = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_7"] (x < y) = p  ===> (true = p) = (x < y)

-- (x < y) = ¬ p ===> (false = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_8"] (x < y) = ¬ p ===> (false = p) = (x < y)

-- (p ∧ ((x < y) ∨ ¬ (y > x))) = ((x > y) ∧ (¬ q ∨ q)) ===> (true = p) = (y < x)
#testOptimize [ "EqBoolEqBoolUnchanged_9"] (p ∧ ((x < y) ∨ ¬ (y > x))) = ((x > y) ∧ (¬ q ∨ q)) ===>
                                           (true = p) = (y < x)

-- ((x < y) ∧ (¬ q ∨ q)) = (¬ (¬ (¬ p ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ q ∨ q))) ===>
-- (false = p) = (x < y)
#testOptimize [ "EqBoolEqBoolUnchanged_10"] ((x < y) ∧ (¬ q ∨ q)) = (¬ (¬ (¬ p ∧ ((x < y) ∨ ¬ (y > x))) ∧ (¬ q ∨ q))) ===>
                                            (false = p) = (x < y)


/-! Test cases for simplification rule `true = decide e ==> e`. -/

-- ∀ (a : Prop), [Decidable a] → true = decide a ===> ∀ (a : Prop), a
#testOptimize [ "DecideEqTrue_1"] ∀ (a : Prop), [Decidable a] → true = decide a ===> ∀ (a : Prop), a


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → true = decide (a ∧ b) ===>
-- ∀ (a b : Prop), a ∧ b
#testOptimize [ "DecideEqTrue_2"] ∀ (a b : Prop), [Decidable a] → [Decidable b] → true = decide (a ∧ b) ===>
                                  ∀ (a b : Prop), a ∧ b

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → true = decide (a ∨ b) ===>
-- ∀ (a b : Prop), a ∨ b
#testOptimize [ "DecideEqTrue_3"] ∀ (a b : Prop), [Decidable a] → [Decidable b] → true = decide (a ∨ b) ===>
                                  ∀ (a b : Prop), a ∨ b

-- true = decide (x ≤ y) ===> x ≤ y
#testOptimize [ "DecideEqTrue_4"] true = decide (x ≤ y) ===> x ≤ y


variable (z : Int)
-- true = decide (x ≤ y ∧ z ≥ y) ===> x ≤ y ∧ y ≤ z
#testOptimize [ "DecideEqTrue_5"] true = decide (x ≤ y ∧ z ≥ y) ===> x ≤ y ∧ y ≤ z

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
-- ∀ (x y : Int), x < y
#testOptimize [ "DecideEqTrue_6"] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                    decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
                                  ∀ (x y : Int), x < y

-- ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), x ≤ y
#testOptimize [ "DecideEqTrue_7"] ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), x ≤ y


-- ∀ (a : Prop), [Decidable a] → (true = decide a) = a ===> True
#testOptimize [ "DecideEqTrue_8"] ∀ (a : Prop), [Decidable a] → (true = decide a) = a ===> True


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (true = decide (a ∧ b)) = (a ∧ b) ===> True
#testOptimize [ "DecideEqTrue_9"] ∀ (a b : Prop), [Decidable a] → [Decidable b] →
                                    (true = decide (a ∧ b)) = (a ∧ b) ===> True


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (true = decide (a ∨ b)) = (a ∨ b) ===> True
#testOptimize [ "DecideEqTrue_10"] ∀ (a b : Prop), [Decidable a] → [Decidable b] →
                                     (true = decide (a ∨ b)) = (a ∨ b) ===> True

-- (true = decide (x ≤ y)) = (x ≤ y) ===> True
#testOptimize [ "DecideEqTrue_11"] (true = decide (x ≤ y)) = (x ≤ y) ===> True

-- (true = decide (x ≤ y ∧ z ≥ y)) = (x ≤ y ∧ y ≤ z) ===> True
#testOptimize [ "DecideEqTrue_12"] (true = decide (x ≤ y ∧ z ≥ y)) = (x ≤ y ∧ y ≤ z) ===> True

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  (decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y)) = (x < y) ===> True
#testOptimize [ "DecideEqTrue_13"] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                     (decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y)) = (x < y) ===> True

-- ∀ (x y : Nat), (x ≤ y && x ≤ y) = (x ≤ y) ===> True
#testOptimize [ "DecideEqTrue_14"] ∀ (x y : Nat), (x ≤ y && x ≤ y) = (x ≤ y) ===> True


-- ∀ (x y z : Int) (a b c : Bool),
--  (if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
-- ∀ (x y z : Int) (a : Bool), (if true = a ∧ (x ≤ y) then x else y) < z
#testOptimize [ "DecideEqTrue_15"] ∀ (x y z : Int) (a b c : Bool),
                                     (if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
                                   ∀ (x y z : Int) (a : Bool), (if true = a ∧ (x ≤ y) then x else y) < z

-- ∀ (x y z : Int) (a b c : Bool),
--  ((if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z) =
--  (z > (if (x ≤ y) ∧ a then x else y)) ===> True
#testOptimize [ "DecideEqTrue_16"] ∀ (x y z : Int) (a b c : Bool),
                                     ((if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z) =
                                     (z > (if (x ≤ y) ∧ a then x else y)) ===> True


/-! Test cases for simplification rule `false = decide e ==> ¬ e`. -/

-- ∀ (a : Prop), [Decidable a] → false = decide a ===> ∀ (a : Prop), ¬ a
#testOptimize [ "DecideEqFalse_1"] ∀ (a : Prop), [Decidable a] → false = decide a ===> ∀ (a : Prop), ¬ a


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∧ b) ===>
-- ∀ (a b : Prop), ¬ a ∧ b
#testOptimize [ "DecideEqFalse_2"] ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∧ b) ===>
                                   ∀ (a b : Prop), ¬ (a ∧ b)

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∨ b) ===>
-- ∀ (a b : Prop), ¬ (a ∨ b)
#testOptimize [ "DecideEqFalse_3"] ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∨ b) ===>
                                   ∀ (a b : Prop), ¬ (a ∨ b)

-- false = decide (x ≤ y) ===> ¬ x ≤ y
#testOptimize [ "DecideEqFalse_4"] false = decide (x ≤ y) ===> ¬ x ≤ y

-- false = decide (x ≤ y ∧ z ≥ y) ===> ¬ (x ≤ y ∧ y ≤ z)
#testOptimize [ "DecideEqFalse_5"] false = decide (x ≤ y ∧ z ≥ y) ===> ¬ (x ≤ y ∧ y ≤ z)

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
-- ∀ (x y : Int), ¬ x < y
#testOptimize [ "DecideEqFalse_6"] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                     decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
                                   ∀ (x y : Int), ¬ x < y

-- ∀ (x y : Nat) (a b c : Bool), ((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y ===>
-- ∀ (x y : Nat), x ≤ y
#testOptimize [ "DecideEqFalse_7"] ∀ (x y : Nat) (a b c : Bool),
                                    ((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y ===>
                                   ∀ (x y : Nat), x ≤ y

-- ∀ (p q : Prop) (a b c : Bool),
-- [Decidable p] → [Decidable q] →
-- ((a || ((b || c) && !(c || b))) && !a) = ¬ (p ∧ q) ===>
-- ∀ (p q : Prop), p ∧ q
#testOptimize [ "DecideEqFalse_8"] ∀ (p q : Prop) (a b c : Bool), [Decidable p] → [Decidable q] →
                                    ((a || ((b || c) && !(c || b))) && !a) = ¬ (p ∧ q) ===>
                                   ∀ (p q : Prop), p ∧ q

-- ∀ (a : Prop), [Decidable a] → (false = decide a) = ¬ a ===> True
#testOptimize [ "DecideEqFalse_9"] ∀ (a : Prop), [Decidable a] → (false = decide a) = ¬ a ===> True


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (false = decide (a ∧ b)) = ¬ (a ∧ b) ===> True
#testOptimize [ "DecideEqFalse_10"] ∀ (a b : Prop), [Decidable a] → [Decidable b] →
                                      (false = decide (a ∧ b)) = ¬ (a ∧ b) ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (false = decide (a ∨ b)) = ¬ (a ∨ b) ===> True
#testOptimize [ "DecideEqFalse_11"] ∀ (a b : Prop), [Decidable a] → [Decidable b] →
                                      (false = decide (a ∨ b)) = ¬ (a ∨ b) ===> True

-- (false = decide (x ≤ y)) = ¬ x ≤ y ===> True
#testOptimize [ "DecideEqFalse_12"] (false = decide (x ≤ y)) = ¬ x ≤ y ===> True

-- (false = decide (x ≤ y ∧ z ≥ y)) = ¬ (x ≤ y ∧ y ≤ z) ===> True
#testOptimize [ "DecideEqFalse_13"] (false = decide (x ≤ y ∧ z ≥ y)) = ¬ (x ≤ y ∧ y ≤ z) ===> True

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  (decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y)) = ¬ (x < y) ===> True
#testOptimize [ "DecideEqFalse_14"] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                      (decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y)) = ¬ (x < y) ===> True

-- ∀ (x y : Nat) (a b c : Bool),
-- (((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y) = (x ≤ y) ===> True
#testOptimize [ "DecideEqFalse_15"] ∀ (x y : Nat) (a b c : Bool),
                                      (((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y) = (x ≤ y) ===> True

-- ∀ (p q : Prop) (a b c : Bool),
-- [Decidable p] → [Decidable q] →
-- (((a || ((b || c) && !(c || b))) && !a) = ¬ (p ∧ q)) = (p ∧ q) ===> True
#testOptimize [ "DecideEqFalse_16"] ∀ (p q : Prop) (a b c : Bool), [Decidable p] → [Decidable q] →
                                      (((a || ((b || c) && !(c || b))) && !a) = ¬ (p ∧ q)) = (p ∧ q) ===> True


/-! Test cases for simplification rule `decide e1 = decide e2 ==> e1 = e2`. -/

-- ∀ (p q : Prop), [Decidable p] → [Decidable q] → decide p = decide q ===>
-- ∀ (p q : Prop), p = q
#testOptimize [ "DecideEqDecide_1"] ∀ (p q : Prop), [Decidable p] → [Decidable q] → decide p = decide q ===>
                                    ∀ (p q : Prop), p = q

-- ∀ (p : Prop), [Decidable p] → [Decidable q] → decide p = decide p ===> True
#testOptimize [ "DecideEqDecide_2"] ∀ (p : Prop), [Decidable p] →  decide p = decide p ===> True


-- ∀ (a b : Prop) (c d e : Bool) (x y z : Int), [Decidable a] → [Decidable b] →
--  (x < y && ((d || !e) || !(!e || d))) = ((a ∧ b) && (c || !c)) ===>
-- ∀ (a b : Prop) (x y : Int), (a ∧ b) = (x < y)
#testOptimize [ "DecideEqDecide_3"] ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
                                      (x < y && ((d || !e) || !(!e || d))) = ((a ∧ b) && (c || !c)) ===>
                                    ∀ (a b : Prop) (x y : Int), (a ∧ b) = (x < y)

-- ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
--  (x < y && (c || ((d || !e) && !(!e || d)))) = ((a ∧ b) && (c || !c)) ===>
-- ∀ (a b : Prop) (c : Bool) (x y : Int), (a ∧ b) = (true = c ∧ x < y)
#testOptimize [ "DecideEqDecide_4"] ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
                                      (x < y && (c || ((d || !e) && !(!e || d)))) = ((a ∧ b) && (c || !c)) ===>
                                    ∀ (a b : Prop) (c : Bool) (x y : Int), (a ∧ b) = (true = c ∧ x < y)

-- ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] → decide p = (decide q = decide r) ===>
-- ∀ (p q r : Prop), p = (q = r)
#testOptimize [ "DecideEqDecide_5"] ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
                                      decide p = (decide q = decide r) ===>
                                    ∀ (p q r : Prop), p = (q = r)

-- ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] → (decide p = decide q) = decide r ===>
-- ∀ (p q r : Prop), r = (p = q)
#testOptimize [ "DecideEqDecide_6"] ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
                                      (decide p = decide q) = decide r ===>
                                    ∀ (p q r : Prop), r = (p = q)

-- ∀ (p : Prop), [Decidable p] → (decide p = decide (¬ p)) ===> False
#testOptimize [ "DecideEqDecide_7"] ∀ (p : Prop), [Decidable p] → (decide p = decide (¬ p)) ===> False

-- ∀ (x y : Int) (a b : Bool), (x < y && (!a || a)) = ((b && !b) || ¬ (y > x)) ===> False
#testOptimize [ "DecideEqDecide_8"] ∀ (x y : Int) (a b : Bool),
                                      ((x < y) && (!a || a)) = ((b && !b) || ¬ (y > x)) ===> False

-- ∀ (p q : Prop), [Decidable p] → [Decidable q] → (decide (¬ p) = decide (¬ q)) ===>
-- ∀ (p q : Prop), p = q
#testOptimize [ "DecideEqDecide_9"] ∀ (p q : Prop), [Decidable p] → [Decidable q] →
                                       (decide (¬ p) = decide (¬ q)) ===>
                                    ∀ (p q : Prop), p = q

-- ∀ (x y z : Int) (a b : Bool), (¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z)) ===>
-- ∀ (x y z : Int), (x < y) = (z < y)
#testOptimize [ "DecideEqDecide_10" ] ∀ (x y z : Int) (a b : Bool),
                                        (¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z)) ===>
                                      ∀ (x y z : Int), (x < y) = (z < y)


-- ∀ (p q : Prop), [Decidable p] → [Decidable q] → (decide p = decide q) = (p = q) ===> True
#testOptimize [ "DecideEqDecide_11"] ∀ (p q : Prop), [Decidable p] → [Decidable q] →
                                       (decide p = decide q) = (p = q) ===> True

-- ∀ (a b : Prop) (c d e : Bool) (x y z : Int), [Decidable a] → [Decidable b] →
--  ((x < y && ((d || !e) || !(!e || d))) = ((a ∧ b) && (c || !c))) = ((a ∧ b) = (x < y)) ===> True
#testOptimize [ "DecideEqDecide_12"] ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
                                       ((x < y && ((d || !e) || !(!e || d))) = ((a ∧ b) && (c || !c))) =
                                       ((a ∧ b) = (x < y)) ===> True

-- ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
--  ((x < y && (c || ((d || !e) && !(!e || d)))) = ((a ∧ b) && (c || !c))) =
--  ((a ∧ b) = (true = c ∧ x < y)) ===> True
#testOptimize [ "DecideEqDecide_13"] ∀ (a b : Prop) (c d e : Bool) (x y : Int), [Decidable a] → [Decidable b] →
                                       ((x < y && (c || ((d || !e) && !(!e || d)))) = ((a ∧ b) && (c || !c))) =
                                       ((a ∧ b) = (true = c ∧ x < y)) ===> True

-- ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
--  (decide p = (decide q = decide r)) = (p = (q = r)) ===> True
#testOptimize [ "DecideEqDecide_14"] ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
                                       (decide p = (decide q = decide r)) = (p = (q = r)) ===> True

-- ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
-- ((decide p = decide q) = decide r) = (r = (p = q)) ===> True
#testOptimize [ "DecideEqDecide_15"] ∀ (p q r : Prop), [Decidable p] → [Decidable q] → [Decidable r] →
                                       ((decide p = decide q) = decide r) = (r = (p = q)) ===> True

-- ∀ (p q : Prop), [Decidable p] → [Decidable q] → (decide (¬ p) = decide (¬ q)) = (p = q) ===> True
#testOptimize [ "DecideEqDecide_16"] ∀ (p q : Prop), [Decidable p] → [Decidable q] →
                                       (decide (¬ p) = decide (¬ q)) = (p = q) ===> True

-- ∀ (x y z : Int) (a b : Bool),
-- ((¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z))) = ((x < y) = (z < y)) ===> True
#testOptimize [ "DecideEqDecide_17" ] ∀ (x y z : Int) (a b : Bool),
                                      ((¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z))) = ((x < y) = (z < y)) ===> True


/-! Test cases for simplification rule `decide e1 = e2 | e2 = decide e1 ===> e1 = (true = e2)`. -/

-- ∀ (p : Prop) (a : Bool), [Decidable p] → decide p = a ===>
-- ∀ (p : Prop) (a : Bool), p = (true = a)
#testOptimize [ "DecideEqBool_1" ] ∀ (p : Prop) (a : Bool), [Decidable p] → decide p = a ===>
                                   ∀ (p : Prop) (a : Bool), p = (true = a)

-- ∀ (p : Prop) (a : Bool), [Decidable p] → a = decide p ===>
-- ∀ (p : Prop) (a : Bool), p = (true = a)
#testOptimize [ "DecideEqBool_2" ] ∀ (p : Prop) (a : Bool), [Decidable p] → a = decide p ===>
                                   ∀ (p : Prop) (a : Bool), p = (true = a)

-- ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = c ===>
-- ∀ (x y : Int) (c : Bool), (true = c) = (x ≤ y)
#testOptimize [ "DecideEqBool_3" ] ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = c ===>
                                   ∀ (x y : Int) (c : Bool), (true = c) = (x ≤ y)


-- ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = (!c && (a || !a)) ===>
-- ∀ (x y : Int) (c : Bool), (false = c) = (x ≤ y)
#testOptimize [ "DecideEqBool_4" ] ∀ (x y : Int) (a b c : Bool),
                                     (x ≤ y || (a && (b && !b))) = (!c && (a || !a)) ===>
                                   ∀ (x y : Int) (c : Bool), (false = c) = (x ≤ y)

-- ∀ (x y : Int) (a b c : Bool), ((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (!c && (a || !a)) ===>
-- ∀ (c : Bool), true = c
#testOptimize [ "DecideEqBool_5" ] ∀ (x y : Int) (a b c : Bool),
                                    ((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (!c && (a || !a)) ===>
                                   ∀ (c : Bool), true = c

-- ∀ (x y : Int) (a b c : Bool), (!c ∨ (x ≤ y ∧ (b ∧ !b))) = (!c && (a || !a)) ===> True
#testOptimize [ "DecideEqBool_6" ] ∀ (x y : Int) (a b c : Bool),
                                     (!c ∨ (x ≤ y ∧ (b ∧ !b))) = (!c && (a || !a)) ===> True


-- ∀ (x y : Int) (a b c : Bool), ((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (c == b && (a || !a)) ===>
-- ∀ (c : Bool), ¬ b = c
#testOptimize [ "DecideEqBool_7" ] ∀ (x y : Int) (a b c : Bool),
                                    ((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (c == b && (a || !a)) ===>
                                   ∀ (b c : Bool), ¬ b = c

-- ∀ (x y : Int) (a b c : Bool), (b == c ∨ (x ≤ y ∧ (b ∧ !b))) = (c == b && (a || !a)) ===> True
#testOptimize [ "DecideEqBool_8" ] ∀ (x y : Int) (a b c : Bool),
                                     (b == c ∨ (x ≤ y ∧ (b ∧ !b))) = (c == b && (a || !a)) ===> True


-- ∀ (p : Prop) (a : Bool), [Decidable p] → (decide p = a) = (a = p) ===> True
#testOptimize [ "DecideEqBool_9" ] ∀ (p : Prop) (a : Bool), [Decidable p] →
                                     (decide p = a) = (a = p) ===> True

-- ∀ (x y : Int) (a b c : Bool),
--  ((x ≤ y || (a && (b && !b))) = c) = ((x ≤ y) = c) ===> True
#testOptimize [ "DecideEqBool_10" ] ∀ (x y : Int) (a b c : Bool),
                                      ((x ≤ y || (a && (b && !b))) = c) = ((x ≤ y) = c) ===> True


-- ∀ (x y : Int) (a b c : Bool),
--  ((x ≤ y || (a && (b && !b))) = (!c && (a || !a))) = ((x ≤ y) = !c) ===> True
#testOptimize [ "DecideEqBool_11" ] ∀ (x y : Int) (a b c : Bool),
                                    ((x ≤ y || (a && (b && !b))) = (!c && (a || !a))) =
                                    ((x ≤ y) = !c) ===> True

-- ∀ (x y : Int) (a b c : Bool),
--  (((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (!c && (a || !a))) = c ===> True
#testOptimize [ "DecideEqBool_12" ] ∀ (x y : Int) (a b c : Bool),
                                    (((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) =
                                    (!c && (a || !a))) = c ===> True

-- ∀ (x y : Int) (a b c : Bool),
--  (((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (c == b && (a || !a))) = (¬ b = c) ===> True
#testOptimize [ "DecideEqBool_13" ] ∀ (x y : Int) (a b c : Bool),
                                      (((!c ∧ (x ≤ y ∧ (b ∧ !b))) || (a && !a)) = (c == b && (a || !a))) =
                                      (¬ b = c) ===> True

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (a && b) && c ===>
-- ∀ (a b : Prop) (c : Bool), (a ∧ b) ∧ true = c
#testOptimize [ "DecideEqBool_14" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (a && b) && c ===>
                                    ∀ (a b : Prop) (c : Bool), (a ∧ b) ∧ true = c

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → ((a && b) && c) = ((a ∧ b) && c) ===> True
#testOptimize [ "DecideEqBool_15" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                      ((a && b) && c) = ((a ∧ b) && c) ===> True

-- ∀ (x y : Int) (b : Bool), (x < y) == b ==>
-- ∀ (x y : Int) (b : Bool), (true = b) = (x < y)
#testOptimize [ "DecideEqBool_16" ] ∀ (x y : Int) (b : Bool), (x < y) == b ===>
                                    ∀ (x y : Int) (b : Bool), (true = b) = (x < y)

-- ∀ (x y : Int) (b : Bool), ((x < y) == b) = ((x < y) = b) ===> True
#testOptimize [ "DecideEqBool_17" ] ∀ (x y : Int) (b : Bool), ((x < y) == b) = ((x < y) = b) ===> True


-- ∀ (x y z : Int) (b c : Bool), (if ((x < y) && c) == b then x else y) < z ===>
-- ∀ (x y z : Int) (b c : Bool), (if (true = c ∧ (x < y)) = (true = b) then x else y) < z
#testOptimize [ "DecideEqBool_18" ] ∀ (x y z : Int) (b c : Bool), (if ((x < y) && c) == b then x else y) < z ===>
                                    ∀ (x y z : Int) (b c : Bool), (if (true = c ∧ (x < y)) = (true = b) then x else y) < z

-- ∀ (x y : Int) (b c : Bool),
--  (if ((x < y) ∧ c) = b then x else y) = (if ((x < y) && c) == b then x else y) ===> True
#testOptimize [ "DecideEqBool_19" ] ∀ (x y : Int) (b c : Bool),
                                      (if ((x < y) ∧ c) = b then x else y) =
                                      (if ((x < y) && c) == b then x else y) ===> True

-- ∀ (x y : Int) (b c : Bool), ((x < y && c) = b) ===>
-- ∀ (x y : Int) (b c : Bool), ((true = c) ∧ x < y) = (true = b)
#testOptimize [ "DecideEqBool_20"] ∀ (x y : Int) (b c : Bool), (x < y && c) = b ===>
                                   ∀ (x y : Int) (b c : Bool), ((true = c) ∧ x < y) = (true = b)

-- ∀ (x y : Int) (b c : Bool), ((x < y && c) = b) = (b = (c ∧ x < y)) ===> True
#testOptimize [ "DecideEqBool_21"] ∀ (x y : Int) (b c : Bool), ((x < y && c) = b) = (b = (c ∧ x < y)) ===> True


end Test.DecideEq
