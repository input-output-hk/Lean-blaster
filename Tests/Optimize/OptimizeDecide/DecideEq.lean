import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.DecideEq

/-! ## Test objectives to validate `Decidable.decide` simplification rules on `Eq`. -/


/-! Test cases for simplification rule `true = (a == b) ==> a = b (if hasLawFulBEqInstance Type(a))`. -/

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


/-! Test cases to ensure that simplification rule `true = (a == b) ==> (a = b) (if hasLawFulBEqInstance Type(a))`
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


/-! Test cases for simplification rule `false = (a == b) ==> ¬ (a = b) (if hasLawFulBEqInstance Type(a))`. -/

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


/-! Test cases to ensure that simplification rule `false = (a == b) ==> ¬ (a = b) (if hasLawFulBEqInstance Type(a))`
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
    `c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if hasLawFulBEqInstance Type(a))`
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
    `c = (a == b) | (a == b) = c ==> (true = c) = (a = b) (if hasLawFulBEqInstance Type(a))` is not applied wrongly.
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


/-! Test cases for simplification rule
     `true = if c then e1 else e2 ==> (c → true = e1) ∧ (¬ c → true = e2)`.
-/

-- ∀ (c a b : Bool), (if c then a else b) = true ===>
-- ∀ (c a b : Bool), (false = c → true = b) ∧ (true = c → true = a)
#testOptimize [ "TrueEqIte_1" ] ∀ (c a b : Bool), (if c then a else b) = true ===>
                                ∀ (c a b : Bool), (false = c → true = b) ∧ (true = c → true = a)

-- ∀ (a b : Bool), (if a then true else b) = true ===>
-- ∀ (a b : Bool), false = a → true = b
#testOptimize [ "TrueEqIte_2" ] ∀ (a b : Bool), (if a then true else b) = true ===>
                                ∀ (a b : Bool), false = a → true = b

-- ∀ (a b : Bool), (if a then b else true) = true ===>
-- ∀ (a b : Bool), true = a → true = b
#testOptimize [ "TrueEqIte_3" ] ∀ (a b : Bool), (if a then b else true) = true ===>
                                ∀ (a b : Bool), true = a → true = b

-- ∀ (a b : Bool), (if a then false else b) = true ===>
-- ∀ (a b : Bool), true = (b && !a)
#testOptimize [ "TrueEqIte_4" ] ∀ (a b : Bool), (if a then false else b) = true ===>
                                ∀ (a b : Bool), true = (b && !a)

-- ∀ (a b : Bool), (if a then b else false) = true ===>
-- ∀ (a b : Bool), true = (a && b)
#testOptimize [ "TrueEqIte_5" ] ∀ (a b : Bool), (if a then b else false) = true ===>
                                ∀ (a b : Bool), true = (a && b)

-- ∀ (a b : Bool), (if a then a else b) = true ===>
-- ∀ (a b : Bool), false = a → true = b
#testOptimize [ "TrueEqIte_6" ] ∀ (a b : Bool), true = (if a then a else b) ===>
                                ∀ (a b : Bool), false = a → true = b

-- ∀ (a b : Bool), (if a then b else a) = true ===>
-- ∀ (a b : Bool), true = (a && b)
#testOptimize [ "TrueEqIte_7" ] ∀ (a b : Bool), (if a then b else a) = true ===>
                                ∀ (a b : Bool), true = (a && b)

-- ∀ (c a b : Bool), (if !c then a else b) = true ===>
-- ∀ (c a b : Bool), (false = c → true = a) ∧ (true = c → true = b)
#testOptimize [ "TrueEqIte_8" ] ∀ (c a b : Bool), (if !c then a else b) = true ===>
                                ∀ (c a b : Bool), (false = c → true = a) ∧ (true = c → true = b)

-- ∀ (c a b : Bool), (if c then a else b) = true → (false = c → true = b) ∧ (true = c → true = a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_9" ]
  ∀ (c a b : Bool), ((if c then a else b) = true) → (false = c → true = b) ∧ (true = c → true = a) ===> True

-- ∀ (a b : Bool), (if a then true else b) = true → false = a → true = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_10" ]
  ∀ (a b : Bool), (if a then true else b) = true → false = a → true = b ===> True

-- ∀ (a b : Bool), (if a then b else true) = true → true = a → true = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_11" ]
  ∀ (a b : Bool), (if a then b else true) = true → true = a → true = b ===> True


-- ∀ (a b : Bool), (if a then false else b) = true → false = a ∧ (false = a → true = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_12" ]
  ∀ (a b : Bool), (if a then false else b) = true → false = a ∧ (false = a → true = b) ===> True

-- ∀ (a b : Bool), (if a then b else false) = true → true = a ∧ (true = a → true = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_13" ]
  ∀ (a b : Bool), (if a then b else false) = true → true = a ∧ (true = a → true = b) ===> True

-- ∀ (a b : Bool), (if a then a else b) = true → false = a → true = b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_14" ]
  ∀ (a b : Bool), (if a then a else b) = true → false = a → true = b ===> True

-- ∀ (a b : Bool), (if a then b else a) = true → true = a ∧ (true = a → true = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_15" ]
  ∀ (a b : Bool), (if a then b else a) = true → true = a ∧ (true = a → true = b) ===> True

-- ∀ (c a b : Bool), (if !c then a else b) = true → (false = c → true = a) ∧ (true = c → true = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqIte_16" ]
 ∀ (c a b : Bool), (if !c then a else b) = true → (false = c → true = a) ∧ (true = c → true = b) ===> True


-- ∀ (a b c d : Bool), (if c = d then a else b) = true ===>
-- ∀ (a b c d : Bool), (¬ (c = d) → true = b) ∧ (c = d → true = a)
#testOptimize [ "TrueEqIte_17" ] ∀ (a b c d : Bool), (if c = d then a else b) = true ===>
                                 ∀ (a b c d : Bool), (¬ (c = d) → true = b) ∧ (c = d → true = a)

-- ∀ (c : Prop) (a b : Bool), (if c then a else b) = true ===>
-- ∀ (c : Prop) (a b : Bool), (c → true = a) ∧ (¬ c → true = b)
#testOptimize [ "TrueEqIte_18" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = true ===>
  ∀ (c : Prop) (a b : Bool), (c → true = a) ∧ (¬ c → true = b)

-- ∀ (a b c : Bool), (if a = c then true else b) = true ===>
-- ∀ (a b c : Bool), (¬ (a = c) → true = b)
#testOptimize [ "TrueEqIte_19" ] ∀ (a b c : Bool), (if a = c then true else b) = true ===>
                                 ∀ (a b c : Bool), (¬ (a = c) → true = b)

-- ∀ (a b c : Bool), (if a = c then b else true) = true ===>
-- ∀ (a b c : Bool),  a = c → true = b
#testOptimize [ "TrueEqIte_20" ] ∀ (a b c : Bool), (if a = c then b else true) = true ===>
                                 ∀ (a b c : Bool),  a = c → true = b

-- ∀ (a b c : Bool), (if a = c then false else b) = true ===>
-- ∀ (a b c : Bool), ¬ a = c ∧ true = b
#testOptimize [ "TrueEqIte_21" ] ∀ (a b c : Bool), (if a = c then false else b) = true ===>
                                 ∀ (a b c : Bool), ¬ a = c ∧ true = b

-- ∀ (a b c : Bool), (if a = c then b else false) = true ===>
-- ∀ (a b c : Bool), a = c ∧ true = b
#testOptimize [ "TrueEqIte_22" ] ∀ (a b c : Bool), (if a = c then b else false) = true ===>
                                 ∀ (a b c : Bool), a = c ∧ true = b

-- ∀ (x y : Int) (a b : Bool), (if x < y then a else b) = true ===>
-- ∀ (x y : Int) (a b : Bool), (¬ x < y → true = b) ∧ (x < y → true = a)
#testOptimize [ "TrueEqIte_23" ]
  ∀ (x y : Int) (a b : Bool), (if x < y then a else b) = true ===>
  ∀ (x y : Int) (a b : Bool), (¬ x < y → true = b) ∧ (x < y → true = a)


-- ∀ (x y : Int) (a b c d : Bool), (if x < y then if c then a else b else d) = true ===>
-- ∀ (x y : Int) (a b c d : Bool),
--  (¬ x < y → true = d) ∧ (x < y → (false = c → true = b) ∧ (true = c → true = a))
#testOptimize [ "TrueEqIte_24" ]
  ∀ (x y : Int) (a b c d : Bool), (if x < y then if c then a else b else d) = true ===>
  ∀ (x y : Int) (a b c d : Bool),
   (¬ x < y → true = d) ∧ (x < y → (false = c → true = b) ∧ (true = c → true = a))


-- ∀ (x y : Int) (a b c d : Bool), (if x < y then d else if c then a else b) = true ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → (false = c → true = b) ∧ (true = c → true = a)) ∧ (x < y → true = d)
#testOptimize [ "TrueEqIte_25" ]
  ∀ (x y : Int) (a b c d : Bool), (if x < y then d else if c then a else b) = true ===>
  ∀ (x y : Int) (a b c d : Bool),
    (¬ x < y → (false = c → true = b) ∧ (true = c → true = a)) ∧ (x < y → true = d)


-- ∀ (x y z : Int) (a b c d : Bool),
--  (if x < y then (if x < z then (if c then a else b) else d) else a) = true ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → true = a) ∧
--   (x < y → (¬ x < z → true = d) ∧ (x < z → (false = c → true = b) ∧ (true = c → true = a)))
#testOptimize [ "TrueEqIte_26" ]
  ∀ (x y z : Int) (a b c d : Bool),
  (if x < y then (if x < z then (if c then a else b) else d) else a) = true ===>
  ∀ (x y z : Int) (a b c d : Bool),
     (¬ x < y → true = a) ∧
     (x < y → (¬ x < z → true = d) ∧ (x < z → (false = c → true = b) ∧ (true = c → true = a)))

-- ∀ (x y z : Int) (a b c d : Bool),
--   (if x < y then a else (if x < z then (if c then a else b) else d)) = true ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → (¬ x < z → true = d) ∧ (x < z → (false = c → true = b) ∧ (true = c → true = a))) ∧
--   (x < y → true = a)
#testOptimize [ "TrueEqIte_27" ]
  ∀ (x y z : Int) (a b c d : Bool),
     (if x < y then a else (if x < z then (if c then a else b) else d)) = true ===>
  ∀ (x y z : Int) (a b c d : Bool),
     (¬ x < y → (¬ x < z → true = d) ∧ (x < z → (false = c → true = b) ∧ (true = c → true = a))) ∧
     (x < y → true = a)

-- ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = ((!c || a) && (c || b)) ===>
-- ∀ (c : Prop) (a b : Bool),
--   ((c ∨ true = b) ∧ (¬ c ∨ true  = a)) = ((c → true = a) ∧ (¬ c → true = b))
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_28" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = ((!c || a) && (c || b)) ===>
  ∀ (c : Prop) (a b : Bool),
    ((c ∨ true = b) ∧ (¬ c ∨ true = a)) = ((c → true = a) ∧ (¬ c → true = b))

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then true else b) = (b || a) ===>
-- ∀ (a : Prop) (b : Bool), (a ∨ true = b) = (¬ a → true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_29" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then true else b) = (b || a) ===>
  ∀ (a : Prop) (b : Bool), (a ∨ true = b) = (¬ a → true = b)

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else true) = (!a || b) ===>
-- ∀ (a : Prop) (b : Bool), (¬ a ∨ true = b) = (a → true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_30" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else true) = (!a || b) ===>
  ∀ (a : Prop) (b : Bool), (¬ a ∨ true = b) = (a → true = b)

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then false else b) = (!a && (a || b)) ===>
-- ∀ (a : Prop) (b : Bool), (¬ a ∧ (a ∨ true = b)) = (¬ a ∧ true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_31" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then false else b) = (!a && (a || b)) ===>
  ∀ (a : Prop) (b : Bool), (¬ a ∧ (a ∨ true = b)) = (¬ a ∧ true = b)

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else false) = ((!a || b) && a) ===>
-- ∀ (a : Prop) (b : Bool), (a ∧ (¬ a ∨ true = b)) = (a ∧ true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_32" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else false) = ((!a || b) && a) ===>
  ∀ (a : Prop) (b : Bool), (a ∧ (¬ a ∨ true = b)) = (a ∧ true = b)

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then a else b) = (a || b) ===>
-- ∀ (a : Prop) (b : Bool), (a ∨ true = b) = (¬ a → true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_33" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then a else b) = (a || b) ===>
  ∀ (a : Prop) (b : Bool), (a ∨ true = b) = (¬ a → true = b)

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else a) = ((!a || b) && a) ===>
-- ∀ (a : Prop) (b : Bool), (a ∧ (¬ a ∨ true = b)) = (a ∧ true = b)
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_34" ]
  ∀ (a : Prop) (b : Bool), [Decidable a] → (if a then b else a) = ((!a || b) && a) ===>
  ∀ (a : Prop) (b : Bool), (a ∧ (¬ a ∨ true = b)) = (a ∧ true = b)

-- ∀ (c : Prop) (a b : Bool), [Decidable c] → (if !c then a else b) = ((c || a) && (!c || b)) ===>
-- ∀ (c : Prop) (a b : Bool),
--   ((c ∨ true = a) ∧ (¬ c ∨ true = b)) = ((c → true = b) ∧ (¬ c → true = a))
-- NOTE: can be simplified to True with additional simplification rules
#testOptimize [ "TrueEqIte_35" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if !c then a else b) = ((c || a) && (!c || b)) ===>
  ∀ (c : Prop) (a b : Bool),
    ((c ∨ true = a) ∧ (¬ c ∨ true = b)) = ((c → true = b) ∧ (¬ c → true = a))

/-! Test cases for simplification rule
     `false = if c then e1 else e2 ==> (c → false = e1) ∧ (¬ c → false = e2)`.
-/

-- ∀ (c a b : Bool), (if c then a else b) = false ===>
-- ∀ (c a b : Bool), (false = c → false = b) ∧ (true = c → false = a)
#testOptimize [ "FalseEqIte_1" ] ∀ (c a b : Bool), (if c then a else b) = false ===>
                                 ∀ (c a b : Bool), (false = c → false = b) ∧ (true = c → false = a)

-- ∀ (a b : Bool), (if a then true else b) = false ===>
-- ∀ (a b : Bool), false = (a || b)
#testOptimize [ "FalseEqIte_2" ] ∀ (a b : Bool), (if a then true else b) = false ===>
                                 ∀ (a b : Bool), false = (a || b)

-- ∀ (a b : Bool), (if a then b else true) = false ===>
-- ∀ (a b : Bool), true = (a && !b
#testOptimize [ "FalseEqIte_3" ] ∀ (a b : Bool), (if a then b else true) = false ===>
                                 ∀ (a b : Bool), true = (a && !b)

-- ∀ (a b : Bool), (if a then false else b) = false ===>
-- ∀ (a b : Bool), false = a → false = b
#testOptimize [ "FalseEqIte_4" ] ∀ (a b : Bool), (if a then false else b) = false ===>
                                 ∀ (a b : Bool), false = a → false = b

-- ∀ (a b : Bool), (if a then b else false) = false ===>
-- ∀ (a b : Bool), true = a → false = b
#testOptimize [ "FalseEqIte_5" ] ∀ (a b : Bool), (if a then b else false) = false ===>
                                 ∀ (a b : Bool), true = a → false = b

-- ∀ (a b : Bool), false = (if a then a else b) ===>
-- ∀ (a b : Bool), false = (a || b)
#testOptimize [ "FalseEqIte_6" ] ∀ (a b : Bool), false = (if a then a else b) ===>
                                 ∀ (a b : Bool), false = (a || b)

-- ∀ (a b : Bool), (if a then b else a) = false ===>
-- ∀ (a b : Bool), true = a → false = b
#testOptimize [ "FalseEqIte_7" ] ∀ (a b : Bool), (if a then b else a) = false ===>
                                 ∀ (a b : Bool), true = a → false = b

-- ∀ (c a b : Bool), (if !c then a else b) = false ===>
-- ∀ (c a b : Bool), (false = c → false = a) ∧ (true = c → false = b)
#testOptimize [ "FalseEqIte_8" ] ∀ (c a b : Bool), (if !c then a else b) = false ===>
                                 ∀ (c a b : Bool), (false = c → false = a) ∧ (true = c → false = b)

-- ∀ (c a b : Bool), (if c then a else b) = false →
--  (false = c → false = b) ∧ (true = c → false = a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqIte_9" ]
  ∀ (c a b : Bool), ((if c then a else b) = false) →
    (false = c → false = b) ∧ (true = c → false = a) ===> True

-- ∀ (a b : Bool), (if a then true else b) = false → false = a ∧ (false = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
-- NOTE: can be simplified to
-- ∀ (a b : Bool), (if a then true else b) = false → false = a ∧ false = b ===> True
#testOptimize [ "FalseEqIte_10" ]
  ∀ (a b : Bool), (if a then true else b) = false → false = a ∧ (false = a → false = b) ===> True

-- ∀ (a b : Bool), (if a then b else true) = false → true = a ∧ (true = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
-- NOTE can be simplified to
--  ∀ (a b : Bool), (if a then b else true) = false → true = a ∧ false = b ===> True
#testOptimize [ "FalseEqIte_11" ]
  ∀ (a b : Bool), (if a then b else true) = false → true = a ∧ (true = a → false = b) ===> True

-- ∀ (a b : Bool), (if a then false else b) = false → (false = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqIte_12" ]
  ∀ (a b : Bool), (if a then false else b) = false → (false = a → false = b) ===> True

-- ∀ (a b : Bool), (if a then b else false) = false → (true = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqIte_13" ]
  ∀ (a b : Bool), (if a then b else false) = false → (true = a → false = b) ===> True

-- ∀ (a b : Bool), (if a then a else b) = false → false = a ∧ (false = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
-- NOTE: can be simplified to
--  ∀ (a b : Bool), (if a then a else b) = false → false = a ∧ false = b
#testOptimize [ "FalseEqIte_14" ]
  ∀ (a b : Bool), (if a then a else b) = false → false = a ∧ (false = a → false = b) ===> True

-- ∀ (a b : Bool), (if a then b else a) = false → (true = a → false = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqIte_15" ]
  ∀ (a b : Bool), (if a then b else a) = false → (true = a → false = b) ===> True

-- ∀ (c a b : Bool), (if !c then a else b) = false → (false = c → false = a) ∧ (true = c → false = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqIte_16" ]
 ∀ (c a b : Bool), (if !c then a else b) = false →
   (false = c → false = a) ∧ (true = c → false = b) ===> True


-- ∀ (a b c d : Bool), (if c = d then a else b) = false ===>
-- ∀ (a b c d : Bool), (¬ (c = d) → false = b) ∧ (c = d → false = a)
#testOptimize [ "FalseEqIte_17" ] ∀ (a b c d : Bool), (if c = d then a else b) = false ===>
                                  ∀ (a b c d : Bool), (¬ (c = d) → false = b) ∧ (c = d → false = a)

-- ∀ (c : Prop) (a b : Bool), (if c then a else b) = false ===>
-- ∀ (c : Prop) (a b : Bool), (c → false = a) ∧ (¬ c → false = b)
#testOptimize [ "FalseEqIte_18" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = false ===>
  ∀ (c : Prop) (a b : Bool), (c → false = a) ∧ (¬ c → false = b)

-- ∀ (a b c : Bool), (if a = c then true else b) = false ===>
-- ∀ (a b c : Bool), ¬ (a = c) ∧ false = b
#testOptimize [ "FalseEqIte_19" ] ∀ (a b c : Bool), (if a = c then true else b) = false ===>
                                  ∀ (a b c : Bool), ¬ (a = c) ∧ false = b

-- ∀ (a b c : Bool), (if a = c then b else true) = false ===>
-- ∀ (a b c : Bool), a = c ∧ false = b
#testOptimize [ "FalseEqIte_20" ] ∀ (a b c : Bool), (if a = c then b else true) = false ===>
                                  ∀ (a b c : Bool), a = c ∧ false = b

-- ∀ (a b c : Bool), (if a = c then false else b) = false ===>
-- ∀ (a b c : Bool), ¬ a = c → false = b
#testOptimize [ "FalseEqIte_21" ] ∀ (a b c : Bool), (if a = c then false else b) = false ===>
                                  ∀ (a b c : Bool), ¬ a = c → false = b

-- ∀ (a b c : Bool), (if a = c then b else false) = false ===>
-- ∀ (a b c : Bool), a = c → false = b
#testOptimize [ "FalseEqIte_22" ] ∀ (a b c : Bool), (if a = c then b else false) = false ===>
                                  ∀ (a b c : Bool), a = c → false = b

-- ∀ (x y : Int) (a b : Bool), (if x < y then a else b) = false ===>
-- ∀ (x y : Int) (a b: Bool), (¬ x < y → false = b) ∧ (x < y → false = a)
#testOptimize [ "FalseEqIte_23" ]
  ∀ (x y : Int) (a b : Bool), (if x < y then a else b) = false ===>
  ∀ (x y : Int) (a b: Bool), (¬ x < y → false = b) ∧ (x < y → false = a)


-- ∀ (x y : Int) (a b c d : Bool), (if x < y then if c then a else b else d) = false ===>
-- ∀ (x y : Int) (a b c d : Bool),
--  (¬ x < y → false = d) ∧ (x < y → (false = c → false = b) ∧ (true = c → false = a))
#testOptimize [ "FalseEqIte_24" ]
  ∀ (x y : Int) (a b c d : Bool), (if x < y then if c then a else b else d) = false ===>
  ∀ (x y : Int) (a b c d : Bool),
    (¬ x < y → false = d) ∧ (x < y → (false = c → false = b) ∧ (true = c → false = a))


-- ∀ (x y : Int) (a b c d : Bool), (if x < y then d else if c then a else b) = false ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → (false = c → false = b) ∧ (true = c → false = a)) ∧ (x < y → false = d)
#testOptimize [ "FalseEqIte_25" ]
  ∀ (x y : Int) (a b c d : Bool), (if x < y then d else if c then a else b) = false ===>
  ∀ (x y : Int) (a b c d : Bool),
    (¬ x < y → (false = c → false = b) ∧ (true = c → false = a)) ∧ (x < y → false = d)


-- ∀ (x y z : Int) (a b c d : Bool),
--  (if x < y then (if x < z then (if c then a else b) else d) else a) = false ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → false = a) ∧
--   (x < y → (¬ x < z → false = d) ∧ (x < z → (false = c → false = b) ∧ (true = c → false = a)))
#testOptimize [ "FalseEqIte_26" ]
  ∀ (x y z : Int) (a b c d : Bool),
  (if x < y then (if x < z then (if c then a else b) else d) else a) = false ===>
  ∀ (x y z : Int) (a b c d : Bool),
     (¬ x < y → false = a) ∧
     (x < y → (¬ x < z → false = d) ∧ (x < z → (false = c → false = b) ∧ (true = c → false = a)))

-- ∀ (x y z : Int) (a b c d : Bool),
--   (if x < y then a else (if x < z then (if c then a else b) else d)) = false ===>
-- ∀ (x y : Int) (a b c d : Bool),
--   (¬ x < y → (¬ x < z → false = d) ∧ (x < z → (false = c → false = b) ∧ (true = c → false = a))) ∧
--   (x < y → false = a)
#testOptimize [ "FalseEqIte_27" ]
  ∀ (x y z : Int) (a b c d : Bool),
     (if x < y then a else (if x < z then (if c then a else b) else d)) = false ===>
  ∀ (x y z : Int) (a b c d : Bool),
     (¬ x < y → (¬ x < z → false = d) ∧ (x < z → (false = c → false = b) ∧ (true = c → false = a))) ∧
     (x < y → false = a)


/-! Test cases to ensure that simplification rules
     - `true = if c then e1 else e2 ==> (c → true = e1) ∧ (¬ c → true = e2)`
     - `false = if c then e1 else e2 ==> (c → false = e1) ∧ (¬ c → false = e2)`
    are not wrongly applied.
-/

-- ∀ (c : Prop) (a b d : Bool), [Decidable c] → d = if c then a else b ===>
-- ∀ (c : Prop) (a b d : Bool), d = Blaster.dite' c (fun _ => a) (fun _ => b)
#testOptimize [ "BoolEqIteUnchanged_1" ]
  ∀ (c : Prop) (a b d : Bool), [Decidable c] → d = if c then a else b ===>
  ∀ (c : Prop) (a b d : Bool), d = Blaster.dite' c (fun _ => a) (fun _ => b)

-- ∀ (c : Prop) (a b d : Bool), [Decidable c] → (if c then a else b) = d ===>
-- ∀ (c : Prop) (a b d : Bool), d = Blaster.dite' c (fun _ => a) (fun _ => b)
#testOptimize [ "BoolEqIteUnchanged_2" ]
  ∀ (c : Prop) (a b d : Bool), [Decidable c] → (if c then a else b) = d ===>
  ∀ (c : Prop) (a b d : Bool), d = Blaster.dite' c (fun _ => a) (fun _ => b)

-- ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = (a && b) ===>
-- ∀ (c : Prop) (a b : Bool),
--   (a && b) = Blaster.dite' c (fun _ => a) (fun _ => b)
#testOptimize [ "BoolEqIteUnchanged_3" ]
  ∀ (c : Prop) (a b : Bool), [Decidable c] → (if c then a else b) = (a && b) ===>
  ∀ (c : Prop) (a b : Bool),
    (a && b) = Blaster.dite' c (fun _ => a) (fun _ => b)

-- ∀ (a : Prop) (b c : Bool), [Decidable a] → (if a then true else b) = (b || c) ===>
-- ∀ (a : Prop) (b c : Bool), (b || c) = Blaster.dite' a (fun _ => true) (fun _ => b)
#testOptimize [ "BoolEqIteUnchanged_4" ]
  ∀ (a : Prop) (b c : Bool), [Decidable a] → (if a then true else b) = (b || c) ===>
  ∀ (a : Prop) (b c : Bool), (b || c) = Blaster.dite' a (fun _ => true) (fun _ => b)

/-! Test cases for simplification rule
     `true = dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> (c → true = e1) ∧ (¬ c → true = e2)`.
-/

-- ∀ (c a b : Bool) (t : c → Bool → Bool) (f : ¬ c → Bool → Bool),
--   (if h : c then t h a else f h b) = true ===>
-- ∀ (c a b : Bool) (t : true = c → Bool → Bool) (f : false = c → Bool → Bool),
--   (∀ h : false = c, true = f h b) ∧ (∀ h : true = c, true = t h a)
#testOptimize [ "TrueEqDite_1" ]
  ∀ (c a b : Bool) (t : c → Bool → Bool) (f : ¬ c → Bool → Bool),
    (if h : c then t h a else f h b) = true ===>
  ∀ (c a b : Bool) (t : true = c → Bool → Bool) (f : false = c → Bool → Bool),
    (∀ h : false = c, true = f h b) ∧ (∀ h : true = c, true = t h a)

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool), (if h : a then true else f h b) = true ===>
-- ∀ (a b : Bool) (f : false = a → Bool → Bool) (h : false = a), true = f h b
#testOptimize [ "TrueEqDite_2" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool), (if h : a then true else f h b) = true ===>
  ∀ (a b : Bool) (f : false = a → Bool → Bool) (h : false = a), true = f h b

-- ∀ (a b : Bool) (t : a → Bool → Bool), (if h : a then t h b else true) = true ===>
-- ∀ (a b : Bool) (t : true = a → Bool → Bool) (h : true = a), true = t h b
#testOptimize [ "TrueEqDite_3" ]
  ∀ (a b : Bool) (t : a → Bool → Bool), (if h : a then t h b else true) = true ===>
  ∀ (a b : Bool) (t : true = a → Bool → Bool) (h : true = a), true = t h b

-- ∀ (a b : Bool) (t : ¬ a → Bool → Bool),
--   (if h : a then false else t h b) = true ===>
-- ∀ (a b : Bool) (t : false = a → Bool → Bool), false = a ∧ (∀ (h : false = a), true = t h b)
#testOptimize [ "TrueEqDite_4" ]
  ∀ (a b : Bool) (t : ¬ a → Bool → Bool),
    (if h : a then false else t h b) = true ===>
  ∀ (a b : Bool) (t : false = a → Bool → Bool), false = a ∧ (∀ (h : false = a), true = t h b)

-- ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else false) = true ===>
-- ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), true = f h b)
#testOptimize [ "TrueEqDite_5" ]
  ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else false) = true ===>
  ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), true = f h b)

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool), true = (if h : a then a else f h b) ===>
-- ∀ (a b : Bool) (f : false = a → Bool → Bool) (h : false = a), true = f h b
#testOptimize [ "TrueEqDite_6" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool), true = (if h : a then a else f h b) ===>
  ∀ (a b : Bool) (f : false = a → Bool → Bool) (h : false = a), true = f h b

-- ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else a) = true ===>
-- ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), true = f h b)
#testOptimize [ "TrueEqDite_7" ]
  ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else a) = true ===>
  ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), true = f h b)

-- ∀ (c a b : Bool) (f : !c → Bool → Bool), (if h : !c then f h a else b) = true ===>
-- ∀ (c a b : Bool) (f : false = c → Bool → Bool),
--   (∀ (h : false = c), true = f h a) ∧ (true = c → true = b)
#testOptimize [ "TrueEqDite_8" ]
  ∀ (c a b : Bool) (f : !c → Bool → Bool), (if h : !c then f h a else b) = true ===>
  ∀ (c a b : Bool) (f : false = c → Bool → Bool),
    (∀ (h : false = c), true = f h a) ∧ (true = c → true = b)

-- ∀ (c a b : Bool) (f : c → Bool → Bool),
-- ((if h : c then f h a else b) = true) → (false = c → true = b) ∧ (forall (h : c), f h a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_9" ]
  ∀ (c a b : Bool) (f : c → Bool → Bool),
  ((if h : c then f h a else b) = true) → (false = c → true = b) ∧ (forall (h : c), f h a) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then true else f h b) = true → (∀ h : ¬ a, f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_10" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then true else f h b) = true → (∀ h : ¬ a, f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else true) → (∀ (h : a), f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_11" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else true) → (∀ (h : a), f h b) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then false else f h b) → false = a ∧ (∀ (h : ¬ a), f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_12" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then false else f h b) → false = a ∧ (∀ (h : ¬ a), f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else false) → true = a ∧ (∀ (h : a), f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_13" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else false) → true = a ∧ (∀ (h : a), f h b) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then a else f h b) → (∀ (h : ¬ a), f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_14" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then a else f h b) → (∀ (h : ¬ a), f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else a) → true = a ∧ (∀ (h : a), f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_15" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else a) → true = a ∧ (∀ (h : a), f h b) ===> True

-- ∀ (c a b : Bool) (f : !c → Bool → Bool),
--   (if h : !c then f h a else b) → (∀ (h : !c), f h a) ∧ (true = c → true = b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "TrueEqDite_16" ]
 ∀ (c a b : Bool) (f : !c → Bool → Bool),
   (if h : !c then f h a else b) → (∀ (h : !c), f h a) ∧ (true = c → true = b) ===> True

-- ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
--   (if h : c = d then f h a else b) = true ===>
-- ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
--   (¬ (c = d) → true = b) ∧ (∀ (h : c = d), true = f h a)
#testOptimize [ "TrueEqDite_17" ]
  ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
    (if h : c = d then f h a else b) = true ===>
  ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
    (¬ (c = d) → true = b) ∧ (∀ (h : c = d), true = f h a)

-- ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
--   (if h : c then a else f h b) = true ===>
-- ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool),
--   (c → true = a) ∧ (∀ (h : ¬ c), true = f h b)
#testOptimize [ "TrueEqDite_18" ]
  ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool), [Decidable c] →
    (if h : c then a else f h b) = true ===>
  ∀ (c : Prop) (a b : Bool) (f : ¬ c → Bool → Bool),
    (c → true = a) ∧ (∀ (h : ¬ c), true = f h b)

-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--    (if h : a = c then true else f h b) = true ===>
-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   (∀ (h : ¬ a = c), true = f h b)
#testOptimize [ "TrueEqDite_19" ]
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
     (if h : a = c then true else f h b) = true ===>
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    (∀ (h : ¬ a = c), true = f h b)

-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   (if h : a = c then f h b else true) = true ===>
-- ∀ (a b c : Bool) (f : a = c → Bool → Bool), ∀ (h : a = c), true = f h
#testOptimize [ "TrueEqDite_20" ]
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    (if h : a = c then f h b else true) = true ===>
  ∀ (a b c : Bool) (f : a = c → Bool → Bool), ∀ (h : a = c), true = f h b

-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   (if h : a = c then false else f h b) = true ===>
-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--     ¬ (a = c) ∧ (∀ (h : ¬ a = c), true = f h b)
#testOptimize [ "TrueEqDite_21" ]
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    (if h : a = c then false else f h b) = true ===>
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
      ¬ (a = c) ∧ (∀ (h : ¬ a = c), true = f h b)

-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   (if h : a = c then f h b else false) = true ===>
-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   a = c ∧ (∀ (h : a = c), true = f h b)
#testOptimize [ "TrueEqDite_22" ]
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    (if h : a = c then f h b else false) = true ===>
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    a = c ∧ (∀ (h : a = c), true = f h b)

-- ∀ (x y : Int) (a b : Bool) (f : x < y → Bool → Bool),
--   (if h : x < y then f h a else b) = true ===>
-- ∀ (x y : Int) (a b: Bool) (f : x < y → Bool → Bool),
--   (¬ x < y → true = b) ∧ (∀ (h : x < y), true = f h a)
#testOptimize [ "TrueEqDite_23" ]
  ∀ (x y : Int) (a b : Bool) (f : x < y → Bool → Bool),
    (if h : x < y then f h a else b) = true ===>
  ∀ (x y : Int) (a b: Bool) (f : x < y → Bool → Bool),
    (¬ x < y → true = b) ∧ (∀ (h : x < y), true = f h a)


-- ∀ (x y : Int) (a b c d : Bool) (f : ¬ x < y → Bool → Bool) (g : c → Bool → Bool),
--   (if h1 : x < y then if h2 : c then g h2 a else b else f h1 d) = true ===>
-- ∀ (x y : Int) (a b c d : Bool) (f : ¬ x < y → Bool → Bool) (g : true = c → Bool → Bool),
--   (∀ (h1 : ¬ x < y), true = f h1 d) ∧ (x < y → (false = c → true = b) ∧
--   (∀ (h2 : true = c), true = g h2 a))
#testOptimize [ "TrueEqDite_24" ]
  ∀ (x y : Int) (a b c d : Bool) (f : ¬ x < y → Bool → Bool) (g : c → Bool → Bool),
    (if h1 : x < y then if h2 : c then g h2 a else b else f h1 d) = true ===>
  ∀ (x y : Int) (a b c d : Bool) (f : ¬ x < y → Bool → Bool) (g : true = c → Bool → Bool),
    (∀ (h1 : ¬ x < y), true = f h1 d) ∧ (x < y → (false = c → true = b) ∧
    (∀ (h2 : true = c), true = g h2 a))


-- ∀ (x y : Int) (a b c d : Bool) (f : x < y → Bool → Bool) (g : c → Bool → Bool),
--   (if h : x < y then f h d else if h2 : c then g h2 a else b) = true ===>
-- ∀ (x y : Int) (a b c d : Bool) (f : x < y → Bool → Bool) (g : true = c → Bool → Bool),
--   (¬ x < y → (false = c → true = b) ∧ (∀ (h2 : true = c), true = g h2 a)) ∧
--   (∀ (h : x < y), true = f h d)
#testOptimize [ "TrueEqDite_25" ]
  ∀ (x y : Int) (a b c d : Bool) (f : x < y → Bool → Bool) (g : c → Bool → Bool),
    (if h : x < y then f h d else if h2 : c then g h2 a else b) = true ===>
  ∀ (x y : Int) (a b c d : Bool) (f : x < y → Bool → Bool) (g : true = c → Bool → Bool),
    (¬ x < y → (false = c → true = b) ∧ (∀ (h2 : true = c), true = g h2 a)) ∧
    (∀ (h : x < y), true = f h d)


-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
--   (if h1 : x < y then (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d) else f h1 a) = true ===>
-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
--    (∀ (h1 : ¬ x < y), true = f h1 a) ∧
--    (x < y → (∀ (h2 : ¬ x < z), true = g h2 d) ∧
--    (x < z → (false = c → true = b) ∧ (∀ (h3 : true = c), true = t h3 a)))
#testOptimize [ "TrueEqDite_26" ]
  ∀ (x y z : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
    (if h1 : x < y then (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d) else f h1 a) = true ===>
  ∀ (x y z : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
     (∀ (h1 : ¬ x < y), true = f h1 a) ∧
     (x < y → (∀ (h2 : ¬ x < z), true = g h2 d) ∧
     (x < z → (false = c → true = b) ∧ (∀ (h3 : true = c), true = t h3 a)))

-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
--    (if h1 : x < y then f h1 a else (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d)) = true ===>
-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
--    (¬ x < y → (∀ (h2 : ¬ x < z), true = g h2 d) ∧ (x < z → (false = c → true = b) ∧
--    (∀ (h3 : true = c), true = t h3 a))) ∧ (∀ (h1 : x < y), true = f h1 a)
#testOptimize [ "TrueEqDite_27" ]
  ∀ (x y z : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
     (if h1 : x < y then f h1 a else (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d)) = true ===>
  ∀ (x y z : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
     (¬ x < y → (∀ (h2 : ¬ x < z), true = g h2 d) ∧ (x < z → (false = c → true = b) ∧
     (∀ (h3 : true = c), true = t h3 a))) ∧ (∀ (h1 : x < y), true = f h1 a)


/-! Test cases for simplification rule
     `false = dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> (c → false = e1) ∧ (¬ c → false = e2)`.
-/

-- ∀ (c a b : Bool) (f : c → Bool → Bool), (if h : c then f h a else b) = false ===>
-- ∀ (c a b : Bool) (f : true = c → Bool → Bool),
--   (false = c → false = b) ∧ (∀ (h : true = c), false = f h a)
#testOptimize [ "FalseEqDite_1" ]
  ∀ (c a b : Bool) (f : c → Bool → Bool), (if h : c then f h a else b) = false ===>
  ∀ (c a b : Bool) (f : true = c → Bool → Bool),
    (false = c → false = b) ∧ (∀ (h : true = c), false = f h a)

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool), (if h : a then true else f h b) = false ===>
-- ∀ (a b : Bool) (f : false = a → Bool → Bool),
--   false = a ∧ (∀ (h : false = a), false = f h b)
#testOptimize [ "FalseEqDite_2" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool), (if h : a then true else f h b) = false ===>
  ∀ (a b : Bool) (f : false = a → Bool → Bool),
    false = a ∧ (∀ (h : false = a), false = f h b)

-- ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else true) = false ===>
-- ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), false = f h b)
#testOptimize [ "FalseEqDite_3" ]
  ∀ (a b : Bool) (f : a → Bool → Bool), (if h : a then f h b else true) = false ===>
  ∀ (a b : Bool) (f : true = a → Bool → Bool), true = a ∧ (∀ (h : true = a), false = f h b)

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then false else f h b) = false ===>
-- ∀ (a b : Bool) (f : false = a → Bool → Bool),
--  ∀ (h : false = a), false = f h b
#testOptimize [ "FalseEqDite_4" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then false else f h b) = false ===>
  ∀ (a b : Bool) (f : false = a → Bool → Bool),
   ∀ (h : false = a), false = f h b

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else false) = false ===>
-- ∀ (a b : Bool) (f : true = a → Bool → Bool),
--   ∀ (h : true = a), false = f h b
#testOptimize [ "FalseEqDite_5" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else false) = false ===>
  ∀ (a b : Bool) (f : true = a → Bool → Bool),
    ∀ (h : true = a), false = f h b

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   false = (if h : a then a else f h b) ===>
-- ∀ (a b : Bool) (f : false = a → Bool → Bool),
--   false = a ∧ ∀ (h : false = a), false = f h b
#testOptimize [ "FalseEqDite_6" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    false = (if h : a then a else f h b) ===>
  ∀ (a b : Bool) (f : false = a → Bool → Bool),
    false = a ∧ ∀ (h : false = a), false = f h b

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else a) = false ===>
-- ∀ (a b : Bool) (f : true = a → Bool → Bool),
--   ∀ (h : true = a), false = f h b
#testOptimize [ "FalseEqDite_7" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else a) = false ===>
  ∀ (a b : Bool) (f : true = a → Bool → Bool),
    ∀ (h : true = a), false = f h b

-- ∀ (c a b : Bool) (f : !c → Bool → Bool),
--   (if h : !c then f h a else b) = false ===>
-- ∀ (c a b : Bool) (f : false = c → Bool → Bool),
--   (∀ (h : false = c), false = f h a) ∧ (true = c → false = b)
#testOptimize [ "FalseEqDite_8" ]
  ∀ (c a b : Bool) (f : !c → Bool → Bool),
    (if h : !c then f h a else b) = false ===>
  ∀ (c a b : Bool) (f : false = c → Bool → Bool),
    (∀ (h : false = c), false = f h a) ∧ (true = c → false = b)

-- ∀ (c a b : Bool) (f : c → Bool → Bool),
--     (if h : c then f h a else b) = false →
--   (false = c → false = b) ∧ (∀ (h : c), false = f h a) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_9" ]
  ∀ (c a b : Bool) (f : c → Bool → Bool),
      (if h : c then f h a else b) = false →
    (false = c → false = b) ∧ (∀ (h : c), false = f h a) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then true else f h b) = false →
--     false = a ∧ (∀ (h : ¬ a), false = f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_10" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then true else f h b) = false →
      false = a ∧ (∀ (h : ¬ a), false = f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else true) = false →
--     true = a ∧ (∀ (h : a), false = f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_11" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else true) = false →
      true = a ∧ (∀ (h : a), false = f h b) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then false else f h b) = false →
--     (∀ ( h : ¬ a), false = f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_12" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then false else f h b) = false →
      (∀ ( h : ¬ a), false = f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else false) = false →
--     (∀ (h : a), false = f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_13" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else false) = false →
      (∀ (h : a), false = f h b) ===> True

-- ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
--   (if h : a then a else f h b) = false →
--       false = a ∧ (∀ (h : ¬ a), false = f h b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_14" ]
  ∀ (a b : Bool) (f : ¬ a → Bool → Bool),
    (if h : a then a else f h b) = false →
        false = a ∧ (∀ (h : ¬ a), false = f h b) ===> True

-- ∀ (a b : Bool) (f : a → Bool → Bool),
--   (if h : a then f h b else a) = false →
--    ∀ (h : a), false = f h b ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "FalseEqDite_15" ]
  ∀ (a b : Bool) (f : a → Bool → Bool),
    (if h : a then f h b else a) = false →
     ∀ (h : a), false = f h b ===> True

 -- ∀ (c a b : Bool) (f : !c → Bool → Bool),
 --   (if h : !c then f h a else b) = false →
 --     (∀ (h : !c), false = f h a) ∧ (true = c → false = b) ===> True
#testOptimize [ "FalseEqDite_16" ]
 ∀ (c a b : Bool) (f : !c → Bool → Bool),
   (if h : !c then f h a else b) = false →
     (∀ (h : !c), false = f h a) ∧ (true = c → false = b) ===> True


-- ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
--   (if h : c = d then f h a else b) = false ===>
-- ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
--   (¬ (c = d) → false = b) ∧ (∀ (h : c = d), false = f h a)
#testOptimize [ "FalseEqDite_17" ]
  ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
    (if h : c = d then f h a else b) = false ===>
  ∀ (a b c d : Bool) (f : c = d → Bool → Bool),
    (¬ (c = d) → false = b) ∧ (∀ (h : c = d), false = f h a)

-- ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool), [Decidable c] →
--   (if h : c then f h a else b) = false ===>
-- ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool),
--   (∀ (h : c), false = f h a) ∧ (¬ c → false = b)
#testOptimize [ "FalseEqDite_18" ]
  ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool), [Decidable c] →
    (if h : c then f h a else b) = false ===>
  ∀ (c : Prop) (a b : Bool) (f : c → Bool → Bool),
    (∀ (h : c), false = f h a) ∧ (¬ c → false = b)

-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   (if h : a = c then true else f h b) = false ===>
-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   ¬ (a = c) ∧ ∀ (h : ¬ a = c), false = f h b
#testOptimize [ "FalseEqDite_19" ]
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    (if h : a = c then true else f h b) = false ===>
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    ¬ (a = c) ∧ ∀ (h : ¬ a = c), false = f h b

-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   (if h : a = c then f h b else true) = false ===>
-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   a = c ∧ ∀ (h : a = c), false = f h b
#testOptimize [ "FalseEqDite_20" ]
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    (if h : a = c then f h b else true) = false ===>
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    a = c ∧ ∀ (h : a = c), false = f h b

-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   (if h : a = c then false else f h b) = false ===>
-- ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
--   ∀ (h : ¬ a = c), false = f h b
#testOptimize [ "FalseEqDite_21" ]
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    (if h : a = c then false else f h b) = false ===>
  ∀ (a b c : Bool) (f : ¬ a = c → Bool → Bool),
    ∀ (h : ¬ a = c), false = f h b

-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   (if h : a = c then f h b else false) = false ===>
-- ∀ (a b c : Bool) (f : a = c → Bool → Bool),
--   ∀ (h : a = c), false = f h b
#testOptimize [ "FalseEqDite_22" ]
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    (if h : a = c then f h b else false) = false ===>
  ∀ (a b c : Bool) (f : a = c → Bool → Bool),
    ∀ (h : a = c), false = f h b

-- ∀ (x y : Int) (a b : Bool) (f : x < y → Bool → Bool),
--   (if h : x < y then f h a else b) = false ===>
-- ∀ (x y : Int) (a b: Bool) (f : x < y → Bool → Bool),
--   (¬ x < y → false = b) ∧ (∀ (h : x < y), false = f h a)
#testOptimize [ "FalseEqDite_23" ]
  ∀ (x y : Int) (a b : Bool) (f : x < y → Bool → Bool),
    (if h : x < y then f h a else b) = false ===>
  ∀ (x y : Int) (a b: Bool) (f : x < y → Bool → Bool),
    (¬ x < y → false = b) ∧ (∀ (h : x < y), false = f h a)

-- ∀ (x y : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : c → Bool → Bool),
--     (if h1 : x < y then if h2 : c then g h2 a else b else f h1 d) = false ===>
-- ∀ (x y : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : true = c → Bool → Bool),
--     (∀ (h1 : ¬ x < y), false = f h1 d) ∧ (x < y → (false = c → false = b) ∧
--     (∀ (h2 : true = c), false = g h2 a))
#testOptimize [ "FalseEqDite_24" ]
  ∀ (x y : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : c → Bool → Bool),
      (if h1 : x < y then if h2 : c then g h2 a else b else f h1 d) = false ===>
  ∀ (x y : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : true = c → Bool → Bool),
      (∀ (h1 : ¬ x < y), false = f h1 d) ∧ (x < y → (false = c → false = b) ∧
      (∀ (h2 : true = c), false = g h2 a))


-- ∀ (x y : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : c → Bool → Bool),
--     (if h1 : x < y then f h1 d else if h2 : c then g h2 a else b) = false ===>
-- ∀ (x y : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : true = c → Bool → Bool),
--   (¬ x < y → (false = c → false = b) ∧ (∀ (h2 : true = c), false = g h2 a)) ∧
--   (∀ (h1 : x < y), false = f h1 d)
#testOptimize [ "FalseEqDite_25" ]
  ∀ (x y : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : c → Bool → Bool),
      (if h1 : x < y then f h1 d else if h2 : c then g h2 a else b) = false ===>
  ∀ (x y : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : true = c → Bool → Bool),
    (¬ x < y → (false = c → false = b) ∧ (∀ (h2 : true = c), false = g h2 a)) ∧
    (∀ (h1 : x < y), false = f h1 d)


-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
--     (if h1 : x < y then (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d) else f h1 a) = false ===>
-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
--    (∀ (h1 : ¬ x < y), false = f h1 a) ∧
--    (x < y →
--      (∀ (h2 : ¬ x < z), false = g h2 d) ∧
--      (x < z → (false = c → false = b) ∧ (∀ (h3 : true = c), false = t h3 a)))
#testOptimize [ "FalseEqDite_26" ]
  ∀ (x y z : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
      (if h1 : x < y then (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d) else f h1 a) = false ===>
  ∀ (x y z : Int) (a b c d : Bool)
    (f : ¬ x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
     (∀ (h1 : ¬ x < y), false = f h1 a) ∧
     (x < y →
       (∀ (h2 : ¬ x < z), false = g h2 d) ∧
       (x < z → (false = c → false = b) ∧ (∀ (h3 : true = c), false = t h3 a)))

-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
--    (if h1 : x < y then f h1 a else (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d)) = false ===>
-- ∀ (x y z : Int) (a b c d : Bool)
--   (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
--    (¬ x < y →
--       (∀ (h2 : ¬ x < z), false = g h2 d) ∧
--       (x < z → (false = c → false = b) ∧ (∀ (h3 : true = c), false = t h3 a))) ∧
--    (∀ (h1 : x < y), false = f h1 a)
#testOptimize [ "FalseEqDite_27" ]
  ∀ (x y z : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : c → Bool → Bool),
     (if h1 : x < y then f h1 a else (if h2 : x < z then (if h3 : c then t h3 a else b) else g h2 d)) = false ===>
  ∀ (x y z : Int) (a b c d : Bool)
    (f : x < y → Bool → Bool) (g : ¬ x < z → Bool → Bool) (t : true = c → Bool → Bool),
     (¬ x < y →
        (∀ (h2 : ¬ x < z), false = g h2 d) ∧
        (x < z → (false = c → false = b) ∧ (∀ (h3 : true = c), false = t h3 a))) ∧
     (∀ (h1 : x < y), false = f h1 a)


/-! Test cases to ensure that simplification rules
     - `true = dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> (c → true = e1) ∧ (¬ c → true = e2)`.
     - `false = dite c (fun h : c => e1) (fun h : ¬ c => e2) ==> (c → false = e1) ∧ (¬ c → false = e2)`.
    are not wrongly applied.
-/

def boolEqDIteUnchanged_1 : Expr :=
Lean.Expr.forallE `c
  (Lean.Expr.const `Bool [])
  (Lean.Expr.forallE `a
    (Lean.Expr.const `Bool [])
    (Lean.Expr.forallE `b
      (Lean.Expr.const `Bool [])
      (Lean.Expr.forallE `d
        (Lean.Expr.const `Bool [])
        (Lean.Expr.forallE `f
          (Lean.Expr.forallE
            (Lean.Name.mkNum `a.Tests.Optimize.OptimizeDecide.DecideEq._hyg 14440)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                (Lean.Expr.const `Bool.true []))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE
              (Lean.Name.mkNum `a.Tests.Optimize.OptimizeDecide.DecideEq._hyg 14442)
              (Lean.Expr.const `Bool [])
              (Lean.Expr.const `Bool [])
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Blaster.dite' [Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.const `Bool []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Bool []))
                        (Lean.Expr.const `Bool.true []))
                      (Lean.Expr.bvar 4)))
                (Lean.Expr.lam `h
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Bool []))
                      (Lean.Expr.const `Bool.true []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 4))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.lam `h
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
                    (Lean.Expr.const `Bool.false []))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 3)
                (Lean.BinderInfo.default))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
elab "boolEqDIteUnchanged_1" : term => return boolEqDIteUnchanged_1

-- ∀ (c a b d : Bool) (f : c → Bool → Bool), d = (if h : c then f h a else b) ===>
-- ∀ (c a b d : Bool) (f : true = c → Bool → Bool),
--   d = Blaster.dite' (true = c) (fun h : true = c => f h a) (fun _ => b)
#testOptimize [ "BoolEqDIteUnchanged_1" ]
  ∀ (c a b d : Bool) (f : c → Bool → Bool),
    d = if h : c then f h a else b ===> boolEqDIteUnchanged_1


-- ∀ (c a b d : Bool) (f : c → Bool → Bool), (if h : c then a else b) = d ===>
-- ∀ (c a b d : Bool) (f : true = c → Bool → Bool),
--   d = Blaster.dite' (true = c) (fun h : true = c => f h a) (fun _ => b)
#testOptimize [ "BoolEqDIteUnchanged_2" ]
  ∀ (c a b d : Bool) (f : c → Bool → Bool),
    (if h : c then f h a else b) = d ===> boolEqDIteUnchanged_1


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

-- true = decide (x ≤ y) ===> ¬ y < x
#testOptimize [ "DecideEqTrue_4"] true = decide (x ≤ y) ===> ¬ y < x


variable (z : Int)
-- true = decide (x ≤ y ∧ z ≥ y) ===> ¬ y < x ∧ ¬ z < y
#testOptimize [ "DecideEqTrue_5"] true = decide (x ≤ y ∧ z ≥ y) ===> ¬ y < x ∧ ¬ z < y

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
-- ∀ (x y : Int), x < y
#testOptimize [ "DecideEqTrue_6"] ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] →
                                    decide ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
                                  ∀ (x y : Int), x < y

-- ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), ¬ y < x
#testOptimize [ "DecideEqTrue_7"] ∀ (x y : Nat), x ≤ y && x ≤ y ===> ∀ (x y : Nat), ¬ y < x


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
-- ∀ (x y z : Int) (a : Bool), Blaster.dite' (¬ y < x ∧ true = a) (fun _ => x) (fun _ => y) < z
#testOptimize [ "DecideEqTrue_15"]
  ∀ (x y z : Int) (a b c : Bool), (if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z ===>
  ∀ (x y z : Int) (a : Bool), Blaster.dite' (¬ y < x ∧ true = a) (fun _ => x) (fun _ => y) < z

-- ∀ (x y z : Int) (a b c : Bool),
--  ((if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z) =
--  (z > (if (x ≤ y) ∧ a then x else y)) ===> True
#testOptimize [ "DecideEqTrue_16"]
  ∀ (x y z : Int) (a b c : Bool),
    ((if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) < z) =
    (z > (if (x ≤ y) ∧ a then x else y)) ===> True


/-! Test cases for simplification rule `false = decide e ==> ¬ e`. -/

-- ∀ (a : Prop), [Decidable a] → false = decide a ===> ∀ (a : Prop), ¬ a
#testOptimize [ "DecideEqFalse_1"]
  ∀ (a : Prop), [Decidable a] → false = decide a ===> ∀ (a : Prop), ¬ a


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∧ b) ===>
-- ∀ (a b : Prop), ¬ a ∧ b
#testOptimize [ "DecideEqFalse_2"]
  ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∧ b) ===>
  ∀ (a b : Prop), ¬ (a ∧ b)

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∨ b) ===>
-- ∀ (a b : Prop), ¬ (a ∨ b)
#testOptimize [ "DecideEqFalse_3"]
  ∀ (a b : Prop), [Decidable a] → [Decidable b] → false = decide (a ∨ b) ===>
  ∀ (a b : Prop), ¬ (a ∨ b)

-- false = decide (x ≤ y) ===> y < x
#testOptimize [ "DecideEqFalse_4"] false = decide (x ≤ y) ===> y < x

-- false = decide (x ≤ y ∧ z ≥ y) ===> (y < x ∨ z < y)
#testOptimize [ "DecideEqFalse_5"] false = decide (x ≤ y ∧ z ≥ y) ===> (y < x ∨ z < y)

-- ∀ (a b : Prop), ∀ (x y : Int),
--  [Decidable a] → [Decidable b] →
--  decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
-- ∀ (x y : Int), ¬ x < y
#testOptimize [ "DecideEqFalse_6"]
  ∀ (a b : Prop) (x y : Int), [Decidable a] → [Decidable b] → decide ((a ∧ ¬ a) ∨ (b ∧ ¬ b)) = (x < y) ===>
  ∀ (x y : Int), ¬ x < y

-- ∀ (x y : Nat) (a b c : Bool), ((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y ===>
-- ∀ (x y : Nat), ¬ y < x
#testOptimize [ "DecideEqFalse_7"]
  ∀ (x y : Nat) (a b c : Bool), ((a || ((b || c) && !(c || b))) && !a) = ¬ x ≤ y ===>
  ∀ (x y : Nat), ¬ y < x

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
#testOptimize [ "DecideEqDecide_10" ]
  ∀ (x y z : Int) (a b : Bool), (¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z)) ===>
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
-- ((¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z))) = ((y ≤ x) = (y ≤ z)) ===> True
#testOptimize [ "DecideEqDecide_17" ] ∀ (x y z : Int) (a b : Bool),
                                      ((¬ (x < y) && (!a || a)) = ((b && !b) || ¬ (y > z))) = ((y ≤ x) = (y ≤ z)) ===> True


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
-- ∀ (x y : Int) (c : Bool), ¬ y < x = (true = c)
#testOptimize [ "DecideEqBool_3" ]
  ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = c ===>
  ∀ (x y : Int) (c : Bool), ¬ y < x = (true = c)


-- ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = (!c && (a || !a)) ===>
-- ∀ (x y : Int) (c : Bool), ¬ y < x = (false = c)
#testOptimize [ "DecideEqBool_4" ]
  ∀ (x y : Int) (a b c : Bool), (x ≤ y || (a && (b && !b))) = (!c && (a || !a)) ===>
  ∀ (x y : Int) (c : Bool), ¬ y < x = (false = c)

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
-- ∀ (x y z : Int) (b c : Bool), Blaster.dite' ((true = c ∧ (x < y)) = (true = b)) (fun _ => x) (fun _ => y) < z
#testOptimize [ "DecideEqBool_18" ]
  ∀ (x y z : Int) (b c : Bool), (if ((x < y) && c) == b then x else y) < z ===>
  ∀ (x y z : Int) (b c : Bool), Blaster.dite' ((true = c ∧ (x < y)) = (true = b)) (fun _ => x) (fun _ => y) < z

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
