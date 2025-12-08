import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.NominalDecide

/-! ## Test objectives to validate nominal `Decidable.decide` simplification rules. -/


/-! Test cases for simplification rule `decide False ==> false` -/

-- decide False ===> false
#testOptimize [ "DecideFalse_1" ] decide False ===> false

-- decide (¬ True) ===> false
#testOptimize [ "DecideFalse_2" ] decide (¬ True) ===> false

-- decide (False ∧ True) ===> false
#testOptimize [ "DecideFalse_3" ] decide (False ∧ True) ===> false

-- decide (true = false) ===> false
#testOptimize [ "DecideFalse_4" ] decide (true = false) ===> false

-- ∀ (a : Prop), [Decidable a] → (a ∧ False) = false ===> True
#testOptimize [ "DecideFalse_5" ] ∀ (a : Prop), [Decidable a] → (a ∧ False) = false ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → ((a ∧ False) ∧ b) = false ===> True
#testOptimize [ "DecideFalse_6" ]
  ∀ (a b : Prop), [Decidable a] → [Decidable b] → ((a ∧ False) ∧ b) = false ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) = false ===> True
#testOptimize [ "DecideFalse_7" ]
  ∀ (a b : Prop), [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) = false ===> True

-- ∀ (a b : Prop),
--  [Decidable a] → [Decidable b] → [Decidable c] →
--  (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) = false ===> True
#testOptimize [ "DecideFalse_8" ]
  ∀ (a b c : Prop), [Decidable a] → [Decidable b] → [Decidable c] →
      (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b))) = false ===> True

-- ∀ (a : Bool), (a = !a) = false ===> True
#testOptimize [ "DecideFalse_9" ] ∀ (a : Bool), (a = !a) = false ===> True

-- decide (List.nil = [1, 2, 3, 4]) ===> false
#testOptimize [ "DecideFalse_10" ] decide (List.nil = [1, 2, 3, 4]) ===> false

variable (a : Nat)
variable (b : Nat)
variable (c : Nat)
-- decide (List.nil = [a, b, c]) ===> false
#testOptimize [ "DecideFalse_11" ] decide (List.nil = [a, b, c]) ===> false

-- ∀ (x y z : Int), ([x, y] = [x, y, z]) = false ===> True
#testOptimize [ "DecideFalse_12" ] ∀ (x y z : Int), ([x, y] = [x, y, z]) = false ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (b ∧ ¬ b) && a ===> False
-- NOTE: `(b ∧ ¬ b) && a` is represented as `decide (b ∧ ¬ b) && (decide a)`
#testOptimize [ "DecideFalse_13" ] ∀ (a b : Prop), [Decidable a] → [Decidable b] → (b ∧ ¬ b) && a ===> False


-- ∀ (a : Bool) (b : Prop), [Decidable b] → (b ∧ ¬ b) && a ===> False
-- NOTE: `(b ∧ ¬ b) && a` is represented as `decide (b ∧ ¬ b) && a`
#testOptimize [ "DecideFalse_14" ] ∀ (a : Bool) (b : Prop), [Decidable b] → (b ∧ ¬ b) && a ===> False


-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) && c ===> False
#testOptimize [ "DecideFalse_15" ] ∀ (a b : Prop) (c : Bool),
                                   [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) && c ===> False


/-! Test cases for simplification rule `decide True ==> true` -/

-- decide True ===> true
#testOptimize [ "DecideTrue_1" ] decide True ===> true

-- decide (¬ False) ===> true
#testOptimize [ "DecideTrue_2" ] decide (¬ False) ===> true

-- decide (True ∧ True) ===> true
#testOptimize [ "DecideTrue_3" ] decide (True ∧ True) ===> true

-- decide (True ∨ False) ===> true
#testOptimize [ "DecideTrue_4" ] decide (True ∨ False) ===> true

-- decide (true = true) ===> true
#testOptimize [ "DecideTrue_5" ] decide (true = true) ===> true

-- ∀ (a : Prop), [Decidable a] → (a ∨ True) = true ===> True
#testOptimize [ "DecideTrue_6" ] ∀ (a : Prop), [Decidable a] → (a ∨ True) = true ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (a ∨ True ∨ b) = true ===> True
#testOptimize [ "DecideTrue_7" ] ∀ (a b : Prop),
                                    [Decidable a] → [Decidable b] → (a ∨ True ∨ b) = true ===> True

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = true ===> True
#testOptimize [ "DecideTrue_8" ] ∀ (a b : Prop),
                                   [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∨ (b ∧ ¬ b)) = true ===> True

-- ∀ (a b : Prop),
--  [Decidable a] → [Decidable b] → [Decidable c] →
--  (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∨ ((b ∧ a) ∧ c)) = true ===> True
#testOptimize [ "DecideTrue_9" ] ∀ (a b c : Prop),
                                  [Decidable a] → [Decidable b] → [Decidable c] →
                                  (((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∨ ((b ∧ a) ∧ c)) = true ===> True

-- ∀ (a : Bool), decide (a = a) = true ===> True
#testOptimize [ "DecideTrue_10" ] ∀ (a : Bool), decide (a = a) = true ===> True

-- decide ((List.nil : List Int) = List.nil) ===> false
#testOptimize [ "DecideTrue_11" ] decide ((List.nil : List Int) = List.nil) ===> true

-- decide ( [a, b, c] = [a, b, c]) ===> true
#testOptimize [ "DecideTrue_12" ] decide ([a, b, c] = [a, b, c]) ===> true

-- ∀ (x y z : Int), ([x, y, z] = [x, y, z]) = true ===> True
#testOptimize [ "DecideTrue_13" ] ∀ (x y z : Int), ([x, y, z] = [x, y, z]) = true ===> True


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (b ∨ ¬ b) && a ===> ∀ (a : Prop), a
-- NOTE: `(b ∨ ¬ b) && a` is represented as `decide (b ∨ ¬ b) && (decide a)`
-- NOTE: simplification also via rule `true = decide e ===> e`
#testOptimize [ "DecideTrue_14" ] ∀ (a b : Prop), [Decidable a] → [Decidable b] → (b ∨ ¬ b) && a ===>
                                  ∀ (a : Prop), a


-- ∀ (a : Bool) (b : Prop), [Decidable b] → (b ∨ ¬ b) && a ===> ∀ (a : Bool), true = a
-- NOTE: `(b ∨ ¬ b) && a` is represented as `decide (b ∨ ¬ b) && a`
#testOptimize [ "DecideTrue_15" ] ∀ (a : Bool) (b : Prop), [Decidable b] → (b ∨ ¬ b) && a ===>
                                  ∀ (a : Bool), true = a

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) || c ===>
-- ∀ (c : Bool), true = c
#testOptimize [ "DecideTrue_16" ] ∀ (a b : Prop) (c : Bool),
                                   [Decidable a] → [Decidable b] → ((a ∨ ¬ a) ∧ (b ∧ ¬ b)) || c ===>
                                  ∀ (c : Bool), true = c


/-! Test cases for simplification rule `decide (true = p) ==> p` -/

variable (p : Bool)
-- decide (true = p) ===> p
#testOptimize [ "DecideEqTrue_1" ] decide (true = p) ===> p

-- decide (p = true) ===> p
#testOptimize [ "DecideEqTrue_2" ] decide (p = true) ===> p

-- decide (true = (! (!p))) ===> p
#testOptimize [ "DecideEqTrue_3" ] decide (true = (! (!p))) ===> p

-- decide (true = !(!(!(!p)))) ===> p
#testOptimize [ "DecideEqTrue_4" ] decide (true = !(!(!(!p)))) ===> p

-- decide (false = !p) ===> p
#testOptimize [ "DecideEqTrue_5" ] decide (false = !p) ===> p

-- decide (false = !(!(!p))) ===> p
#testOptimize [ "DecideEqTrue_6" ] decide (false = !(!(!p))) ===> p

-- decide (p ∧ ((a < b) ∨ ¬ (b > a))) ===> p
#testOptimize [ "DecideEqTrue_7" ] decide (p ∧ ((a < b) ∨ ¬ (b > a))) ===> p


/-! Test cases for simplification rule `decide (false = p) ==> ! p`. -/

-- decide (false = p) ===> ! p
#testOptimize [ "DecideEqFalse_1" ] decide (false = p) ===> ! p

-- decide (p = false) ===> ! p
#testOptimize [ "DecideEqFalse_2" ] decide (p = false) ===> ! p

-- decide (false = (! (!p))) ===> ! p
#testOptimize [ "DecideEqFalse_3" ] decide (false = (! (!p))) ===> ! p

-- decide (false = !(!(!(!p)))) ===> ! p
#testOptimize [ "DecideEqFalse_4" ] decide (false = !(!(!(!p)))) ===> ! p

-- decide (true = !p) ===> ! p
#testOptimize [ "DecideEqFalse_5" ] decide (true = !p) ===> ! p

-- decide (true = !(!(!p))) ===> ! p
#testOptimize [ "DecideEqFalse_6" ] decide (true = !(!(!p))) ===> ! p

-- decide (¬ p) ===> ! p
#testOptimize [ "DecideEqFalse_7" ] decide (¬ p) ===> ! p

variable (q : Bool)

-- decide (¬ (¬ (¬ p ∧ (a < b ∨ ¬ (b > a))) ∧ (¬ q v q))) ===> ! p
#testOptimize [ "DecideEqFalse_8" ] decide (¬ (¬ (¬ p ∧ ((a < b) ∨ ¬ (b > a))) ∧ (¬ q ∨ q))) ===> ! p


/-! Test cases to validate proper update of Decidable instance in `decide` application. -/

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → (((a ∧ b) ∧ (b ∨ ¬ b)) && c) = (c && (a ∧ b)) ===> True
#testOptimize [ "DecideDecidableUpdate_1" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                             (((a ∧ b) ∧ (b ∨ ¬ b)) && c) = (c && (a ∧ b)) ===> True

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → ((a ∧ b) ∧ ((b ∨ ¬ b) && c)) = (c ∧ (a ∧ b)) ===> True
#testOptimize [ "DecideDecidableUpdate_2" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                             ((a ∧ b) ∧ ((b ∨ ¬ b) && c)) = (c ∧ (a ∧ b)) ===> True

-- ∀ (x y : Int) (a b c : Bool),
-- (if (x ≤ y) && ((a || ((b || c) && !(c || b)))) then x else y) =
-- (if (x ≤ y) && a then x else y) ===> True
#testOptimize [ "DecideDecidableUpdate_3" ] ∀ (x y : Int) (a b c : Bool),
                                              (if (x ≤ y ∧ y ≥ x) && ((a || ((b || c) && !(c || b)))) then x else y) =
                                              (if (x ≤ y) && a then x else y) ===> True


-- ∀ (x y : Int) (a b c : Bool),
-- (if c then (x ≤ y ∧ (a ∨ ((b ∨ c) ∧ ¬ (c ∨ b)))) else b =
-- (if c then x ≤ y ∧ true = a else b) ===> True
#testOptimize [ "DecideDecidableUpdate_4" ] ∀ (x y : Int) (a b c : Bool),
                                              (if c then (x ≤ y ∧ (a ∨ ((b ∨ c) ∧ ¬ (c ∨ b)))) else b) =
                                              (if c then x ≤ y ∧ true = a else b) ===> True


/-! Test cases to ensure that the following simplification rules are not wrongly applied:
     - `decide False ==> false`
     - `decide True ==> true`
     - `decide (true = p) ==> p`
     - `decide (false = p) ==> ! p`
-/
-- ∀ (a : Prop), [Decidable a] → decide a === ∀ (a : Prop), a
-- NOTE: `true = decide p` is reduce to `p`
#testOptimize [ "DecideUnchanged_1" ] ∀ (a : Prop), [Decidable a] → decide a ===> ∀ (a : Prop), a


-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → decide (a = b) ===> ∀ (a b : Prop), a = b
-- NOTE: `true = decide p` is reduced to `p`
#testOptimize [ "DecideUnchanged_2" ] ∀ (a b : Prop), [Decidable a] → [Decidable b] → decide (a = b) ===>
                                      ∀ (a b : Prop), a = b


-- ∀ (a : Prop) (b : Bool), [Decidable a] → decide a = b ===>
-- ∀ (a : Prop) (b : Bool), a = (true = b)
-- NOTE: `(decide a) = b` is normalized to `a = (true = b)`
#testOptimize [ "DecideUnchanged_3" ] ∀ (a : Prop) (b : Bool), [Decidable a] → (decide a) = b ===>
                                      ∀ (a : Prop) (b : Bool), a = (true = b)

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (a ∧ b) = false ===>
-- ∀ (a b : Prop), ¬ (a ∧ b)
-- NOTE: `false = decide p is normalized to `¬ p``
#testOptimize [ "DecideUnchanged_4" ] ∀ (a b : Prop), [Decidable a] → [Decidable b] → (a ∧ b) = false ===>
                                      ∀ (a b : Prop), ¬ (a ∧ b)

-- ∀ (a b c : Prop), [Decidable a] → [Decidable b] → [Decidable c] → (b ∧ c) && a ===>
-- ∀ (a b c : Prop), a ∧ (b ∧ c)
#testOptimize [ "DecideUnchanged_5" ] ∀ (a b c : Prop), [Decidable a] → [Decidable b] → [Decidable c] → (b ∧ c) && a ===>
                                      ∀ (a b c : Prop), a ∧ (b ∧ c)

-- ∀ (x y z : Int) (xs : List Int), ([x, y, z] = xs) = false ===>
-- ∀ (x y z : Int) (xs : List Int), ¬ ([x, y, z] = xs)
-- NOTE: `false = decide p is normalized to `¬ p`
#testOptimize [ "DecideUnchanged_6" ] ∀ (x y z : Int) (xs : List Int), ([x, y, z] = xs) = false ===>
                                      ∀ (x y z : Int) (xs : List Int), ¬ ([x, y, z] = xs)

-- ∀ (a b : Prop), [Decidable a] → [Decidable b] → (a ∨ b) = true ===>
-- ∀ (a b : Prop), (a ∨ b)
-- NOTE: `true = decide p` is reduced to `p`
#testOptimize [ "DecideUnchanged_7" ] ∀ (a b : Prop), [Decidable a] → [Decidable b] → (a ∨ b) = true ===>
                                      ∀ (a b : Prop), (a ∨ b)

-- ∀ (a b c : Prop), [Decidable a] → [Decidable b] → [Decidable c] → (b ∨ c) && a ===>
-- ∀ (a b c : Prop), a ∧ (b ∨ c)
#testOptimize [ "DecideUnchanged_8" ] ∀ (a b c : Prop), [Decidable a] → [Decidable b] → [Decidable c] → (b ∨ c) && a ===>
                                      ∀ (a b c : Prop), a ∧ (b ∨ c)

-- ∀ (x y z : Int) (xs : List Int), ([x, y, z] = xs) = true ===>
-- ∀ (x y z : Int) (xs : List Int), [x, y, z] = xs
-- NOTE: `true = decide p` is reduced to `p`
#testOptimize [ "DecideUnchanged_9" ]  ∀ (x y z : Int) (xs : List Int), ([x, y, z] = xs) = true ===>
                                       ∀ (x y z : Int) (xs : List Int), [x, y, z] = xs

-- decide (q = !(!(!(!p)))) ===> Blaster.decide' (q = !p)
#testOptimize [ "DecideUnchanged_10" ] decide (q = (!(!(!p)))) ===> Blaster.decide' (q = !p)

-- decide (q = !(!(!(!p)))) ===> Blaster.decide' (p = q)
#testOptimize [ "DecideUnchanged_11" ] decide (q = !(!(!(!p)))) ===> Blaster.decide' (p = q)


end Test.NominalDecide
