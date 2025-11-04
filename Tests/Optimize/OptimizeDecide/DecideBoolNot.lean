import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.DecideBoolNot

/-! ## Test objectives to validate `Decidable.decide` simplification rules on Boolean `not`. -/

/-! Test cases for simplification rule `!(decide p) ==> decide (¬ p)`. -/

-- ∀ (a : Prop), [Decidable a] → !(decide a) = decide (¬ a) ===> True
#testOptimize [ "NotDecide_1" ] ∀ (a : Prop), [Decidable a] → !(decide a) = decide (¬ a) ===> True

-- ∀ (a : Prop), [Decidable a] → !(decide a) ===> ∀ (a : Prop), ¬ a
-- NOTE: `true = decide e` is reduced to `e`
#testOptimize [ "NotDecide_2" ] ∀ (a : Prop), [Decidable a] → !(decide a) ===> ∀ (a : Prop), ¬ a

-- ∀ (a : Prop), [Decidable a] → !(decide a) = decide (False = a) ===> True
#testOptimize [ "NotDecide_3" ] ∀ (a : Prop), [Decidable a] → !(decide a) = decide (False = a) ===> True

-- ∀ (a : Prop), [Decidable a] → decide (a = False) = !(decide a) ===> True
#testOptimize [ "NotDecide_4" ] ∀ (a : Prop), [Decidable a] → decide (a = False) = !(decide a) ===> True

-- ∀ (a : Prop), [Decidable a] → !(decide ¬ a) = decide a ===> True
#testOptimize [ "NotDecide_5" ] ∀ (a : Prop), [Decidable a] → !(decide ¬ a) = decide a ===> True

-- ∀ (a : Prop), [Decidable a] → !decide (¬ a) ===> ∀ (a : Prop), a
-- NOTE: `true = decide e` is reduced to `e`
#testOptimize [ "NotDecide_6" ] ∀ (a : Prop), [Decidable a] → !decide (¬ a) ===> ∀ (a : Prop), a

-- ∀ (x y : Int) (b : Bool), ((¬ (x ≤ y) || !(x ≤ y)) && b) = (¬ (x ≤ y) ∧ true = b) ===> True
#testOptimize [ "NotDecide_7" ] ∀ (x y : Int) (b : Bool),
                                 ((¬ (x ≤ y) || !(x ≤ y)) && b) = (¬ (x ≤ y) ∧ true = b) ===> True

-- ∀ (x y : Int) (b : Bool), (¬ (x ≤ y) || !(x ≤ y)) && b ===>
-- ∀ (x y : Int) (b : Bool), true = b ∧ (y < x)
#testOptimize [ "NotDecide_8" ] ∀ (x y : Int) (b : Bool), (¬ (x ≤ y) || !(x ≤ y)) && b ===>
                                ∀ (x y : Int) (b : Bool), true = b ∧ (y < x)

-- ∀ (a : Prop) (b c : Bool), [Decidable a] → (¬ a || ((b || c) && !(c || b)) || ¬ a) = !(decide a) ===> True
#testOptimize [ "NotDecide_9" ] ∀ (a : Prop) (b c : Bool), [Decidable a] →
                                  (¬ a || ((b || c) && !(c || b)) || ¬ a) = !(decide a) ===> True

-- ∀ (a : Prop) (b c : Bool), [Decidable a] → (¬ a || ((b || c) && !(c || b)) || ¬ a) ===>
-- ∀ (a : Prop), ¬ a
-- NOTE: `false = decide e` is reduced to `¬ e`
#testOptimize [ "NotDecide_10" ] ∀ (a : Prop) (b c : Bool), [Decidable a] →
                                   (¬ a || ((b || c) && !(c || b)) || ¬ a) ===>
                                 ∀ (a : Prop), ¬ a

-- ∀ (a : Prop) (b c : Bool), [Decidable a] → (!a || ((b || c) && !(c || b)) || !a) = decide (¬ a) ===> True
#testOptimize [ "NotDecide_11" ] ∀ (a : Prop) (b c : Bool), [Decidable a] →
                                   (!a || ((b || c) && !(c || b)) || !a) = decide (¬ a) ===> True

-- ∀ (a : Prop) (b c : Bool), [Decidable a] → (!a || ((b || c) && !(c || b)) || !a) ===>
-- ∀ (a : Prop), ¬ a
-- NOTE: `false = decide e` is reduced to `¬ e`
#testOptimize [ "NotDecide_12" ] ∀ (a : Prop) (b c : Bool), [Decidable a] →
                                   (!a || ((b || c) && !(c || b)) || !a) ===>
                                 ∀ (a : Prop), ¬ a

-- !(decide False) ===> true
#testOptimize [ "NotDecide_13" ] !(decide False) ===> true

-- !(decide True) ===> false
#testOptimize [ "NotDecide_14" ] !(decide True) ===> false

-- ∀ (a b c : Prop) (d : Bool),
--  [Decidable a] → [Decidable b] → [Decidable c] →
--  ((¬ a ∧ ((c ∨ b) ∧ ¬ (b ∨ c)) ∧ a) && d) = false ===> True
#testOptimize [ "NotDecide_15" ] ∀ (a b c : Prop) (d : Bool), [Decidable a] → [Decidable b] → [Decidable c] →
                                   ((¬ a ∧ ((c ∨ b) ∧ ¬ (b ∨ c)) ∧ a) && d) = false ===> True

-- ∀ (a b c : Prop) (d : Bool),
--  [Decidable a] → [Decidable b] → [Decidable c] →
--  ((¬ a ∧ ((c ∨ b) ∧ ¬ (b ∨ c)) ∧ a) && d) ===> False
#testOptimize [ "NotDecide_16" ] ∀ (a b c : Prop) (d : Bool), [Decidable a] → [Decidable b] → [Decidable c] →
                                   ((¬ a ∧ ((c ∨ b) ∧ ¬ (b ∨ c)) ∧ a) && d) ===> False

-- ∀ (a b c : Prop) (d : Bool),
--  [Decidable a] → [Decidable b] → [Decidable c] →
--  ((¬ a ∨ ((c ∨ b) ∧ ¬ (b ∨ c)) ∨ a) && d) = d ===>
-- ∀ (d : Bool), true = d
#testOptimize [ "NotDecide_17" ] ∀ (a b c : Prop) (d : Bool), [Decidable a] → [Decidable b] → [Decidable c] →
                                   ((¬ a ∨ ((c ∨ b) ∧ ¬ (b ∨ c)) ∨ a) && d) ===>
                                 ∀ (d : Bool), true = d

-- ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] → !(if (c || !c) then ¬ a else b) && c ===>
-- ∀ (a : Prop), a ∧ true = c
#testOptimize [ "NotDecide_18" ] ∀ (a b : Prop) (c : Bool), [Decidable a] → [Decidable b] →
                                   !(if (c || !c) then ¬ a else b) && c ===>
                                 ∀ (a : Prop) (c : Bool), a ∧ (true = c)

/-! Test cases to ensure that rule ``!(decide p) ==> decide (¬ p)` is not wrongly applied. -/

-- ∀ (a : Prop) (b : Bool), [Decidable a] → (decide a) && b ===>
-- ∀ (a : Prop) (b : Bool), a ∧ true = b
-- NOTE: `true = decide p` is reduced to `p`
#testOptimize [ "NotDecideUnchanged_1" ] ∀ (a : Prop) (b : Bool), [Decidable a] → (decide a) && b ===>
                                         ∀ (a : Prop) (b : Bool), a ∧ true = b

-- ∀ (a : Prop), [Decidable a] → decide (¬ p) ===>
-- ∀ (a : Prop), ¬ a
-- NOTE: `true = decide e` is reduced to `e`
#testOptimize [ "NotDecideUnchanged_2" ] ∀ (a : Prop), [Decidable a] → decide ¬ a ===>
                                         ∀ (a : Prop), ¬ a

-- ∀ (a : Prop), [Decidable a] → !(!(decide a)) ===> ∀ (a : Prop), a
-- NOTE: `true = decide e` is reduced to `e`
#testOptimize [ "NotDecideUnchanged_3" ] ∀ (a : Prop), [Decidable a] → !(!(decide a)) ===> ∀ (a : Prop), a


end Test.DecideBoolNot
