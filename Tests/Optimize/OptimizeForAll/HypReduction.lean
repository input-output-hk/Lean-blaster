import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.HypReduction
/-! ## Test objectives to validate simplification rules:
      - h : e1 → e2 ==> e2 (if e1 := _ ∈ hypothesisContext.hypothesisMap ∧ ¬ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop)
      - h : e1 → e2 ==> e2[h/h'] (if e1 := h' ∈ hypothesisContext.hypothesisMap ∧ fVarInExpr h.fvarId! e2 ∧ Type(e2) = Prop )
-/

/-! Test cases to ensure that the rules are properly applied. -/

-- ∀ (a b : Prop), a → (a → b) ===>
-- ∀ (a b : Prop), a → b
#testOptimize [ "HypReduction_1" ]
  ∀ (a b : Prop), a → (a → b) ===>
  ∀ (a b : Prop), a → b

-- ∀ (a b c : Prop), (a ∧ c) → (a → b) ===>
-- ∀ (a b c : Prop), (a ∧ c) → b
#testOptimize [ "HypReduction_2" ]
  ∀ (a b c : Prop), (a ∧ c) → (a → b) ===>
  ∀ (a b c : Prop), (a ∧ c) → b

-- ∀ (a b c d : Prop), (a ∧ c) → d → (a → b) ===>
-- ∀ (a b c d : Prop), (a ∧ c) → d → b
#testOptimize [ "HypReduction_3" ]
  ∀ (a b c d : Prop), (a ∧ c) → d → (a → b) ===>
  ∀ (a b c d : Prop), (a ∧ c) → d → b

-- ∀ (x y : Int) (b : Prop), x = y → (x ≤ y → b) ===>
-- ∀ (x y : Int) (b : Prop), x = y → b
#testOptimize [ "HypReduction_4" ]
  ∀ (x y : Int) (b : Prop), x = y → (x ≤ y → b) ===>
  ∀ (x y : Int) (b : Prop), x = y → b

-- ∀ (x y : Int) (b : Prop), x < y → (x ≤ y → b) ===>
-- ∀ (x y : Int) (b : Prop), x < y → b
#testOptimize [ "HypReduction_5" ]
  ∀ (x y : Int) (b : Prop), x < y → (x ≤ y → b) ===>
  ∀ (x y : Int) (b : Prop), x < y → b

-- ∀ (x y : Nat) (b : Prop), x = y → (x ≤ y → b) ===>
-- ∀ (x y : Nat) (b : Prop), x = y → b
#testOptimize [ "HypReduction_6" ]
  ∀ (x y : Nat) (b : Prop), x = y → (x ≤ y → b) ===>
  ∀ (x y : Nat) (b : Prop), x = y → b

-- ∀ (x y : Nat) (b : Prop), x < y → (x ≤ y → b) ===>
-- ∀ (x y : Nat) (b : Prop), x < y → b
#testOptimize [ "HypReduction_7" ]
  ∀ (x y : Nat) (b : Prop), x < y → (x ≤ y → b) ===>
  ∀ (x y : Nat) (b : Prop), x < y → b


-- ∀ (x y : Int) (a b c : Prop), (a ∧ x = y) → c → (x ≤ y → b) ===>
-- ∀ (x y : Int) (a b c : Prop), (a ∧ x = y) → c → b
#testOptimize [ "HypReduction_8" ]
  ∀ (x y : Int) (a b c : Prop), (a ∧ x = y) → c → (x ≤ y → b) ===>
  ∀ (x y : Int) (a b c : Prop), (a ∧ x = y) → c → b

-- ∀ (x y : Int) (a b c : Prop), (x < y ∧ a) → c → (x ≤ y → b) ===>
-- ∀ (x y : Int) (a b c : Prop), (a ∧ x < y) → c → b
#testOptimize [ "HypReduction_9" ]
  ∀ (x y : Int) (a b c : Prop), (x < y ∧ a) → c → (x ≤ y → b) ===>
  ∀ (x y : Int) (a b c : Prop), (a ∧ x < y) → c → b

-- ∀ (x y : Nat) (a b c : Prop), (a ∧ x = y) → c → (x ≤ y → b) ===>
-- ∀ (x y : Nat) (a b c : Prop), (a ∧ x = y) → c → b
#testOptimize [ "HypReduction_10" ]
  ∀ (x y : Nat) (a b c : Prop), (a ∧ x = y) → c → (x ≤ y → b) ===>
  ∀ (x y : Nat) (a b c : Prop), (a ∧ x = y) → c → b

-- ∀ (x y : Nat) (a b c : Prop), (a ∧ x < y) → c → (x ≤ y → b) ===>
-- ∀ (x y : Nat) (a b c : Prop), (a ∧ x < y) → c → b
#testOptimize [ "HypReduction_11" ]
  ∀ (x y : Nat) (a b c : Prop), (a ∧ x < y) → c → (x ≤ y → b) ===>
  ∀ (x y : Nat) (a b c : Prop), (a ∧ x < y) → c → b

-- ∀ (a b c : Prop), (a → b) ∧ (a → c ∧ (a → b)) ===>
-- ∀ (a b c : Prop), (a → b) ∧ (a → b ∧ c)
-- Test case to ensure that reduction is performed only in the right context.
#testOptimize [ "HypReduction_12" ]
  ∀ (a b c : Prop), (a → b) ∧ (a → c ∧ (a → b)) ===>
  ∀ (a b c : Prop), (a → b) ∧ (a → b ∧ c)

-- ∀ (a b c d : Prop), ((a → b) ∧ (a → c ∧ (a → b))) → (a → b ∧ c) → d ===>
-- ∀ (a b c d : Prop), ((a → b) ∧ (a → b ∧ c)) → d
-- Test case to ensure that reduction is performed only in the right context.
#testOptimize [ "HypReduction_13" ]
  ∀ (a b c d : Prop), ((a → b) ∧ (a → c ∧ (a → b))) → (a → b ∧ c) → d ===>
  ∀ (a b c d : Prop), ((a → b) ∧ (a → b ∧ c)) → d

-- ∀ (a b c d : Prop), ((a → b) ∧ (a → c ∧ (a → b))) → (a → b ∧ c) → d ===>
-- ∀ (a b c d : Prop), ((a → b) ∧ (a → b ∧ c)) → d
-- Test case to ensure that reduction is performed only in the right context.
-- TODO INCREMENT NUMBER DOWNWARDS
#testOptimize [ "HypReduction_13" ]
  ∀ (a b c d e : Prop), d → ((a → b) ∧ (a → c ∧ (a → b))) → (a → b ∧ c) → e ===>
  ∀ (a b c d e : Prop), d → ((a → b) ∧ (a → b ∧ c)) → e

-- ∀ (a b c d : Prop), (a → b) → c → (a → b) → d ===>
-- ∀ (a b c d : Prop), (a → b) → c → d
#testOptimize [ "HypReduction_14" ]
  ∀ (a b c d : Prop), (a → b) → c → (a → b) → d ===>
  ∀ (a b c d : Prop), (a → b) → c → d

-- ∀ (a b c : Prop) (x y z : Int) [Decidable c] [Decidable b],
--   (a ∧ c) → b → (if (c ∧ b) then x else y) > z ===>
-- ∀ (a b c : Prop) (y z : Int), (a ∧ c) → b → z < y
#testOptimize [ "HypReduction_15" ]
  ∀ (a b c : Prop) (x y z : Int) [Decidable c] [Decidable b],
    (a ∧ c) → b → (if (c ∧ b) then x else y) > z ===>
  ∀ (a b c : Prop) (y z : Int), (a ∧ c) → b → z < y

-- ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → (a ∧ b ∧ d) → f ===>
-- ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → f
#testOptimize [ "HypReduction_16" ]
  ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → (a ∧ b ∧ d) → f ===>
  ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → f


-- ∀ (a : Prop) (f : a → Prop), a → ∀ (h : a), f h ===>
-- ∀ (a : Prop) (f : a → Prop), ∀ (h : a), f h
#testOptimize [ "HypReduction_17" ]
  ∀ (a : Prop) (f : a → Prop), a → ∀ (h : a), f h ===>
  ∀ (a : Prop) (f : a → Prop), ∀ (h : a), f h

-- ∀ (a c : Prop) (f : a → Prop), (a ∧ c) → ∀ (h : a), f h ===>
-- ∀ (a c : Prop) (f : a → Prop) (h : a ∧ c), f (And.left h)
#testOptimize [ "HypReduction_18" ]
  ∀ (a c : Prop) (f : a → Prop), (a ∧ c) → ∀ (h : a), f h ===>
  ∀ (a c : Prop) (f : a → Prop) (h : a ∧ c), f (And.left h)

-- ∀ (a c : Prop) (f : c → Prop), (a ∧ c) → ∀ (h : c), f h ===>
-- ∀ (a c : Prop) (f : c → Prop) (h : a ∧ c), f (And.right h)
#testOptimize [ "HypReduction_19" ]
  ∀ (a c : Prop) (f : c → Prop), (a ∧ c) → ∀ (h : c), f h ===>
  ∀ (a c : Prop) (f : c → Prop) (h : a ∧ c), f (And.right h)

-- ∀ (a b c : Prop) (f : c → Prop), (a ∧ b ∧ c) → ∀ (h : c), f h ===>
-- ∀ (a b c : Prop) (f : c → Prop) (h : a ∧ b ∧ c), f (And.right (And.right h))
#testOptimize [ "HypReduction_20" ]
  ∀ (a b c : Prop) (f : c → Prop), (a ∧ b ∧ c) → ∀ (h : c), f h ===>
  ∀ (a b c : Prop) (f : c → Prop) (h : a ∧ b ∧ c), f (And.right (And.right h))

-- ∀ (a b c : Prop) (f : a → Prop), (a ∧ c) → b → ∀ (h : a), f h ===>
-- ∀ (a b c : Prop) (f : a → Prop) (h : a ∧ c) (_ : b), f (And.left h)
#testOptimize [ "HypReduction_21" ]
  ∀ (a b c : Prop) (f : a → Prop), (a ∧ c) → b → ∀ (h : a), f h ===>
  ∀ (a b c : Prop) (f : a → Prop) (h : a ∧ c) (_ : b), f (And.left h)

-- ∀ (a b c : Prop) (f : c → Prop), (a ∧ c) → b → ∀ (h : c), f h ===>
-- ∀ (a b c : Prop) (f : c → Prop) (h : a ∧ c) (_ : b), f (And.right h)
#testOptimize [ "HypReduction_22" ]
  ∀ (a b c : Prop) (f : c → Prop), (a ∧ c) → b →  ∀ (h : c), f h ===>
  ∀ (a b c : Prop) (f : c → Prop) (h : a ∧ c) (_ : b), f (And.right h)

-- ∀ (a b c d : Prop) (f : c → Prop), (a ∧ b ∧ c) → d → ∀ (h : c), f h ===>
-- ∀ (a b c d : Prop) (f : c → Prop) (h : a ∧ b ∧ c) (_ : d), f (And.right (And.right h))
#testOptimize [ "HypReduction_23" ]
  ∀ (a b c d : Prop) (f : c → Prop), (a ∧ b ∧ c) → d → ∀ (h : c), f h ===>
  ∀ (a b c d : Prop) (f : c → Prop) (h : a ∧ b ∧ c) (_ : d), f (And.right (And.right h))

-- ∀ (x y : Int) (f : x ≤ y → Prop) (_ : x < y) (h2 : x ≤ y), f h2 ===>
-- ∀ (x y : Int) (f : ¬ (y < x) → Prop) (h : x < y), f (Blaster.int_not_lt_of_lt h)
#testOptimize [ "HypReduction_24" ]
  ∀ (x y : Int) (f : x ≤ y → Prop) (_ : x < y) (h2 : x ≤ y), f h2 ===>
  ∀ (x y : Int) (f : ¬ (y < x) → Prop) (h : x < y), f (Blaster.int_not_lt_of_lt h)

-- ∀ (x y : Int) (f : x ≤ y → Prop) (_ : x = y) (h2 : x ≤ y), f h2 ===>
-- ∀ (x y : Int) (f : ¬ (y < x) → Prop) (h : x = y), f (Blaster.int_not_lt_right_of_eq h)
#testOptimize [ "HypReduction_25" ]
  ∀ (x y : Int) (f : x ≤ y → Prop) (_ : x = y) (h2 : x ≤ y), f h2 ===>
  ∀ (x y : Int) (f : ¬ (y < x) → Prop) (h : x = y), f (Blaster.int_not_lt_right_of_eq h)

-- ∀ (x y : Nat) (f : x ≤ y → Prop) (_ : x < y) (h2 : x ≤ y), f h2 ===>
-- ∀ (x y : Nat) (f : ¬ (y < x) → Prop) (h : x < y), f (Blaster.nat_not_lt_of_lt h)
#testOptimize [ "HypReduction_26" ]
  ∀ (x y : Nat) (f : x ≤ y → Prop) (_ : x < y) (h2 : x ≤ y), f h2 ===>
  ∀ (x y : Nat) (f : ¬ (y < x) → Prop) (h : x < y), f (Blaster.nat_not_lt_of_lt h)

-- ∀ (x y : Nat) (f : x ≤ y → Prop) (_ : x = y) (h2 : x ≤ y), f h2 ===>
-- ∀ (x y : Nat) (f : ¬ (y < x) → Prop) (h : x = y), f (Blaster.nat_not_lt_right_of_eq h)
#testOptimize [ "HypReduction_27" ]
  ∀ (x y : Nat) (f : x ≤ y → Prop) (_ : x = y) (h2 : x ≤ y), f h2 ===>
  ∀ (x y : Nat) (f : ¬ (y < x) → Prop) (h : x = y), f (Blaster.nat_not_lt_right_of_eq h)

-- ∀ (x y : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = y) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y : Int) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x = y) (_ : c),
--   f (Blaster.int_not_lt_right_of_eq (And.right h))
#testOptimize [ "HypReduction_28" ]
  ∀ (x y : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = y) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y : Int) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x = y) (_ : c),
    f (Blaster.int_not_lt_right_of_eq (And.right h))

-- ∀ (x y : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : x < y ∧ a) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y : Int) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x < y) (_ : c),
--   f (Blaster.int_not_lt_of_lt (And.right h))
#testOptimize [ "HypReduction_29" ]
  ∀ (x y : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : x < y ∧ a) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y : Int) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x < y) (_ : c),
    f (Blaster.int_not_lt_of_lt (And.right h))

-- ∀ (x y : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = y) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y : Nat) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x = y) (_ : c),
--   f (Blaster.nat_not_lt_right_of_eq (And.right h))
#testOptimize [ "HypReduction_30" ]
  ∀ (x y : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = y) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y : Nat) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x = y) (_ : c),
    f (Blaster.nat_not_lt_right_of_eq (And.right h))

-- ∀ (x y : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : x < y ∧ a) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y : Nat) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x < y) (_ : c),
--   f (Blaster.nat_not_lt_of_lt (And.right h))
#testOptimize [ "HypReduction_31" ]
  ∀ (x y : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : x < y ∧ a) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y : Nat) (a c : Prop) (f : ¬ y < x → Prop) (h : a ∧ x < y) (_ : c),
    f (Blaster.nat_not_lt_of_lt (And.right h))

-- ∀ (a b c : Prop) (f : a → Prop), (a → b) ∧ (a → c ∧ (∀ (h : a), f h)) ===>
-- ∀ (a b c : Prop) (f : a → Prop), (a → b) ∧ ∀ (h : a), c ∧ f h
-- Test case to ensure that reduction is performed only in the right context.
#testOptimize [ "HypReduction_32" ]
  ∀ (a b c : Prop) (f : a → Prop), (a → b) ∧ (a → c ∧ (∀ (h : a), f h)) ===>
  ∀ (a b c : Prop) (f : a → Prop), (a → b) ∧ ∀ (h : a), c ∧ f h


-- ∀ (a b c : Prop) (x y z : Int) (f : c → Int → Int) [Decidable c],
--   (a ∧ c) → b → (if h : c then f h x else y) > z ===>
-- ∀ (a b c : Prop) (x z : Int) (f : c → Int → Int) (h : a ∧ c) (_ : b),
--   z < f (And.right h) x
#testOptimize [ "HypReduction_33" ]
  ∀ (a b c : Prop) (x y z : Int) (f : c → Int → Int) [Decidable c],
    (a ∧ c) → b → (if h : c then f h x else y) > z ===>
  ∀ (a b c : Prop) (x z : Int) (f : c → Int → Int) (h : a ∧ c) (_ : b),
    z < f (And.right h) x

-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int),
--   (a ∧ c ∧ x < z) → b → (if h : z < x then x else f h y) > z ===>
-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x < z) (_ : b),
--   z < f (Blaster.int_not_lt_of_lt (And.right (And.right h))) y
#testOptimize [ "HypReduction_34" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int),
    (a ∧ c ∧ x < z) → b → (if h : z < x then x else f h y) > z ===>
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x < z) (_ : b),
    z < f (Blaster.int_not_lt_of_lt (And.right (And.right h))) y

-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int),
--   (a ∧ c ∧ x = z) → b → (if h : z < x then x else f h y) > z ===>
-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x = z) (_ : b),
--   z < f (Blaster.int_not_lt_right_of_eq (And.right (And.right h))) y
#testOptimize [ "HypReduction_35" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int),
    (a ∧ c ∧ x = z) → b → (if h : z < x then x else f h y) > z ===>
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x = z) (_ : b),
    z < f (Blaster.int_not_lt_right_of_eq (And.right (And.right h))) y


--  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable a], (a ∧ c ∧ x < z) → b →
--    (if h : z < x then x else f h y) > z →
--    (if h : a ∨ z < x then x else f (And.right (Blaster.and_not_from_not_or h)) y) > z ===>
-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x < z) ( _ : b),
--   ¬ z < f (Blaster.int_not_lt_of_lt (And.right (And.right h))) y
#testOptimize [ "HypReduction_36" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable a], (a ∧ c ∧ x < z) → b →
    (if h : z < x then x else f h y) > z →
    (if h : a ∨ z < x then x else f (And.right (Blaster.and_not_from_not_or h)) y) > z ===>
 ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) (h : a ∧ c ∧ x < z) ( _ : b),
   ¬ z < f (Blaster.int_not_lt_of_lt (And.right (And.right h))) y

-- ∀ (a b c : Prop) (f : a ∧ c → Prop), (a ∧ b ∧ c) → ∀ (h : a ∧ c), f h ===>
-- ∀ (a b c : Prop) (f : a ∧ c → Prop) (h : a ∧ b ∧ c),
--   f (And.intro (And.left h) (And.right (And.right h)))
-- Test case considering proof reconstruction when referenced hyp resolves to True
#testOptimize [ "HypReduction_37" ]
  ∀ (a b c : Prop) (f : a ∧ c → Prop), (a ∧ b ∧ c) → ∀ (h : a ∧ c), f h ===>
  ∀ (a b c : Prop) (f : a ∧ c → Prop) (h : a ∧ b ∧ c),
    f (And.intro (And.left h) (And.right (And.right h)))

-- ∀ (a b c : Prop) (f : a ∧ c → Prop), a → (b ∧ c) → ∀ (h : a ∧ c), f h ===>
-- ∀ (a b c : Prop) (f : a ∧ c → Prop) (h1 : a) (h2 : b ∧ c), f (And.intro h1 (And.right h2))
-- Test cases considering proof reconstruction when referenced hyp resolves to True
-- and proof depends on multiple premises.
#testOptimize [ "HypReduction_38" ]
  ∀ (a b c : Prop) (f : a ∧ c → Prop), a → (b ∧ c) → ∀ (h : a ∧ c), f h ===>
  ∀ (a b c : Prop) (f : a ∧ c → Prop) (h1 : a) (h2 : b ∧ c), f (And.intro h1 (And.right h2))

-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (q ∧ d) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ (q ∧ d)), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (d ∧ q) → Prop)
--   (h1 : a ∧ e) (_ : b) (h2 : c ∧ d) (h3 : p ∧ q),
--     f (And.intro (And.intro (And.left h1) (And.left h3)) (And.intro (And.right h2) (And.right h3)))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_39" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (q ∧ d) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ (q ∧ d)), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (d ∧ q) → Prop)
    (h1 : a ∧ e) (_ : b) (h2 : c ∧ d) (h3 : p ∧ q),
      f (And.intro (And.intro (And.left h1) (And.left h3)) (And.intro (And.right h2) (And.right h3)))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d)), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ p)) ∧ (d ∧ (c ∧ q)) → Prop)
--   (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
--    f (And.intro
--      (And.intro (And.left h1) (And.intro h2 (And.left h4)))
--      (And.intro (And.right h3) (And.intro (And.left h3) (And.right h4))))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_40" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d)), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ p)) ∧ (d ∧ (c ∧ q)) → Prop)
    (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
     f (And.intro
       (And.intro (And.left h1) (And.intro h2 (And.left h4)))
       (And.intro (And.right h3) (And.intro (And.left h3) (And.right h4))))

-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ d)), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ p)) ∧ (d ∧ (c ∧ q)) → Prop)
--   (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
--    f (And.intro
--      (And.intro (And.left h1) (And.intro h2 (And.left h4)))
--      (And.intro (And.right h3) (And.intro (And.left h3) (And.right h4))))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_41" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ (d ∧ b)) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ b)) ∧ ((q ∧ c) ∧ (d ∧ b))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ p)) ∧ ((b ∧ d) ∧ (c ∧ q)) → Prop)
    (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
     f (And.intro
       (And.intro (And.left h1) (And.intro h2 (And.left h4)))
       (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h4))))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (e ∧ c))) ∧ ((q ∧ c) ∧ (d ∧ b)) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ (e ∧ c))) ∧ ((q ∧ c) ∧ (d ∧ b))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (c ∧ e))) ∧ ((b ∧ d) ∧ (c ∧ q)) → Prop)
--   (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
--    f (And.intro
--      (And.intro (And.left h1) (And.intro (And.left h4) (And.intro (And.left h3) (And.right h1))))
--      (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h4))))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_42" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (e ∧ c))) ∧ ((q ∧ c) ∧ (d ∧ b)) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ (p ∧ (e ∧ c))) ∧ ((q ∧ c) ∧ (d ∧ b))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (c ∧ e))) ∧ ((b ∧ d) ∧ (c ∧ q)) → Prop)
    (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
     f (And.intro
       (And.intro (And.left h1) (And.intro (And.left h4) (And.intro (And.left h3) (And.right h1))))
       (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h4))))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∧ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c))) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ ((q ∧ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c)))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∧ (c ∧ (d ∧ e))) ∧ ((b ∧ d) ∧ (c ∧ e))) → Prop)
--   (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
--   f (And.intro
--      (And.intro (And.left h1) (And.left h4))
--      (And.intro
--       (And.intro (And.right h4) (And.intro (And.left h3) (And.intro (And.right h3) (And.right h1))))
--       (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h1)))))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_43" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∧ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c))) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ ((q ∧ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c)))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∧ (c ∧ (d ∧ e))) ∧ ((b ∧ d) ∧ (c ∧ e))) → Prop)
    (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p ∧ q),
    f (And.intro
       (And.intro (And.left h1) (And.left h4))
       (And.intro
        (And.intro (And.right h4) (And.intro (And.left h3) (And.intro (And.right h3) (And.right h1))))
        (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h1)))))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q)))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
--   (h1 : e ∧ q) (h3 : c ∧ d) (h4 : (a ∧ b) ∧ (b ∧ p)),
--   f (And.intro
--      (And.intro (And.left (And.left h4)) (And.intro (And.right (And.left h4)) h3))
--      (And.intro (And.right (And.right h4)) (And.intro (And.left h1) (And.intro (And.left (And.right h4)) (And.right h1)))))
-- Test cases considering proof reconstruction based on multiple premises.
#testOptimize [ "HypReduction_44" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q)))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
    (h1 : e ∧ q) (h3 : c ∧ d) (h4 : (a ∧ b) ∧ (b ∧ p)),
    f (And.intro
       (And.intro (And.left (And.left h4)) (And.intro (And.left (And.right h4)) h3))
       (And.intro (And.right (And.right h4)) (And.intro (And.left h1) (And.intro (And.left (And.right h4)) (And.right h1)))))

-- ∀ (a b e p q : Prop) (f : (a ∧ (b ∧ True)) ∧ (p ∧ (True ∧ (b ∧ q))) → Prop)
--   (_ : q ∧ e) (h : (a ∧ (b ∧ True)) ∧ (p ∧ (True ∧ (b ∧ q)))), f h ===>
-- ∀ (a b e p q : Prop) (f : (a ∧ b) ∧ (p ∧ (b ∧ q)) → Prop)
--   (h1 : e ∧ q) (h4 : (a ∧ b) ∧ (b ∧ p)),
--   f (And.intro (And.left h4)
--     (And.intro (And.right (And.right h4)) (And.intro (And.left (And.right h4)) (And.right h1))))
-- Test cases considering proof reconstruction when True appears in original hypothesis
#testOptimize [ "HypReduction_45" ]
  ∀ (a b e p q : Prop) (f : (a ∧ (b ∧ True)) ∧ (p ∧ (True ∧ (b ∧ q))) → Prop)
    (_ : q ∧ e) (h : (a ∧ (b ∧ True)) ∧ (p ∧ (True ∧ (b ∧ q)))), f h ===>
  ∀ (a b e p q : Prop) (f : (a ∧ b) ∧ (p ∧ (b ∧ q)) → Prop)
    (h1 : e ∧ q) (h4 : (a ∧ b) ∧ (b ∧ p)),
    f (And.intro (And.left h4)
      (And.intro (And.right (And.right h4)) (And.intro (And.left (And.right h4)) (And.right h1))))


-- ∀ (a b c d e p q : Prop) (f : ((a ∧ d) ∧ (b ∧ (c ∧ a))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
--   (_ : b ∧ e) (_ : c ∧ d) (h : ((a ∧ d) ∧ (b ∧ (c ∧ a))) ∧ (p ∧ (e ∧ (b ∧ q)))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (p ∧ (e ∧ (b ∧ q))) ∧ ((a ∧ d) ∧ (b ∧ (a ∧ c))) → Prop)
--   (h1 : b ∧ e) (h3 : c ∧ d) (h4 : a ∧ (p ∧ q)),
--   f (And.intro
--      (And.intro (And.left (And.right h4))
--        (And.intro (And.right h1) (And.intro (And.left h1) (And.right (And.right h4)))))
--      (And.intro (And.intro (And.left h4) (And.right h3))
--       (And.intro (And.left h1) (And.intro (And.left h4) (And.left h3)))))
-- Test cases considering proof reconstruction for And absorption rule.
#testOptimize [ "HypReduction_46" ]
  ∀ (a b c d e p q : Prop) (f : ((a ∧ d) ∧ (b ∧ (c ∧ a))) ∧ (p ∧ (e ∧ (b ∧ q))) → Prop)
    (_ : b ∧ e) (_ : c ∧ d) (h : ((a ∧ d) ∧ (b ∧ (c ∧ a))) ∧ (p ∧ (e ∧ (b ∧ q)))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (p ∧ (e ∧ (b ∧ q))) ∧ ((a ∧ d) ∧ (b ∧ (a ∧ c))) → Prop)
    (h1 : b ∧ e) (h3 : c ∧ d) (h4 : a ∧ (p ∧ q)),
    f (And.intro
       (And.intro (And.left (And.right h4))
         (And.intro (And.right h1) (And.intro (And.left h1) (And.right (And.right h4)))))
       (And.intro (And.intro (And.left h4) (And.right h3))
        (And.intro (And.left h1) (And.intro (And.left h4) (And.left h3)))))

--  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (_ : (a → b) ∧ (a → c ∧ (a → b))) (h : a → b ∧ c), f h ===>
--  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (h : (a → b) ∧ (a → b ∧ c)), f (And.right h)
-- Test case to ensure that reduction is performed only in the right context.
#testOptimize [ "HypReduction_47" ]
  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (_ : (a → b) ∧ (a → c ∧ (a → b))) (h : a → b ∧ c), f h ===>
  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (h : (a → b) ∧ (a → b ∧ c)), f (And.right h)

-- ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (_ : (a → b) ∧ (a → c ∧ (a → b))) (h : a → b ∧ c), f h ===>
-- ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (h : (a → b) ∧ (a → b ∧ c)), f (And.right h)
-- Test case to ensure that reduction is performed only in the right context.
#testOptimize [ "HypReduction_48" ]
  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (_ : (a → b) ∧ (a → c ∧ (a → b))) (h : a → b ∧ c), f h ===>
  ∀ (a b c : Prop) (f : (a → b ∧ c) → Prop) (h : (a → b) ∧ (a → b ∧ c)), f (And.right h)

-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable a], (a ∧ c ∧ x < z) → b →
--   (if h : z < x then x else f h y) > z →
--   (if h : a ∧ ¬ z < x then f (And.right h) y else x) > z ===> True
#testOptimize [ "HypReduction_49" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable a], (a ∧ c ∧ x < z) → b →
    (if h : z < x then x else f h y) > z →
    (if h : a ∧ ¬ z < x then f (And.right h) y else x) > z ===> True

-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable c], (a ∧ c ∧ x < z) → b →
--   (if h : z < x then x else f h y) > z →
--   (if h : (¬ c) ∨ z < x then x else f (And.right (Blaster.and_not_from_not_or h)) y) > z ===> True
#testOptimize [ "HypReduction_50" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < x) → Int → Int) [Decidable c], (a ∧ c ∧ x < z) → b →
    (if h : z < x then x else f h y) > z →
    (if h : (¬ c) ∨ z < x then x else f (And.right (Blaster.and_not_from_not_or h)) y) > z ===> True

-- ∀ (a b c : Prop) (x y z : Int) (f : x < z → Int → Int) [Decidable c], (a ∧ c ∧ x < z) → b →
--   (if h : x < z then f h y else x) > z →
--   (if h : c ∧ x < z then f (And.right h) y else x) > z ===> True
#testOptimize [ "HypReduction_51" ]
  ∀ (a b c : Prop) (x y z : Int) (f : x < z → Int → Int) [Decidable c], (a ∧ c ∧ x < z) → b →
    (if h : x < z then f h y else x) > z →
    (if h : c ∧ x < z then f (And.right h) y else x) > z ===> True

-- ∀ (a b c d : Prop), (a → b) → c → (a → b) → d ===>
-- ∀ (a b c d : Prop), (a → b) → c → d
#testOptimize [ "HypReduction_52" ]
  ∀ (a b c d : Prop), (a → b) → c → (a → b) → d ===>
  ∀ (a b c d : Prop), (a → b) → c → d

-- ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → (a ∧ b ∧ d) → f ===>
-- ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → f
#testOptimize [ "HypReduction_53" ]
  ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → (a ∧ b ∧ d) → f ===>
  ∀ (a b c d e f : Prop), (a ∧ e) → b → (c ∧ d) → f

-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (e ∨ c))) ∧ ((q ∨ c) ∧ (d ∧ b)) → Prop)
--   (_ : a ∧ d) (_ : c ∧ b) (h : (a ∧ (p ∧ (e ∨ c))) ∧ ((q ∨ c) ∧ (d ∧ b))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (c ∨ e))) ∧ ((b ∧ d) ∧ (c ∨ q)) → Prop)
--   (h1 : a ∧ d) (h2 : b ∧ c) (h3 : p),
--    f (And.intro
--       (And.intro (And.left h1) (And.intro h3 (Or.inl (And.right h2))))
--       (And.intro (And.intro (And.left h2) (And.right h1)) (Or.inl (And.right h2))))
-- Test cases mixing proof reconstuction for conjunction and disjunction based on multiple premises.
#testOptimize [ "HypReduction_54" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (e ∨ c))) ∧ ((q ∨ c) ∧ (d ∧ b)) → Prop)
    (_ : a ∧ d) (_ : c ∧ b) (h : (a ∧ (p ∧ (e ∨ c))) ∧ ((q ∨ c) ∧ (d ∧ b))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (p ∧ (c ∨ e))) ∧ ((b ∧ d) ∧ (c ∨ q)) → Prop)
    (h1 : a ∧ d) (h2 : b ∧ c) (h3 : p),
     f (And.intro
        (And.intro (And.left h1) (And.intro h3 (Or.inl (And.right h2))))
        (And.intro (And.intro (And.left h2) (And.right h1)) (Or.inl (And.right h2))))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∨ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c))) → Prop)
--   (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ ((q ∨ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c)))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (((b ∧ d) ∧ (c ∧ e)) ∧ (q ∨ (c ∧ (d ∧ e)))) → Prop)
--   (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p),
--   f (And.intro
--      (And.intro (And.left h1) h4)
--      (And.intro
--       (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h1)))
--       (Or.inr (And.intro (And.left h3) (And.intro (And.right h3) (And.right h1))))))
-- Test cases mixing proof reconstuction for conjunction and disjunction based on multiple premises.
#testOptimize [ "HypReduction_55" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ ((q ∨ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c))) → Prop)
    (_ : a ∧ e) (_ : b) (_ : c ∧ d) (h : (a ∧ p) ∧ ((q ∨ (c ∧ (e ∧ d))) ∧ ((d ∧ b) ∧ (e ∧ c)))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ p) ∧ (((b ∧ d) ∧ (c ∧ e)) ∧ (q ∨ (c ∧ (d ∧ e)))) → Prop)
    (h1 : a ∧ e) (h2 : b) (h3 : c ∧ d) (h4 : p),
    f (And.intro
       (And.intro (And.left h1) h4)
       (And.intro
        (And.intro (And.intro h2 (And.right h3)) (And.intro (And.left h3) (And.right h1)))
        (Or.inr (And.intro (And.left h3) (And.intro (And.right h3) (And.right h1))))))


-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q)))), f h ===>
-- ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q))) → Prop)
--   (h1 : e ∧ q) (h3 : c ∧ d) (h4 : a ∧ b),
--   f (And.intro
--      (And.intro (And.left h4) (And.intro (And.right h4) h3))
--      (Or.inr (And.intro (And.left h1) (Or.inl (And.right h4)))))
-- Test cases mixing proof reconstuction for conjunction and disjunction based on multiple premises.
#testOptimize [ "HypReduction_56" ]
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q)))), f h ===>
  ∀ (a b c d e p q : Prop) (f : (a ∧ (b ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (b ∨ q))) → Prop)
    (h1 : e ∧ q) (h2 : c ∧ d) (h3 : a ∧ b),
    f (And.intro
       (And.intro (And.left h3) (And.intro (And.right h3) h2))
       (Or.inr (And.intro (And.left h1) (Or.inl (And.right h3)))))

-- ∀ (a c d e p q : Prop) (x : Nat) (f : (y : Nat) → (a ∧ (y = 2 ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (y = 2 ∨ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (x = 2 ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x = 2 ∨ q)))), f x h ===>
-- ∀ (a c d e p q : Prop) (x : Nat) (f : (y : Nat) → (a ∧ ((c ∧ d) ∧ 2 = y)) ∧ (p ∨ (e ∧ (q ∨ 2 = y))) → Prop)
--   (h1 : e ∧ q) (h2 : c ∧ d) (h3 : a ∧ 2 = x),
--   f 2 (And.intro
--        (And.intro (And.left h3) (And.intro h2 (by rfl)))
--        (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))
-- Test cases mixing proof reconstuction for conjunction and disjunction based on multiple premises.
#testOptimize [ "HypReduction_57" ] (norm-result: 1)
  ∀ (a c d e p q : Prop) (x : Nat) (f : (y : Nat) → (a ∧ (y = 2 ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (y = 2 ∨ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (h : (a ∧ (x = 2 ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x = 2 ∨ q)))), f x h ===>
  ∀ (a c d e p q : Prop) (x : Nat) (f : (y : Nat) → (a ∧ ((c ∧ d) ∧ 2 = y)) ∧ (p ∨ (e ∧ (q ∨ 2 = y))) → Prop)
    (h1 : e ∧ q) (h2 : c ∧ d) (h3 : a ∧ 2 = x),
    f 2 (And.intro
         (And.intro (And.left h3) (And.intro h2 (by rfl)))
         (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))

-- ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
--   (_ : x = 5 ∧ y = 10) (h : x < y), f x y h → f 5 10 (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Int
#testOptimize [ "HypReduction_58" ]
  ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
    (_ : x = 5 ∧ y = 10) (h : x < y), f x y h → f 5 10 (of_decide_eq_true rfl) ===> True

-- ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
--   (_ : x = 5 ∧ y = 10) (h : x < y), f x y h ===>
-- ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
--   (_ : 5 = x ∧ 10 = y), f 5 10 (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Int
#testOptimize [ "HypReduction_59" ] (norm-result: 1)
  ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
    (_ : x = 5 ∧ y = 10) (h : x < y), f x y h ===>
  ∀ (x y : Int) (f : (x : Int) → (y : Int) → x < y → Prop)
    (_ : 5 = x ∧ 10 = y), f 5 10 (of_decide_eq_true rfl)

-- ∀ (a c d e p q : Prop) (x y : Int) (f : (x : Int) → (y : Int) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (_ : x = 5 ∧ y = 10) (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
-- ∀ (a c d e p q : Prop) (x y : Int) (f : (x : Int) → (y : Int) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
--   (h1 : e ∧ q) (h2 : c ∧ d) (_ : 5 = x ∧ 10 = y) (h4 : a),
--   f 5 10 (And.intro
--          (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
--          (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Int
#testOptimize [ "HypReduction_60" ] (norm-result: 1)
  ∀ (a c d e p q : Prop) (x y : Int) (f : (x : Int) → (y : Int) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (_ : x = 5 ∧ y = 10) (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
  ∀ (a c d e p q : Prop) (x y : Int) (f : (x : Int) → (y : Int) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
    (h1 : e ∧ q) (h2 : c ∧ d) (_ : 5 = x ∧ 10 = y) (h4 : a),
    f 5 10 (And.intro
            (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
            (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))


-- ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
--   (_ : x = 5 ∧ y = 10) (h : x < y), f x y h → f 5 10 (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Nat
#testOptimize [ "HypReduction_61" ]
  ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
    (_ : x = 5 ∧ y = 10) (h : x < y), f x y h → f 5 10 (of_decide_eq_true rfl) ===> True

-- ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
--   (_ : x = 5 ∧ y = 10) (h : x < y), f x y h ===>
-- ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
--   (_ : 5 = x ∧ 10 = y), f 5 10 (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Nat
#testOptimize [ "HypReduction_62" ] (norm-result: 1)
  ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
    (_ : x = 5 ∧ y = 10) (h : x < y), f x y h ===>
  ∀ (x y : Nat) (f : (x : Nat) → (y : Nat) → x < y → Prop)
    (_ : 5 = x ∧ 10 = y), f 5 10 (of_decide_eq_true rfl)

-- ∀ (a c d e p q : Prop) (x y : Nat) (f : (x : Nat) → (y : Nat) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (_ : x = 5 ∧ y = 10) (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
-- ∀ (a c d e p q : Prop) (x y : Nat) (f : (x : Nat) → (y : Nat) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
--   (h1 : e ∧ q) (h2 : c ∧ d) (_ : 5 = x ∧ 10 = y) (h4 : a),
--   f 5 10 (And.intro
--          (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
--          (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on Nat
#testOptimize [ "HypReduction_63" ] (norm-result: 1)
  ∀ (a c d e p q : Prop) (x y : Nat) (f : (x : Nat) → (y : Nat) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (_ : x = 5 ∧ y = 10) (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
  ∀ (a c d e p q : Prop) (x y : Nat) (f : (x : Nat) → (y : Nat) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
    (h1 : e ∧ q) (h2 : c ∧ d) (_ : 5 = x ∧ 10 = y) (h4 : a),
    f 5 10 (And.intro
            (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
            (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))


-- ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
--   (_ : x = "aa" ∧ y = "bb") (h : x < y), f x y h → f "aa" "bb" (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on String
#testOptimize [ "HypReduction_63" ]
  ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
    (_ : x = "aa" ∧ y = "bb") (h : x < y), f x y h → f "aa" "bb" (of_decide_eq_true rfl) ===> True

-- ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
--   (_ : x = "aa" ∧ y = "bb") (h : x < y), f x y h ===>
-- ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
--   (_ : "aa" = x ∧ "bb" = y), f "aa" "bb" (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on String
#testOptimize [ "HypReduction_64" ]
  ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
    (_ : x = "aa" ∧ y = "bb") (h : x < y), f x y h ===>
  ∀ (x y : String) (f : (x : String) → (y : String) → x < y → Prop)
    (_ : "aa" = x ∧ "bb" = y), f "aa" "bb" (of_decide_eq_true rfl)

-- ∀ (a c d e p q : Prop) (x y : String) (f : (x : String) → (y : String) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
--   (_ : q ∧ e) (_ : c ∧ d) (_ : x = "aa" ∧ y = "bb") (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
-- ∀ (a c d e p q : Prop) (x y : String) (f : (x : String) → (y : String) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
--   (h1 : e ∧ q) (h2 : c ∧ d) (_ : "aa" = x ∧ "bb" = y) (h4 : a),
--   f 5 10 (And.intro
--           (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
--           (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LT.lt on String
#testOptimize [ "HypReduction_65" ]
  ∀ (a c d e p q : Prop) (x y : String) (f : (x : String) → (y : String) → (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q))) → Prop)
    (_ : q ∧ e) (_ : c ∧ d) (_ : x = "aa" ∧ y = "bb") (h : (a ∧ (x < y ∧ (c ∧ d))) ∧ (p ∨ (e ∧ (x < y ∨ q)))), f x y h ===>
  ∀ (a c d e p q : Prop) (x y : String) (f : (x : String) → (y : String) → (a ∧ ((c ∧ d) ∧ x < y)) ∧ (p ∨ (e ∧ (q ∨ x < y))) → Prop)
    (h1 : e ∧ q) (h2 : c ∧ d) (_ : "aa" = x ∧ "bb" = y) (h4 : a),
    f "aa" "bb" (And.intro
                 (And.intro h4 (And.intro h2 (of_decide_eq_true rfl)))
                 (Or.inr (And.intro (And.left h1) (Or.inl (And.right h1)))))

def elemNatSize (xs : List Nat) (x y : Nat) (h : x ≤ y) : Nat :=
  match xs with
  | [] => y - x
  | a :: xs' => a + y + elemNatSize xs' x y h

-- ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y) (h : x ≤ y),
--   z < elemNatSize xs x y h → z < elemNatSize xs 5 10 (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on Nat
#testOptimize [ "HypReduction_66" ]
  ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y) (h : x ≤ y),
    z < elemNatSize xs x y h → z < elemNatSize xs 5 10 (of_decide_eq_true rfl) ===> True

-- ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y) (h : x ≤ y), z < elemNatSize xs x y h ===>
-- ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y), z < elemNatSize xs 5 10 (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on Nat
#testOptimize [ "HypReduction_67" ] (norm-result: 1)
  ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y) (h : x ≤ y), z < elemNatSize xs x y h ===>
  ∀ (x y z : Nat) (xs : List Nat) (_ : 5 = x ∧ 10 = y), z < elemNatSize xs 5 10 (of_decide_eq_true rfl)


def elemIntSize (xs : List Int) (x y : Int) (h : x ≤ y) : Int :=
  match xs with
  | [] => y - x
  | a :: xs' => a + y + elemIntSize xs' x y h

-- ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y) (h : x ≤ y),
--   z < elemIntSize xs x y h → z < elemIntSize xs 5 10 (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on Int
#testOptimize [ "HypReduction_68" ]
  ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y) (h : x ≤ y),
    z < elemIntSize xs x y h → z < elemIntSize xs 5 10 (of_decide_eq_true rfl) ===> True

-- ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y) (h : x ≤ y), z < elemIntSize xs x y h ===>
-- ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y), z < elemIntSize xs 5 10 (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on Int
#testOptimize [ "HypReduction_69" ] (norm-result: 1)
  ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y) (h : x ≤ y), z < elemIntSize xs x y h ===>
  ∀ (x y z : Int) (xs : List Int) (_ : 5 = x ∧ 10 = y), z < elemIntSize xs 5 10 (of_decide_eq_true rfl)

def elemStringSize (xs : List String) (x y : String) (h : x ≤ y) : Nat :=
  match xs with
  | [] => y.length - x.length
  | a :: xs' => (a ++ y).length + elemStringSize xs' x y h

-- ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y) (h : x ≤ y),
--   z < elemStringSize xs x y h → z < elemStringSize xs "aa" "bb" (of_decide_eq_true rfl) ===> True
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on String
#testOptimize [ "HypReduction_70" ]
  ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y) (h : x ≤ y),
    z < elemStringSize xs x y h → z < elemStringSize xs "aa" "bb" (of_decide_eq_true rfl) ===> True

-- ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y) (h : x ≤ y), z < elemStringSize xs x y h ===>
-- ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y), z < elemStringSize xs "aa" "bb" (of_decide_eq_true rfl)
-- Test cases mixing proof reconstuction on multiple premises with constant propagation for LE.le on String
#testOptimize [ "HypReduction_71" ] (norm-result: 1)
  ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y) (h : x ≤ y), z < elemStringSize xs x y h ===>
  ∀ (x y : String) (z : Nat) (xs : List String) (_ : "aa" = x ∧ "bb" = y), z < elemStringSize xs "aa" "bb" (of_decide_eq_true rfl)


/-! Test cases to ensure that the rules are not wrongly applied. -/

-- ∀ (a b c : Prop), a → (c → b) ===>
-- ∀ (a b c : Prop), a → (c → b)
#testOptimize [ "HypReductionUnchanged_1" ]
  ∀ (a b c : Prop), a → (c → b) ===>
  ∀ (a b c : Prop), a → (c → b)

-- ∀ (a b c d : Prop), (a ∧ c) → (d → b) ===>
-- ∀ (a b c d : Prop), (a ∧ c) → (d → b)
#testOptimize [ "HypReductionUnchanged_2" ]
  ∀ (a b c d : Prop), (a ∧ c) → (d → b) ===>
  ∀ (a b c d : Prop), (a ∧ c) → (d → b)

-- ∀ (x y z : Int) (b : Prop), x = z → (x ≤ y → b) ===>
-- ∀ (x y z : Int) (b : Prop), x = z → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_3" ]
  ∀ (x y z : Int) (b : Prop), x = z → (x ≤ y → b) ===>
  ∀ (x y z : Int) (b : Prop), x = z → (¬ (y < x) → b)

-- ∀ (x y z : Int) (b : Prop), x < z → (x ≤ y → b) ===>
-- ∀ (x y z : Int) (b : Prop), x < z → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_4" ]
  ∀ (x y z : Int) (b : Prop), x < z → (x ≤ y → b) ===>
  ∀ (x y z : Int) (b : Prop), x < z → (¬ (y < x) → b)


-- ∀ (x y z : Nat) (b : Prop), x = z → (x ≤ y → b) ===>
-- ∀ (x y z : Nat) (b : Prop), x = z → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_5" ]
  ∀ (x y z : Nat) (b : Prop), x = z → (x ≤ y → b) ===>
  ∀ (x y z : Nat) (b : Prop), x = z → (¬ (y < x) → b)

-- ∀ (x y z : Nat) (b : Prop), x < z → (x ≤ y → b) ===>
-- ∀ (x y z : Nat) (b : Prop), x < z → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_6" ]
  ∀ (x y z : Nat) (b : Prop), x < z → (x ≤ y → b) ===>
  ∀ (x y z : Nat) (b : Prop), x < z → (¬ (y < x) → b)

-- ∀ (x y z : Int) (a b c : Prop), (a ∧ x = z) → c → (x ≤ y → b) ===>
-- ∀ (x y z : Int) (a b c : Prop), (a ∧ x = z) → c → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_7" ]
  ∀ (x y z : Int) (a b c : Prop), (a ∧ x = z) → c → (x ≤ y → b) ===>
  ∀ (x y z : Int) (a b c : Prop), (a ∧ x = z) → c → (¬ (y < x) → b)

-- ∀ (x y z : Int) (a b c : Prop), (x < z ∧ a) → c → (x ≤ y → b) ===>
-- ∀ (x y z : Int) (a b c : Prop), (a ∧ x < z) → c → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_8" ]
  ∀ (x y z : Int) (a b c : Prop), (x < z ∧ a) → c → (x ≤ y → b) ===>
  ∀ (x y z : Int) (a b c : Prop), (a ∧ x < z) → c → (¬ (y < x) → b)

-- ∀ (x y z : Nat) (a b c : Prop), (a ∧ x = z) → c → (x ≤ y → b) ===>
-- ∀ (x y z : Nat) (a b c : Prop), (a ∧ x = z) → c → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_9" ]
  ∀ (x y z : Nat) (a b c : Prop), (a ∧ x = z) → c → (x ≤ y → b) ===>
  ∀ (x y z : Nat) (a b c : Prop), (a ∧ x = z) → c → (¬ (y < x) → b)

-- ∀ (x y z : Nat) (a b c : Prop), (x < z ∧ a) → c → (x ≤ y → b) ===>
-- ∀ (x y z : Nat) (a b c : Prop), (a ∧ x < z) → c → (¬ (y < x) → b)
#testOptimize [ "HypReductionUnchanged_10" ]
  ∀ (x y z : Nat) (a b c : Prop), (x < z ∧ a) → c → (x ≤ y → b) ===>
  ∀ (x y z : Nat) (a b c : Prop), (a ∧ x < z) → c → (¬ (y < x) → b)

-- ∀ (a b c d : Prop), (a → b) → c → (b → d) → d ===>
-- ∀ (a b c d : Prop), (a → b) → c → (b → d) → d
#testOptimize [ "HypReductionUnchanged_11" ]
  ∀ (a b c d : Prop), (a → b) → c → (b → d) → d ===>
  ∀ (a b c d : Prop), (a → b) → c → (b → d) → d

-- ∀ (a b c d : Prop) (x y z : Int) [Decidable d] [Decidable b],
--   (a ∧ c) → b → (if (d ∧ b) then x else y) > z ===>
-- ∀ (a b c d : Prop) (x y z : Int), (a ∧ c) → b →
--   z < Blaster.dite' d (fun _ => x) (fun _ => y)
#testOptimize [ "HypReductionUnchanged_12" ]
  ∀ (a b c d : Prop) (x y z : Int) [Decidable d] [Decidable b],
    (a ∧ c) → b → (if (d ∧ b) then x else y) > z ===>
  ∀ (a b c d : Prop) (x y z : Int), (a ∧ c) → b →
    z < Blaster.dite' d (fun _ => x) (fun _ => y)

-- ∀ (a b : Prop) (f : b → Prop) (_ : a) (h : b), f h ===>
-- ∀ (a b : Prop) (f : b → Prop) (_ : a) (h : b), f h
#testOptimize [ "HypReductionUnchanged_13" ]
  ∀ (a b : Prop) (f : b → Prop) (_ : a) (h : b), f h ===>
  ∀ (a b : Prop) (f : b → Prop) (_ : a) (h : b), f h

-- ∀ (a c b : Prop) (f : b → Prop) (_ : a ∧ c) (h : b), f h ===>
-- ∀ (a c b : Prop) (f : b → Prop) (_ : a ∧ c) (h : b), f h
#testOptimize [ "HypReductionUnchanged_14" ]
  ∀ (a c b : Prop) (f : b → Prop) (_ : a ∧ c) (h : b), f h ===>
  ∀ (a c b : Prop) (f : b → Prop) (_ : a ∧ c) (h : b), f h

-- ∀ (x y z : Int) (f : x ≤ y → Prop) (_ : x < z) (h : x ≤ y), f h ===>
-- ∀ (x y z : Int) (f : ¬ (y < x) → Prop) (_ : x < z) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_15" ]
  ∀ (x y z : Int) (f : x ≤ y → Prop) (_ : x < z) (h : x ≤ y), f h ===>
  ∀ (x y z : Int) (f : ¬ (y < x) → Prop) (_ : x < z) (h : ¬ y < x), f h

-- ∀ (x y z : Int) (f : x ≤ y → Prop) (_ : x = z) (h : x ≤ y), f h ===>
-- ∀ (x y z : Int) (f : ¬ (y < x) → Prop) (_ : x = z) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_16" ]
  ∀ (x y z : Int) (f : x ≤ y → Prop) (_ : x = z) (h : x ≤ y), f h ===>
  ∀ (x y z : Int) (f : ¬ (y < x) → Prop) (_ : x = z) (h : ¬ y < x), f h

-- ∀ (x y z : Nat) (f : x ≤ y → Prop) (_ : x < z) (h : x ≤ y), f h ===>
-- ∀ (x y z : Nat) (f : ¬ (y < x) → Prop) (_ : x < z) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_15" ]
  ∀ (x y z : Nat) (f : x ≤ y → Prop) (_ : x < z) (h : x ≤ y), f h ===>
  ∀ (x y z : Nat) (f : ¬ (y < x) → Prop) (_ : x < z) (h : ¬ y < x), f h

-- ∀ (x y z : Nat) (f : x ≤ y → Prop) (_ : x = z) (h : x ≤ y), f h ===>
-- ∀ (x y z : Nat) (f : ¬ (y < x) → Prop) (_ : x = z) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_16" ]
  ∀ (x y z : Nat) (f : x ≤ y → Prop) (_ : x = z) (h : x ≤ y), f h ===>
  ∀ (x y z : Nat) (f : ¬ (y < x) → Prop) (_ : x = z) (h : ¬ y < x), f h

-- ∀ (x y z : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = z) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y z : Int) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x = z) (_ : c) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_17" ]
  ∀ (x y z : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = z) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y z : Int) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x = z) (_ : c) (h : ¬ y < x), f h

-- ∀ (x y z : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : x < z ∧ a) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y z : Int) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x < z) (_ : c) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_18" ]
  ∀ (x y z : Int) (a c : Prop) (f : x ≤ y → Prop) (_ : x < z ∧ a) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y z : Int) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x < z) (_ : c) (h : ¬ y < x), f h

-- ∀ (x y z : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = z) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y z : Nat) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x = z) (_ : c) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_19" ]
  ∀ (x y z : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : a ∧ x = z) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y z : Nat) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x = z) (_ : c) (h : ¬ y < x), f h

-- ∀ (x y z : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : x < z ∧ a) (_ : c) (h : x ≤ y), f h ===>
-- ∀ (x y z : Nat) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x < z) (_ : c) (h : ¬ y < x), f h
#testOptimize [ "HypReductionUnchanged_20" ]
  ∀ (x y z : Nat) (a c : Prop) (f : x ≤ y → Prop) (_ : x < z ∧ a) (_ : c) (h : x ≤ y), f h ===>
  ∀ (x y z : Nat) (a c : Prop) (f : ¬ y < x → Prop) (_ : a ∧ x < z) (_ : c) (h : ¬ y < x), f h


-- ∀ (a b c d : Prop) (x y z : Int) (f : d → Int → Int) [Decidable d],
--   (a ∧ c) → b → (if h : d then f h x else y) > z ===>
-- ∀ (a b c d : Prop) (x y z : Int) (f : d → Int → Int) (_ : a ∧ c) (_ : b),
--   z < Blaster.dite' d (fun h => f h x) (fun _ => y)
#testOptimize [ "HypReductionUnchanged_21" ]
  ∀ (a b c d : Prop) (x y z : Int) (f : d → Int → Int) [Decidable d],
    (a ∧ c) → b → (if h : d then f h x else y) > z ===>
  ∀ (a b c d : Prop) (x y z : Int) (f : d → Int → Int) (_ : a ∧ c) (_ : b),
    z < Blaster.dite' d (fun h => f h x) (fun _ => y)

-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int),
--   (a ∧ c ∧ x < z) → b → (if h : z < y then x else f h y) > z ===>
-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int) (_: a ∧ c ∧ x < z) (_ : b),
--   z < Blaster.dite' (z < y) (fun _ => x) (fun h => f h y)
#testOptimize [ "HypReductionUnchanged_22" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int),
    (a ∧ c ∧ x < z) → b → (if h : z < y then x else f h y) > z ===>
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int) (_: a ∧ c ∧ x < z) (_ : b),
    z < Blaster.dite' (z < y) (fun _ => x) (fun h => f h y)


-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int),
--   (a ∧ c ∧ x = z) → b → (if h : z < y then x else f h y) > z ===>
-- ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int) (_ : a ∧ c ∧ x = z) (_ : b),
--   z < Blaster.dite' (z < y) (fun _ => x) (fun h => f h y)
#testOptimize [ "HypReductionUnchanged_23" ]
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int),
    (a ∧ c ∧ x = z) → b → (if h : z < y then x else f h y) > z ===>
  ∀ (a b c : Prop) (x y z : Int) (f : ¬ (z < y) → Int → Int) (_ : a ∧ c ∧ x = z) (_ : b),
    z < Blaster.dite' (z < y) (fun _ => x) (fun h => f h y)


end Test.HypReduction
