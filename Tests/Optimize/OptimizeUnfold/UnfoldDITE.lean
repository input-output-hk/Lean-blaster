import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldDITE

/-! ## Test objectives to validate unfolding `dite` expressions -/

/-! Test cases to validate unfolding of `dite` expressions only when reduced via rewriting. -/

-- ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop), if h : c then (f h p) else True ===>
-- ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop), ∀ (h : true = c), f h p
#testOptimize [ "UnfoldDIte_1" ]
  ∀ (c : Bool) (p : Prop) (f : c → Prop → Prop), if h : c then (f h p) else True ===>
  ∀ (c : Bool) (p : Prop) (f : true = c → Prop → Prop), ∀ (h : true = c), f h p

-- ∀ (c : Bool) (x y : Int) (f : c → Int → Int), (if h : c then (f h x) * 0 else 0) < y ===>
-- ∀ (y : Int), 0 < y
#testOptimize [ "UnfoldDIte_2" ] (norm-result: 1)
  ∀ (c : Bool) (x y : Int) (f : c → Int → Int), (if h : c then (f h x) * 0 else 0) < y ===>
  ∀ (y : Int), 0 < y

-- ∀ (p q : Prop) (f : True → Prop → Prop), if h : True then f h p else q ===>
-- ∀ (p : Prop) (f : True → Prop → Prop), f True.intro p
#testOptimize [ "UnfoldDIte_3" ]
  ∀ (p q : Prop) (f : True → Prop → Prop), if h : True then f h p else q ===>
  ∀ (p : Prop) (f : True → Prop → Prop), f True.intro p

-- ∀ (x y z : Int) (f : True → Int → Int), (if h : True then f h x else y) < z ===>
-- ∀ (x z : Int) (f : True → Int → Int), f True.intro x < z
#testOptimize [ "UnfoldDIte_4" ]
  ∀ (x y z : Int) (f : True → Int → Int), (if h : True then f h x else y) < z ===>
  ∀ (x z : Int) (f : True → Int → Int), f True.intro x < z

-- ∀ (p q : Prop) (f : False → Prop → Prop), if h : False then f h p else q ===>
-- ∀ (q : Prop), q
#testOptimize [ "UnfoldDIte_5" ]
  ∀ (p q : Prop) (f : False → Prop → Prop), if h : False then f h p else q ===>
  ∀ (q : Prop), q

-- ∀ (x y z : Int) (f : False → Int → Int), (if h : False then f h x else y) < z ===>
-- ∀ (y z : Int), y < z
#testOptimize [ "UnfoldDIte_6" ]
  ∀ (x y z : Int) (f : False → Int → Int), (if h : False then f h x else y) < z ===>
  ∀ (y z : Int), y < z

-- ∀ (a b c : Bool) (f : c → Bool → Bool), (if h : c then f h a else b) = true ===>
-- ∀ (a b c : Bool) (f : true = c → Bool → Bool),
--   (false = c → true = b) ∧ (∀ (h : true = c), true = f h a)
#testOptimize [ "UnfoldDIte_7" ]
  ∀ (a b c : Bool) (f : c → Bool → Bool), (if h : c then f h a else b) = true ===>
  ∀ (a b c : Bool) (f : true = c → Bool → Bool),
    (false = c → true = b) ∧ (∀ (h : true = c), true = f h a)

-- ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop), if h : c then f h p else q ===>
-- ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
--   (false = c → q) ∧ (∀ (h : true = c), f h p)
#testOptimize [ "UnfoldDIte_8" ]
  ∀ (c : Bool) (p q : Prop) (f : c → Prop → Prop), if h : c then f h p else q ===>
  ∀ (c : Bool) (p q : Prop) (f : true = c → Prop → Prop),
    (false = c → q) ∧ (∀ (h : true = c), f h p)


/-! Test cases to validate when `dite` expressions must not be unfolded -/

-- ∀ (x y : Int) (t : x = y → Int) (e : ¬ x = y → Int), (if h : x = y then t h else e h) = y ===>
-- ∀ (x y : Int) (t : x = y → Int) (e : ¬ x = y → Int),
--   y = Solver.dite' (x = y) (fun h : x = y => t h) (fun h : ¬ x = y => e h)
#testOptimize [ "DIteNotUnfolded_1" ]
  ∀ (x y : Int) (t : x = y → Int) (e : ¬ x = y → Int), (if h : x = y then t h else e h) = y ===>
  ∀ (x y : Int) (t : x = y → Int) (e : ¬ x = y → Int),
    y = Solver.dite' (x = y) (fun h : x = y => t h) (fun h : ¬ x = y => e h)

-- ∀ (a b : Bool) (x y : Int) (t : a = b → Int → Int) (e : ¬ a = b → Int → Int),
--   (if h : a = b then t h x else e h y) > x ===>
-- ∀ (a b : Bool) (x y : Int) (t : a = b → Int → Int) (e : ¬ a = b → Int → Int),
--   x < Solver.dite' (a = b) (fun h : a = b => t h x) (fun h : ¬ a = b => e h y)
#testOptimize [ "DIteNotUnfolded_2" ]
  ∀ (a b : Bool) (x y : Int) (t : a = b → Int → Int) (e : ¬ a = b → Int → Int),
      (if h : a = b then t h x else e h y) > x ===>
  ∀ (a b : Bool) (x y : Int) (t : a = b → Int → Int) (e : ¬ a = b → Int → Int),
       x < Solver.dite' (a = b) (fun h : a = b => t h x) (fun h : ¬ a = b => e h y)

-- ∀ (x y : Int) (c : Prop) (t : c → Int → Int) (e : ¬ c → Int → Int),
--   [Decidable c] → (if h : c then t h x else e h y) > x ===>
-- ∀ (x y : Int) (c : Prop) (t : c → Int → Int) (e : ¬ c → Int → Int),
--   x < Solver.dite' c (fun h : c => t h x) (fun h : ¬ c => e h y)
#testOptimize [ "DIteNotUnfolded_3" ]
  ∀ (x y : Int) (c : Prop) (t : c → Int → Int) (e : ¬ c → Int → Int),
    [Decidable c] → (if h : c then t h x else e h y) > x ===>
  ∀ (x y : Int) (c : Prop) (t : c → Int → Int) (e : ¬ c → Int → Int),
     x < Solver.dite' c (fun h : c => t h x) (fun h : ¬ c => e h y)

-- ∀ (α : Type) (x y : List α) (t : x = y → List α → List α) (e : ¬ x = y → List α → List α),
--   [DecidableEq α] → (if h : x = y then t h x else e h y) = y ===>
-- ∀ (α : Type) (x y : List α) (t : x = y → List α → List α) (e : ¬ x = y → List α → List α),
--   y = Solver.dite' (x = y) (fun h : x = y => t h x) (fun h : ¬ x = y => e h y)
#testOptimize [ "DIteNotUnfolded_4" ]
  ∀ (α : Type) (x y : List α) (t : x = y → List α → List α) (e : ¬ x = y → List α → List α),
    [DecidableEq α] → (if h : x = y then t h x else e h y) = y ===>
  ∀ (α : Type) (x y : List α) (t : x = y → List α → List α) (e : ¬ x = y → List α → List α),
    y = Solver.dite' (x = y) (fun h : x = y => t h x) (fun h : ¬ x = y => e h y)


end Tests.UnfoldDITE
