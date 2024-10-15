import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldDITE

/-! ## Test objectives to validate unfolding `dite` expressions -/

/-! Test cases to validate unfolding of `dite` expressions only when reduced via rewriting. -/

-- ∀ (c : Bool) (p : Prop), if h : c then p else p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldDIte_1" ] ∀ (c : Bool) (p : Prop), if _h : c then p else p ===> ∀ (p : Prop), p

-- ∀ (c : Bool) (x y : Int), (if h : c then x else x) < y ===> ∀ (x y : Int), x < y
#testOptimize [ "UnfoldDIte_2" ] ∀ (c : Bool) (x y : Int), (if _h : c then x else x) < y ===>
                                 ∀ (x y : Int), x < y

-- ∀ (p q : Prop), if h : True then p else q ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldDIte_3" ] ∀ (p q : Prop), if _h : True then p else q ===> ∀ (p : Prop), p

-- ∀ (x y z : Int), (if h : True then x else y) < z ===> ∀ (x z : Int), x < z
#testOptimize [ "UnfoldDIte_4" ] ∀ (x y z : Int), (if _h : True then x else y) < z ===>
                                 ∀ (x z : Int), x < z

-- ∀ (p q : Prop), if h : False then p else q ===> ∀ (q : Prop), q
#testOptimize [ "UnfoldDIte_5" ] ∀ (p q : Prop), if _h : False then p else q ===> ∀ (q : Prop), q

-- ∀ (x y z : Int), (if h : False then x else y) < z ===> ∀ (y z : Int), y < z
#testOptimize [ "UnfoldDIte_6" ] ∀ (x y z : Int), (if _h : False then x else y) < z ===>
                                 ∀ (y z : Int), y < z

-- ∀ (a b c : Bool), (if h : c then a else b) = true ===> ∀ (a b c : Bool), true = ((a || !c) && (b || c))
#testOptimize [ "UnfoldDIte_7" ] ∀ (a b c : Bool), (if _h : c then a else b) = true ===>
                                 ∀ (a b c : Bool), true = ((a || !c) && (b || c))

-- ∀ (c : Bool) (p q : Prop), if h : c then p else q ===> ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)
#testOptimize [ "UnfoldDIte_8" ] ∀ (c : Bool) (p q : Prop), if _h : c then p else q ===>
                                 ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)


/-! Test cases to validate when `dite` expressions must not be unfolded -/

-- ∀ (x y : Int), (if h : x = y then x else y) = y ===>
-- ∀ (x y : Int), y = (if h : x = y then x else y)
#testOptimize [ "DIteNotUnfolded_1" ] ∀ (x y : Int), (if _h : x = y then x else y) = y ===>
                                      ∀ (x y : Int), y = (if _h : x = y then x else y)

-- ∀ (a b : Bool) (x y : Int), (if h : a = b then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < (if h : a = b then x else y)
#testOptimize [ "DIteNotUnfolded_2" ] ∀ (a b : Bool) (x y : Int), (if _h : a = b then x else y) > x ===>
                                      ∀ (a b : Bool) (x y : Int), x < (if _h : a = b then x else y)


-- ∀ (x y : Int) (c : Prop), [Decidable c] → (if h : c then x else y) > x ===>
-- ∀ (x y : Int) (c : Prop), [Decidable c] → x < (if h : c then x else y)
#testOptimize [ "DIteNotUnfolded_3" ] ∀ (x y : Int) (c : Prop), [Decidable c] → (if _h : c then x else y) > x ===>
                                      ∀ (x y : Int) (c : Prop), [Decidable c] → x < (if _h : c then x else y)


-- ∀ (α : Type) (x y : List α), [DecidableEq α] → (if h : x = y then x else y) = y ===>
-- ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if h : x = y then x else y)
#testOptimize [ "DIteNotUnfolded_4" ] ∀ (α : Type) (x y : List α), [DecidableEq α] → (if _h : x = y then x else y) = y ===>
                                      ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if _h : x = y then x else y)


end Tests.UnfoldDITE
