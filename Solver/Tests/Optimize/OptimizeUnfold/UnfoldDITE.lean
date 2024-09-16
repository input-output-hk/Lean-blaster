import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldDITE

/-! ## Test objectives to validate unfolding `dite` expressions -/

/-! Test cases to validate unfolding of `dite` expressions only when reduced via rewriting. -/

-- ∀ (c : Bool) (p : Prop), if h : c then p else p ===> ∀ (c : Bool) (p : Prop), p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_1" ] ∀ (c : Bool) (p : Prop), if _h : c then p else p ===> ∀ (_c : Bool) (p : Prop), p

-- ∀ (c : Bool) (x y : Int), (if h : c then x else x) < y ===> ∀ (c : Bool) (x y : Int), x < y
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_2" ] ∀ (c : Bool) (x y : Int), (if _h : c then x else x) < y ===>
                                 ∀ (_c : Bool) (x y : Int), x < y

-- ∀ (p q : Prop), if h : True then p else q ===> ∀ (p q : Prop), p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_3" ] ∀ (p q : Prop), if _h : True then p else q ===> ∀ (p _q : Prop), p

-- ∀ (x y z : Int), (if h : True then x else y) < z ===> ∀ (x y z : Int), x < z
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_4" ] ∀ (x y z : Int), (if _h : True then x else y) < z ===>
                                 ∀ (x _y z : Int), x < z

-- ∀ (p q : Prop), if h : False then p else q ===> ∀ (p q : Prop), q
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_5" ] ∀ (p q : Prop), if _h : False then p else q ===> ∀ (_p q : Prop), q

-- ∀ (x y z : Int), (if h : False then x else y) < z ===> ∀ (x y z : Int), y < z
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldDIte_6" ] ∀ (x y z : Int), (if _h : False then x else y) < z ===>
                                 ∀ (_x y z : Int), y < z

-- ∀ (a b c : Bool), (if h : c then a else b) = true ===> ∀ (a b c : Bool), true = ((b || c) && (a || !c))
#testOptimize [ "UnfoldDIte_7" ] ∀ (a b c : Bool), (if _h : c then a else b) = true ===>
                                 ∀ (a b c : Bool), true = ((b || c) && (a || !c) )

-- ∀ (c : Bool) (p q : Prop), if h : c then p else q ===> ∀ (c : Bool) (p q : Prop), (true = c → p) ∧ (false = c → q)
#testOptimize [ "UnfoldDIte_8" ] ∀ (c : Bool) (p q : Prop), if _h : c then p else q ===>
                                 ∀ (c : Bool) (p q : Prop), (true = c → p) ∧ (false = c → q)


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
