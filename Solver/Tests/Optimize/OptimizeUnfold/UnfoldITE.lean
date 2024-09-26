import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldITE

/-! ## Test objectives to validate unfolding `ite` expressions -/

/-! Test cases to validate unfolding of `ite` expressions only when reduced via rewriting. -/

-- ∀ (c : Bool) (p : Prop), if c then p else p ===> ∀ (c : Bool) (p : Prop), p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_1" ] ∀ (c : Bool) (p : Prop), if c then p else p ===> ∀ (_c : Bool) (p : Prop), p

-- ∀ (c : Bool) (x y : Int), (if c then x else x) < y ===> ∀ (c : Bool) (x y : Int), x < y
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_2" ] ∀ (c : Bool) (x y : Int), (if c then x else x) < y ===>
                                ∀ (_c : Bool) (x y : Int), x < y

-- ∀ (p q : Prop), if True then p else q ===> ∀ (p q : Prop), p
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_3" ] ∀ (p q : Prop), if True then p else q ===> ∀ (p _q : Prop), p

-- ∀ (x y z : Int), (if True then x else y) < z ===> ∀ (x y z : Int), x < z
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_4" ] ∀ (x y z : Int), (if True then x else y) < z ===>
                                ∀ (x _y z : Int), x < z

-- ∀ (p q : Prop), if False then p else q ===> ∀ (p q : Prop), q
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_5" ] ∀ (p q : Prop), if False then p else q ===> ∀ (_p q : Prop), q

-- ∀ (x y z : Int), (if False then x else y) < z ===> ∀ (x y z : Int), y < z
-- TODO: remove unused quantifiers when COI performed on forall
#testOptimize [ "UnfoldIte_6" ] ∀ (x y z : Int), (if False then x else y) < z ===>
                                ∀ (_x y z : Int), y < z

-- ∀ (a b c : Bool), (if c then a else b) = true ===> ∀ (a b c : Bool), true = ((a || !c) && (b || c))
#testOptimize [ "UnfoldIte_7" ] ∀ (a b c : Bool), (if c then a else b) = true ===>
                                ∀ (a b c : Bool), true = ((a || !c) && (b || c))

-- ∀ (c : Bool) (p q : Prop), if c then p else q ===> ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)
#testOptimize [ "UnfoldIte_8" ] ∀ (c : Bool) (p q : Prop), if c then p else q ===>
                                ∀ (c : Bool) (p q : Prop), (false = c → q) ∧ (true = c → p)


/-! Test cases to validate when `ite` expressions must not be unfolded -/

-- ∀ (c : Bool) (x y z : Int), (if c then x else y) < z ===>
-- ∀ (c : Bool) (x y z : Int), (if true = c then x else y) < z
#testOptimize [ "IteNotUnfolded_1" ] ∀ (c : Bool) (x y z : Int), (if c then x else y) < z ===>
                                     ∀ (c : Bool) (x y z : Int), (if true = c then x else y) < z


-- ∀ (x y : Int), (if x = y then x else y) = y ===>
-- ∀ (x y : Int), y = (if x = y then x else y)
#testOptimize [ "IteNotUnfolded_2" ] ∀ (x y : Int), (if x = y then x else y) = y ===>
                                     ∀ (x y : Int), y = (if x = y then x else y)

-- ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x ===>
-- ∀ (a b : Bool) (x y : Int), x < (if a = b then x else y)
#testOptimize [ "IteNotUnfolded_3" ] ∀ (a b : Bool) (x y : Int), (if a = b then x else y) > x ===>
                                     ∀ (a b : Bool) (x y : Int), x < (if a = b then x else y)


-- ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x ===>
-- ∀ (x y : Int) (c : Prop), [Decidable c] → x < (if c then x else y)
#testOptimize [ "IteNotUnfolded_4" ] ∀ (x y : Int) (c : Prop), [Decidable c] → (if c then x else y) > x ===>
                                     ∀ (x y : Int) (c : Prop), [Decidable c] → x < (if c then x else y)


-- ∀ (α : Type) (x y : List α), [DecidableEq α] → (if x = y then x else y) = y ===>
-- ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if x = y then x else y)
#testOptimize [ "IteNotUnfolded_5" ] ∀ (α : Type) (x y : List α), [DecidableEq α] → (if x = y then x else y) = y ===>
                                     ∀ (α : Type) (x y : List α), [DecidableEq α] → y = (if x = y then x else y)

end Tests.UnfoldITE
