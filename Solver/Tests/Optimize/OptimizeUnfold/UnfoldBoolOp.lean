import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldBoolOp

/-! ## Test objectives to validate unfolding `Bool` operators -/


/-! Test cases to validate unfolding of `Bool` operators only when reduced to a constant value or via rewriting. -/

-- ∀ (a : Bool), false && a ===> False
#testOptimize ["UnfoldBoolOp_1"] ∀ (a : Bool), false && a ===> False

-- ∀ (a : Bool), true && a ===> ∀ (a : Bool), true = a
#testOptimize ["UnfoldBoolOp_2"] ∀ (a : Bool), true && a  ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), !a && a ===> False
#testOptimize ["UnfoldBoolOp_3"] ∀ (a : Bool), !a && a ===> False

-- ∀ (a : Bool), a && a ===> ∀ (a : Bool), true = a
#testOptimize ["UnfoldBoolOp_4"] ∀ (a : Bool), a && a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), false || a ===> ∀ (a : Bool), a
#testOptimize ["UnfoldBoolOp_5"] ∀ (a : Bool), false || a ===> ∀ (a : Bool), true = a

-- ∀ (a : Bool), true || a ===> True
#testOptimize ["UnfoldBoolOp_6"] ∀ (a : Bool), true || a ===> True

-- ∀ (a : Bool), !a || a ===> True
#testOptimize ["UnfoldBoolOp_7"] ∀ (a : Bool), !a || a ===> True

-- ∀ (a : Bool), a || a ===> ∀ (a : Bool), true = a
#testOptimize ["UnfoldBoolOp_8"] ∀ (a : Bool), a || a ===> ∀ (a : Bool), true = a

-- ! false ==> true
#testOptimize ["UnfoldBoolOp_9"] ! false ===> true

-- ! true ===> false
#testOptimize ["UnfoldBoolOp_10"] ! true ===> false

-- ∀ (a : Bool), ! (!a) ===> ∀ (a : Bool), true = a
#testOptimize ["UnfoldBoolOp_11"] ∀ (a : Bool), !(!a) ===> ∀ (a : Bool), true = a


/-! Test cases to validate when `Bool` operators must not be unfolded -/

-- ∀ (a b : Bool), a && b ===> ∀ (a b : Bool), true = (a && b)
#testOptimize ["BoolOpNotUnfolded_1"] ∀ (a b : Bool), a && b ===> ∀ (a b : Bool), true = (a && b)

-- ∀ (a b : Bool), ! a && b ===> ∀ (a b : Bool), true = (b && !a)
#testOptimize ["BoolOpNotUnfolded_2"] ∀ (a b : Bool), ! a && b ===> ∀ (a b : Bool), true = (b && !a)

-- ∀ (a b : Bool), a || b ===> ∀ (a b : Bool), true = (a || b)
#testOptimize ["BoolOpNotUnfolded_3"] ∀ (a b : Bool), a || b ===> ∀ (a b : Bool), true = (a || b)

-- ∀ (a b : Bool), !a || b ===> ∀ (a b : Bool), true = (b || !a)
#testOptimize ["BoolOpNotUnfolded_4"] ∀ (a b : Bool), !a || b ===> ∀ (a b : Bool), true = (b || !a)

-- ∀ (a : Bool), !a ===> ∀ (a : Bool), !a (i.e., false = a)
#testOptimize ["BoolOpNotUnfolded_5"] ∀ (a : Bool), ! a ===> ∀ (a : Bool), false = a

-- ∀ (a : Bool), ! (! (! a)) ===> ∀ (a : Bool), !a (i.e., false = a)
#testOptimize ["BoolOpNotUnfolded_6"] ∀ (a : Bool), ! (! (! a)) ===> ∀ (a : Bool), false = a


end Tests.UnfoldBoolOp
