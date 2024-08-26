import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolNot
/-! ## Test objectives to validate normalization and simplification rules on ``not -/

-- not false ===> true
#testOptimize [ "BoolNotFalse_1" ] not false ===> true

-- ! false ===> true
#testOptimize [ "BoolNotFalse_2" ] ! false ===> true

-- not true ===> false
#testOptimize [ "BoolNotTrue_1" ] not true ===> false

-- ! true ===> false
#testOptimize [ "BoolNotTrue_2" ] ! true ===> false

-- not (not a) ===> a
#testOptimize [ "BoolNotBoolNot_1" ] ∀ (a : Bool), not (not a) = a ===> True

-- not (not (not a)) ===> not a
#testOptimize [ "BoolNotBoolNot_2" ] ∀ (a : Bool), not (not (not a)) = not a ===> True

-- not (not (not (not a))) ===> a
#testOptimize [ "BoolNotBoolNot_3" ] ∀ (a : Bool), not (not (not (not a))) = a ===> True

-- ! (! a) ===> a
#testOptimize [ "BoolNotBoolNot_4" ] ∀ (a : Bool), (! (! a)) = a ===> True

-- ! (! (! a)) ===> ! a
#testOptimize [ "BoolNotBoolNot_5" ] ∀ (a : Bool), (! (! (! a))) = (! a) ===> True

-- ! (! (! (! a))) ===> a
#testOptimize [ "BoolNotBoolNot_6" ] ∀ (a : Bool), (! (! (! (! a)))) = a ===> True

-- !a ===> !a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_1" ] ∀ (a : Bool), !a ===> ∀ (a : Bool), false = a

-- ! (! (! a)) ===> ! a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_2" ] ∀ (a : Bool), ! (! (!a)) ===> ∀ (a : Bool), false = a

-- ! (a == b) ===> !(a == b) (i.e., false = (a == b))
#testOptimize [ "BoolNotUnchanged_3" ] ∀ (a b : Bool), ! (a == b) ===> ∀ (a b : Bool), false = (a == b)

-- ! (!a == b) ===> !(!a == b) (i.e., false = (!a == b))
-- NOTE: reordering applied on operands
#testOptimize [ "BoolNotUnchanged_4" ] ∀ (a b : Bool), ! ((!a) == b) ===> ∀ (a b : Bool), false = (b == !a)

end Tests.OptimizeBoolNot
