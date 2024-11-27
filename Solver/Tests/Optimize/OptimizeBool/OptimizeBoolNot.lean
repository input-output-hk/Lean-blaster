import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolNot
/-! ## Test objectives to validate normalization and simplification rules on ``not -/

/-! Test cases for `reduceApp` rule on ``not. -/

-- not false ===> true
#testOptimize [ "BoolNotCst_1" ] not false ===> true

-- ! false ===> true
#testOptimize [ "BoolNotCst_2" ] ! false ===> true

-- not true ===> false
#testOptimize [ "BoolNotCst_3" ] not true ===> false

-- ! true ===> false
#testOptimize [ "BoolNotCst_4" ] ! true ===> false

/-! Test cases for simplification rule `! (! e) ==> e`. -/

-- not (not a) = a ===> True
#testOptimize [ "BoolNot_1" ] ∀ (a : Bool), not (not a) = a ===> True

-- not (not a) ===> a
#testOptimize [ "BoolNot_2" ] ∀ (a : Bool), not (not a) ===> ∀ (a : Bool), true = a

-- not (not (not a)) = not a ===> True
#testOptimize [ "BoolNot_3" ] ∀ (a : Bool), not (not (not a)) = not a ===> True

-- not (not (not (not a))) = a ===> True
#testOptimize [ "BoolNot_4" ] ∀ (a : Bool), not (not (not (not a))) = a ===> True

-- ! (! a) = a ==> True
#testOptimize [ "BoolNot_5" ] ∀ (a : Bool), (! (! a)) = a ===> True

-- ! (! a) ===> a
#testOptimize [ "BoolNot_6" ] ∀ (a : Bool), (! (! a)) ===> ∀ (a : Bool), true = a

-- ! (! (! a)) = ! a ===> True
#testOptimize [ "BoolNot_7" ] ∀ (a : Bool), (! (! (! a))) = (! a) ===> True

-- ! (! (! (! a))) = a ===> True
#testOptimize [ "BoolNot_8" ] ∀ (a : Bool), (! (! (! (! a)))) = a ===> True

-- ! ( !(a && b)) = (a && b) ===> True
#testOptimize [ "BoolNot_9" ] ∀ (a b : Bool), (! (! (a && b))) = (a && b) ===> True

-- ! ( !(a == b)) = (a == b) ===> True
#testOptimize [ "BoolNot_10" ] ∀ (a b : Bool), (! (! (a == b))) = (a == b) ===> True


/-! Test cases to ensure when `! (! e) ==> e` must not be applied. -/

-- !a ===> !a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_1" ] ∀ (a : Bool), !a ===> ∀ (a : Bool), false = a

-- ! (! (! a)) ===> ! a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_2" ] ∀ (a : Bool), ! (! (!a)) ===> ∀ (a : Bool), false = a

-- ! (a == b) ===> ¬ (a = b)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BoolNotUnchanged_3" ] ∀ (a b : Bool), ! (a == b) ===> ∀ (a b : Bool), ¬ (a = b)

-- ! (a && b) ===> false = (a && b)
#testOptimize [ "BoolNotUnchanged_4" ] ∀ (a b : Bool), ! (a && b) ===> ∀ (a b : Bool), false = (a && b)

-- if c then !a else b ===> true = ((c || b) && (!c || !a))
#testOptimize [ "BoolNotUnchanged_5" ] ∀ (c a b : Bool), true = (if c then !a else b) ===>
                                       ∀ (c a b : Bool), true = ((c || b) && (!c || !a))


/-! Test cases to ensure that `reduceApp` is properly called
    when `not operand is reduced to a constant value via optimization. -/

variable (a : Bool)
variable (b : Bool)

-- ! (a || !a) ===> false
#testOptimize [ "BoolNotReduce_1" ] ! (a || !a) ===> false

-- ! (a && !a) ===> true
#testOptimize [ "BoolNotReduce_2" ] ! (a && !a) ===> true

-- ! (a || (b || !b)) ==> false
#testOptimize [ "BoolNotReduce_3" ] ! (a || (b || !b)) ===> false

-- ! ((a || (b && !b)) && !a) ==> true
#testOptimize [ "BoolNotReduce_4" ] ! ((a || (b && !b)) && !a) ===> true

end Tests.OptimizeBoolNot
