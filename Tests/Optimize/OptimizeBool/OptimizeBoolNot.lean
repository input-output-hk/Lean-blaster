import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolNot
/-! ## Test objectives to validate normalization and simplification rules on ``not -/

/-! Test cases for `reduceApp` rule on ``not. -/

-- not false ===> true
#testOptimize [ "BoolNotCst_1", proof ] not false ===> true

-- ! false ===> true
#testOptimize [ "BoolNotCst_2", proof ] ! false ===> true

-- not true ===> false
#testOptimize [ "BoolNotCst_3", proof ] not true ===> false

-- ! true ===> false
#testOptimize [ "BoolNotCst_4", proof ] ! true ===> false

/-! Test cases for simplification rule `! (! e) ==> e`. -/

-- not (not a) = a ===> True
#testOptimize [ "BoolNot_1", proof ] ∀ (a : Bool), not (not a) = a ===> True

-- not (not a) ===> a
#testOptimize [ "BoolNot_2", proof ] ∀ (a : Bool), not (not a) ===> ∀ (a : Bool), true = a

-- not (not (not a)) = not a ===> True
#testOptimize [ "BoolNot_3", proof ] ∀ (a : Bool), not (not (not a)) = not a ===> True

-- not (not (not (not a))) = a ===> True
#testOptimize [ "BoolNot_4", proof ] ∀ (a : Bool), not (not (not (not a))) = a ===> True

-- ! (! a) = a ==> True
#testOptimize [ "BoolNot_5", proof ] ∀ (a : Bool), (! (! a)) = a ===> True

-- ! (! a) ===> a
#testOptimize [ "BoolNot_6", proof ] ∀ (a : Bool), (! (! a)) ===> ∀ (a : Bool), true = a

-- ! (! (! a)) = ! a ===> True
#testOptimize [ "BoolNot_7", proof ] ∀ (a : Bool), (! (! (! a))) = (! a) ===> True

-- ! (! (! (! a))) = a ===> True
#testOptimize [ "BoolNot_8", proof ] ∀ (a : Bool), (! (! (! (! a)))) = a ===> True

-- ! ( !(a && b)) = (a && b) ===> True
#testOptimize [ "BoolNot_9", proof ] ∀ (a b : Bool), (! (! (a && b))) = (a && b) ===> True

-- ! ( !(a == b)) = (a == b) ===> True
#testOptimize [ "BoolNot_10", proof ] ∀ (a b : Bool), (! (! (a == b))) = (a == b) ===> True


/-! Test cases to ensure when `! (! e) ==> e` must not be applied. -/

-- !a ===> !a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_1", proof ] ∀ (a : Bool), !a ===> ∀ (a : Bool), false = a

-- ! (! (! a)) ===> ! a (i.e., false = a)
#testOptimize [ "BoolNotUnchanged_2", proof ] ∀ (a : Bool), ! (! (!a)) ===> ∀ (a : Bool), false = a

-- ! (a == b) ===> ¬ (a = b)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "BoolNotUnchanged_3" ] ∀ (a b : Bool), ! (a == b) ===> ∀ (a b : Bool), ¬ (a = b)

-- ! (a && b) ===> false = (a && b)
#testOptimize [ "BoolNotUnchanged_4", proof ] ∀ (a b : Bool), ! (a && b) ===> ∀ (a b : Bool), false = (a && b)

-- if c then !a else b ===> (false = c → true = b) ∧ (true = c → false = a)
#testOptimize [ "BoolNotUnchanged_5" ]
  ∀ (c a b : Bool), true = (if c then !a else b) ===>
  ∀ (c a b : Bool), (false = c → true = b) ∧ (true = c → false = a)

/-! Test cases to ensure that constant propagation is properly performed
    when `not operand is reduced to a constant value via optimization.
-/

variable (a : Bool)
variable (b : Bool)

-- ! (a || !a) ===> false
#testOptimize [ "BoolNotReduce_1", proof ] ! (a || !a) ===> false

-- ! (a && !a) ===> true
#testOptimize [ "BoolNotReduce_2", proof ] ! (a && !a) ===> true

-- ! (a || (b || !b)) ==> false
#testOptimize [ "BoolNotReduce_3", proof ] ! (a || (b || !b)) ===> false

-- ! ((a || (b && !b)) && !a) ==> true
#testOptimize [ "BoolNotReduce_4", proof ] ! ((a || (b && !b)) && !a) ===> true

end Tests.OptimizeBoolNot
