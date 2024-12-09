import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolOr

/-! ## Test objectives to validate normalization and simplification rules on ``or -/


/-! Test cases for `reduceApp` rule on ``or. -/

-- true || false ===> true
#testOptimize [ "BoolOrCst_1" ] true || false ===> true

-- false || true ===> true
#testOptimize [ "BoolOrCst_2" ] false || true ===> true

-- true || true ===> true
#testOptimize [ "BoolOrCst_3" ] true || true ===> true

-- false || false ===> false
#testOptimize [ "BoolOrCst_4" ] false || false ===> false

-- ! true || false ===> false
#testOptimize [ "BoolOrCst_5" ] !true || false ===> false

-- ! false || false ===> true
#testOptimize [ "BoolOrCst_6" ] !false || false ===> true


/-! Test cases for simplification rule `false || e ==> e`. -/

-- (a || false) = a ===> True
#testOptimize [ "BoolOrFalse_1" ] ∀ (a : Bool), (a || false) = a ===> True

-- a || false ===> a (i.e., true = a)
#testOptimize [ "BoolOrFalse_2" ] ∀ (a : Bool), (a || false) ===> ∀ (a : Bool), true = a

-- (false || a) = a ===> True
#testOptimize [ "BoolOrFalse_3" ] ∀ (a : Bool), (false || a) = a ===> True

-- (false || (a && b)) = a && b ===> True
#testOptimize [ "BoolOrFalse_4" ] ∀ (a b : Bool), (false || (a && b)) = (a && b) ===> True

-- ((a || b) || false) = a || b ===> True
#testOptimize [ "BoolOrFalse_5" ] ∀ (a b : Bool), ((a || b) || false) = (a || b) ===> True

-- ((a || false) || b) = a || b ===> True
#testOptimize [ "BoolOrFalse_6" ] ∀ (a b : Bool), ((a || false) || b) = (a || b) ===> True

-- ((false || a) || b) = a || b ===> True
#testOptimize [ "BoolOrFalse_7" ] ∀ (a b : Bool), ((false || a) || b) = (a || b) ===> True

-- let x := a || a
-- let y := a && !x
-- ((y || a) || b) ===> a || b
#testOptimize [ "BoolOrFalse_8" ] ∀ (a b : Bool), let x := a || a; let y := a && !x; ((y || a) || b) ===>
                                  ∀ (a b : Bool), true = (a || b)


/-! Test cases for simplification rule `true || e ==> true`. -/

-- (a || true) = true ===> True
#testOptimize [ "BoolOrTrue_1" ] ∀ (a : Bool), (a || true) = true ===> True

-- (a || true) ====> True
#testOptimize [ "BoolOrTrue_2" ] ∀ (a : Bool), (a || true) ===> True

-- (true || a) = true ===> True
#testOptimize [ "BoolOrTrue_3" ] ∀ (a : Bool), (true || a) = true ===> True

-- true || a ===> True
#testOptimize [ "BoolOrTrue_4" ] ∀ (a : Bool), true || a ===> True

-- true || (a && b) ===> True
#testOptimize [ "BoolOrTrue_5" ] ∀ (a b : Bool), true || (a && b) ===> True

-- (a || b) || true ===> True
#testOptimize [ "BoolOrTrue_6" ] ∀ (a b : Bool), (a || b) || true ===> True

-- (a || true) || b ===> True
#testOptimize [ "BoolOrTrue_7" ] ∀ (a b : Bool), (a || true) || b ===> True

-- (true || a) || b ===> True
#testOptimize [ "BoolOrTrue_8" ] ∀ (a b : Bool), (true || a) || b ===> True

-- let x := a && a
-- let y := a || !x
-- ((y || a) || b) ===> True
#testOptimize [ "BoolOrTrue_9" ] ∀ (a b : Bool), let x := a && a; let y := a || !x; ((y || a) || b) ===> True


/-! Test cases for simplification rule `e || not e ==> true`. -/

-- (a || not a) = true ===> True
#testOptimize [ "BoolOrNot_1" ] ∀ (a : Bool), (a || not a) = true ===> True

-- a || not a ===> True
#testOptimize [ "BoolOrNot_2" ] ∀ (a : Bool), (a || not a) ===> True

-- a || !a ===> True
#testOptimize [ "BoolOrNot_3" ] ∀ (a : Bool), (a || !a) ===> True

-- (a && b) || !(b && a) ===> True
#testOptimize [ "BoolOrNot_4" ] ∀ (a b : Bool), (a && b) || !(b && a) ===> True

-- (a || b) || !(b || a) ===> True
#testOptimize [ "BoolOrNot_5" ] ∀ (a b : Bool), (a || b) || !(b || a) ===> True

-- (not a || a) = true ===> True
#testOptimize [ "BoolOrNot_6" ] ∀ (a : Bool), (not a || a) = true ===> True

-- not a || a ===> True
#testOptimize [ "BoolOrNot_7" ] ∀ (a : Bool), (not a || a) ===> True

-- !a || a ===> True
#testOptimize [ "BoolOrNot_8" ] ∀ (a : Bool), (!a || a) ===> True

-- !(a && b) || (b && a) ===> True
#testOptimize [ "BoolOrNot_9" ] ∀ (a b : Bool), !(a && b) || (b && a) ===> True

-- !(a || b) || (b || a) ===> True
#testOptimize [ "BoolOrNot_10" ] ∀ (a b : Bool), !(a || b) || (b || a) ===> True


/-! Test cases to ensure that simplification rule `e || not e ==> true` is not applied wrongly. -/

-- not a || b ===> not a || b
-- NOTE: reordering applied on operands
#testOptimize [ "BoolOrNotUnchanged_1" ] ∀ (a b : Bool), not a || b ===>
                                         ∀ (a b : Bool), true = (b || not a)

-- b || not a ===> b || not a
#testOptimize [ "BoolOrNotUnchanged_2" ] ∀ (a b : Bool), b || not a ===>
                                         ∀ (a b : Bool), true = (b || not a)

-- not (a && b) || c ===> not (a && b) || c
-- NOTE: reordering applied on operands
#testOptimize [ "BoolOrNotUnchanged_3" ] ∀ (a b c : Bool), not (a && b) || c ===>
                                         ∀ (a b c : Bool), true = (c || not (a && b))

-- c || !(a || b) ===> c || !(a || b)
#testOptimize [ "BoolOrNotUnchanged_4" ] ∀ (a b c : Bool), c || !(a || b) ===>
                                         ∀ (a b c : Bool), true = (c || !(a || b))

-- (a && b) || !(c && d) ===> (a && b) || !(c && d)
-- NOTE: reordering applied on operands
#testOptimize [ "BoolOrNotUnchanged_5" ] ∀ (a b c d : Bool), (a && b) || !(c && d) ===>
                                         ∀ (a b c d : Bool), true = (!(c && d) || (a && b))

-- not a || not a ===> not a (i.e., false = a)
#testOptimize [ "BoolOrNotUnchanged_6" ] ∀ (a : Bool), not a || not a ===> ∀ (a : Bool), false = a

-- !a || !b ==> !a || !b
#testOptimize [ "BoolOrNotUnchanged_7" ] ∀ (a b : Bool), (!a || !b) ===>
                                         ∀ (a b : Bool), true = (!a || !b)

/-! Test cases for simplification rule `e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)`. -/

-- a || a = a ===> True
#testOptimize [ "BoolOrSubsumption_1" ] ∀ (a : Bool), (a || a) = a ===> True

-- a || a ===> a
#testOptimize [ "BoolOrSubsumption_2" ] ∀ (a : Bool), a || a ===> ∀ (a : Bool), true = a

-- (a && b) || (b && a) ===> (a && b)
#testOptimize [ "BoolOrSubsumption_3" ] ∀ (a b : Bool), (a && b) || (b && a) ===>
                                        ∀ (a b : Bool), true = (a && b)

-- ((b || b) && a) || (a && b) ===> (a && b)
#testOptimize [ "BoolOrSubsumption_4" ] ∀ (a b : Bool), ((b || b) && a) || (a && b) ===>
                                        ∀ (a b : Bool), true = (a && b)

-- ((b || b) && a) || ((a && a) && b) ===> (a && b)
#testOptimize [ "BoolOrSubsumption_5" ] ∀ (a b : Bool), ((b || b) && a) || ((a && a) && b) ===>
                                        ∀ (a b : Bool), true = (a && b)


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `false || e ==> e`
     - `true || e ==> true`
     - `e1 || e2 ==> e1 (if e1 =ₚₜᵣ e2)`
-/

-- a || b ===> a || b
#testOptimize [ "BoolOrUnchanged_1" ] ∀ (a b : Bool), (a || b) ===> ∀ (a b : Bool), true = (a || b)

-- (a && c) || (b || d) ===> (a && c) || (b || d)
#testOptimize [ "BoolOrUnchanged_2" ] ∀ (a b c d : Bool), (a && c) || (b || d) ===>
                                      ∀ (a b c d : Bool), true = ((a && c) || (b || d))


/-! Test cases for normalization rule `e1 || e2 ==> e2 || e1 (if e2 <ₒ e1)`. -/

-- a || b = a || b ===> True
#testOptimize [ "BoolOrCommut_1" ] ∀ (a b : Bool), (a || b) = (a || b) ===> True

-- a || b = b || a ===> True
#testOptimize [ "BoolOrCommut_2" ] ∀ (a b : Bool), (a || b) = (b || a) ===> True

-- b || a ===> a || b (when `a` declared first)
#testOptimize [ "BoolOrCommut_3" ] ∀ (a b : Bool), (b || a) ===>
                                   ∀ (a b : Bool), true = (a || b)

-- (a || (b || c)) = ((c || b) || a) ===> True
#testOptimize [ "BoolOrCommut_4" ] ∀ (a b c : Bool), (a || (b || c)) = ((c || b) || a) ===> True


/-! Test cases to ensure that constant propagation is properly performed
    when `or` operands are reduced to constant values via optimization.
-/

variable (a : Bool)
variable (b : Bool)
variable (c : Bool)

-- (a && false) || (true || b) ===> true
#testOptimize [ "BoolOrReduce_1"] (a && false) || (true || b) ===> true

-- (a && false) || (b || !b) ===> true
#testOptimize [ "BoolOrReduce_2"] (a && false) || (b || !b) ===> true

-- (a && !a) || (b || !b) ===> true
#testOptimize [ "BoolOrReduce_3"] (a && !a) || (b || !b) ===> true

-- (a && !a) || (b && !b) ===> false
#testOptimize [ "BoolOrReduce_4"] (a && !a) || (b && !b) ===> false

-- ((a || ((b || c) && !(c || b))) || !a) || ((b && a) && !(a && b)) ===> true
#testOptimize [ "BoolOrReduce_5"] ((a || ((b || c) && !(c || b))) || !a) || ((b && a) && !(a && b)) ===> true

-- ((!a || ((b || c) && !(c || b))) && a) || (!(b && a) && (a && b)) ===> false
#testOptimize [ "BoolOrReduce_6"] ((!a || ((b || c) && !(c || b))) && a) || (!(b && a) && (a && b)) ===> false

end Tests.OptimizeBoolOr
