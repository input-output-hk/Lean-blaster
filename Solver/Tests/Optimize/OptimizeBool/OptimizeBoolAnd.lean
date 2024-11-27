import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeBoolAnd

/-! ## Test objectives to validate normalization and simplification rules on ``and -/

/-! Test cases for `reduceApp` rule on ``and. -/

-- true && false ===> false
#testOptimize [ "BoolAndCst_1" ] true && false ===> false

-- false && true ===> false
#testOptimize [ "BoolAndCst_2" ] false && true ===> false

-- true && true ===> true
#testOptimize [ "BoolAndCst_3" ] true && true ===> true

-- false && false ===> false
#testOptimize [ "BoolAndCst_4" ] false && false ===> false

-- ! true && false ===> false
#testOptimize [ "BoolAndCst_5" ] !true && false ===> false

-- ! false && true ===> true
#testOptimize [ "BoolAndCst_6" ] ! false && true ===> true


/-! Test cases for simplification rule `false && e ==> false`. -/

-- (a && false) = false ===> True
#testOptimize [ "BoolAndFalse_1" ] ∀ (a : Bool), (a && false) = false ===> True

-- (a && false) ===> False
#testOptimize [ "BoolAndFalse_2" ] ∀ (a : Bool), a && false ===> False

-- (false && a) = false ===> True
#testOptimize [ "BoolAndFalse_3" ] ∀ (a : Bool), (false && a) = false ===> True

-- false && a ===> False
#testOptimize [ "BoolAndFalse_4" ] ∀ (a : Bool), false && a ===> False

-- false && (a || b) ===> False
#testOptimize [ "BoolAndFalse_5" ] ∀ (a b : Bool), false && (a || b) ===> False

-- false && (a && b) ===> False
#testOptimize [ "BoolAndFalse_6" ] ∀ (a b : Bool), false && (a && b) ===> False

-- a && (false && b) ===> False
#testOptimize [ "BoolAndFalse_7" ] ∀ (a b : Bool), a && (false && b) ===> False

-- a && (b && false) ===> False
#testOptimize [ "BoolAndFalse_8" ] ∀ (a b : Bool), a && (b && false) ===> False

-- let x := a || a
-- let y := a && !x
-- ((y && a) && b) ===> False
#testOptimize [ "BoolAndFalse_9" ] ∀ (a b : Bool), let x := a || a; let y := a && !x; ((y && a) && b) ===> False


/-! Test cases for simplification rule `true && e ==> e`. -/

-- (a && true) a ===> True
#testOptimize [ "BoolAndTrue_1" ] ∀ (a : Bool), (a && true) = a ===> True

-- (a && true) ===> a (i.e., true = a)
#testOptimize [ "BoolAndTrue_2" ] ∀ (a : Bool), a && true ===> ∀ (a : Bool), true = a

-- (true && a) = a ===> True
#testOptimize [ "BoolAndTrue_3" ] ∀ (a : Bool), (true && a) = a ===> True

-- (true && (a || b)) = (a || b) ===> True
#testOptimize [ "BoolAndTrue_4" ] ∀ (a b : Bool), (true && (a || b)) = (a || b) ===> True

-- ((a && b) && true) = (a && b) ===> True
#testOptimize [ "BoolAndTrue_5" ] ∀ (a b : Bool), ((a && b) && true) = (a && b) ===> True

-- ((a && true) && b) = (a && b) ===> True
#testOptimize [ "BoolAndTrue_6" ] ∀ (a b : Bool), ((a && true) && b) = (a && b) ===> True

-- ((true && a) && b) = (a && b) ===> True
#testOptimize [ "BoolAndTrue_7" ] ∀ (a b : Bool), ((true && a) && b) = (a && b) ===> True

-- let x := a && a
-- let y := a || !x
-- ((y && a) && b) ===> (a && b)
#testOptimize [ "BoolAndTrue_8" ] ∀ (a b : Bool), let x := a && a; let y := a || !x; ((y && a) && b) ===>
                                  ∀ (a b : Bool), true = (a && b)

/-! Test cases for simplification rule `e && not e ==> false`. -/

-- (a && not a) = false ===> True
#testOptimize [ "BoolAndNot_1" ] ∀ (a : Bool), (a && not a) = false ===> True

-- a && not a ===> False
#testOptimize [ "BoolAndNot_2" ] ∀ (a : Bool), a && not a ===> False

-- a && !a ===> False
#testOptimize [ "BoolAndNot_3" ] ∀ (a : Bool), a && !a ===> False

-- (a && b) && !(b && a) ===> False
#testOptimize [ "BoolAndNot_4" ] ∀ (a b : Bool), (a && b) && !(b && a) ===> False

-- (a || b) && !(b || a) ===> False
#testOptimize [ "BoolAndNot_5" ] ∀ (a b : Bool), (a || b) && !(b || a) ===> False

-- (not a && a) = false ===> True
#testOptimize [ "BoolAndNot_6" ] ∀ (a : Bool), (not a && a) = false ===> True

-- not a && a ===> False
#testOptimize [ "BoolAndNot_7" ] ∀ (a : Bool), not a && a ===> False

-- ! a && a ===> False
#testOptimize [ "BoolAndNot_8" ] ∀ (a : Bool), ! a && a ===> False

-- !(a && b) && (b && a) ===> False
#testOptimize [ "BoolAndNot_9" ] ∀ (a b : Bool), !(a && b) && (b && a) ===> False

-- !(a || b) && (b || a) ===> False
#testOptimize [ "BoolAndNot_10" ] ∀ (a b : Bool), !(a || b) && (b || a) ===> False


/-! Test cases to ensure that simplification rule `e && not e ==> false` is not applied wrongly. -/

-- not a && b ===> not a && b
-- NOTE: reordering applied on operands
#testOptimize [ "BoolAndNotUnchanged_1" ] ∀ (a b : Bool), not a && b ===>
                                          ∀ (a b : Bool), true = (b && not a)

-- b && not a ===> b && not a
#testOptimize [ "BoolAndNotUnchanged_2" ] ∀ (a b : Bool), b && not a ===>
                                          ∀ (a b : Bool), true = (b && not a)
-- not (a && b) && c ===> not (a && b) && c
#testOptimize [ "BoolAndNotUnchanged_3" ] ∀ (a b c : Bool), not (a && b) && c ===>
                                          ∀ (a b c : Bool), true = (c && not (a && b))

-- c && !(a || b) ===> c && !(a || b)
#testOptimize [ "BoolAndNotUnchanged_4" ] ∀ (a b c : Bool), c && !(a || b) ===>
                                          ∀ (a b c : Bool), true = (c && !(a || b))

-- (a || b) && !(c || d) ===> (a || b) && !(c || d)
#testOptimize [ "BoolAndNotUnchanged_5" ] ∀ (a b c d : Bool), (a || b) && !(c || d) ===>
                                          ∀ (a b c d : Bool), true = (!(c || d) && (a || b))

-- not a && not a ===> not a (i.e., false = a)
#testOptimize [ "BoolAndNotUnchanged_6" ] ∀ (a : Bool), not a && not a ===> ∀ (a : Bool), false = a

-- not a && not b ===> not a && not b
#testOptimize [ "BoolAndNotUnchanged_7" ] ∀ (a b : Bool), not a && not b ===>
                                          ∀ (a b : Bool), true = (not a && not b)


/-! Test cases for simplification rule `e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)`. -/

-- (a && a) = a ===> True
#testOptimize [ "BoolAndSubsumption_1" ] ∀ (a : Bool), (a && a) = a ===> True

-- (a && a) ===> a
#testOptimize [ "BoolAndSubsumption_2" ] ∀ (a : Bool), a && a ===> ∀ (a : Bool), true = a


-- (a || b) && (b || a) ===> (a || b)
#testOptimize [ "BoolAndSubsumption_3" ] ∀ (a b: Bool), (a || b) && (b || a) ===>
                                         ∀ (a b : Bool), true = (a || b)

-- (a || (b && b)) && (b || a) ===> (a || b)
#testOptimize [ "BoolAndSubsumption_4" ] ∀ (a b: Bool), (a || (b && b)) && (b || a) ===>
                                         ∀ (a b : Bool), true = (a || b)

-- (a || (b && b)) && (b || (a || a)) ===> (a || b)
#testOptimize [ "BoolAndSubsumption_5" ] ∀ (a b: Bool), (a || (b && b)) && (b || (a || a)) ===>
                                         ∀ (a b : Bool), true = (a || b)


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `false && e ==> false`
     - `true && e ==> e`
     -`e1 && e2 ==> e1 (if e1 =ₚₜᵣ e2)`
-/
-- a && b ===> a && b
#testOptimize [ "BoolAndUnchanged_1" ] ∀ (a b : Bool), (a && b) ===> ∀ (a b : Bool), true = (a && b)

-- (a && c) && (b || d) ===> (a && c) && (b || d)
#testOptimize [ "BoolAndUnchanged_2" ] ∀ (a b c d : Bool), (a && c) && (b || d) ===>
                                       ∀ (a b c d : Bool), true = ((a && c) && (b || d))



/-! Test cases for normalization rule `e1 && e2 ==> e2 && e1 (if e2 <ₒ e1)`. -/

-- a && b = a && b ===> True
#testOptimize [ "BoolAndCommut_1" ] ∀ (a b : Bool), (a && b) = (a && b) ===> True

-- a && b = b && a ===> True
#testOptimize [ "BoolAndCommut_2" ] ∀ (a b : Bool), (a && b) = (b && a) ===> True

-- b && a ===> a && b (when `a` declared first)
#testOptimize [ "BoolAndCommut_3" ] ∀ (a b : Bool), (b && a) ===>
                                    ∀ (a b : Bool), true = (a && b)

-- (a && (b && c)) = ((c && b) && a) ===> True
#testOptimize [ "BoolAndCommut_4" ] ∀ (a b c : Bool), (a && (b && c)) = ((c && b) && a) ===> True



/-! Test cases to ensure that `reduceApp` is properly called
    when `and` operands are reduced to constant values via optimization. -/

variable (a : Bool)
variable (b : Bool)
variable (c : Bool)

-- (a && false) && (true || b) ===> false
#testOptimize [ "BoolAndReduce_1"] (a && false) && (true || b) ===> false

-- (a && false) && (b || !b) ===> false
#testOptimize [ "BoolAndReduce_2"] (a && false) && (b || !b) ===> false

-- (a || !a) && (b || !b) ===> true
#testOptimize [ "BoolAndReduce_3"] (a || !a) && (b || !b) ===> true

-- (a && !a) && (b || !b) ===> false
#testOptimize [ "BoolAndReduce_4"] (a && !a) && (b || !b) ===> false

-- ((a || ((b || c) && !(c || b))) || !a) && ((b && a) && !(a && b)) ===> false
#testOptimize [ "BoolAndReduce_5"] ((a || ((b || c) && !(c || b))) || !a) && ((b && a) && !(a && b)) ===> false

-- ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===> true
#testOptimize [ "BoolAndReduce_6"] ((!a || ((b || c) && !(c || b))) || a) && (!(b && a) || (a && b)) ===> true


end Test.OptimizeBoolAnd
