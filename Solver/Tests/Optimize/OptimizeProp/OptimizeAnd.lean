import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeAnd
/-! ## Test objectives to validate normalization and simplification rules on ``And -/

/-! Test cases for simplification rule `False ∧ e ==> False`. -/

-- False ∧ True ===> False
#testOptimize [ "AndFalse_1" ] False ∧ True ===> False

-- (False ∧ True) = False ===> True
#testOptimize [ "AndFalse_2" ] (False ∧ True) = False ===> True

-- True ∧ False ===> False
#testOptimize [ "AndFalse_3" ] True ∧ False ===> False

-- False ∧ False ===> False
#testOptimize [ "AndFalse_4" ] False ∧ False ===> False

-- a ∧ False ===> False
#testOptimize [ "AndFalse_5" ] ∀ (a : Prop), a ∧ False ===> False

-- (a ∧ False) = False ===> True
#testOptimize [ "AndFalse_6" ] ∀ (a : Prop), (a ∧ False) = False ===> True

-- False ∧ a ===> False
#testOptimize [ "AndFalse_7" ] ∀ (a : Prop), False ∧ a ===> False

-- False ∧ (a ∧ b) ===> False
#testOptimize [ "AndFalse_8" ] ∀ (a b : Prop), False ∧ (a ∧ b) ===> False

-- (a ∨ b) ∧ False ===> False
#testOptimize [ "AndFalse_9" ] ∀ (a b : Prop), (a ∨ b) ∧ False ===> False

-- (a ∧ False) ∧ b  ===> False
#testOptimize [ "AndFalse_10" ] ∀ (a b : Prop), (a ∧ False) ∧ b ===> False

-- (False ∧ a) ∧ b  ===> False
#testOptimize [ "AndFalse_11" ] ∀ (a b : Prop), (False ∧ a) ∧ b ===> False

-- (a ∧ False) ∧ (a ∧ b) ===> False
#testOptimize [ "AndFalse_12" ] ∀ (a b : Prop), (a ∧ False) ∧ (a ∧ b) ===> False

-- (a ∧ False) ∨ (b ∨ ¬ b) ===> True
#testOptimize [ "AndFalse_13"] ∀ (a b : Prop), (a ∧ False) ∨ (b ∨ ¬ b) ===> True

-- (a ∨ ¬ a) ∧ (b ∧ ¬ b) ===> False
#testOptimize [ "AndFalse_14"] ∀ (a b : Prop), (a ∨ ¬ a) ∧ (b ∧ ¬ b) ===> False

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b)) ===> False
#testOptimize [ "AndFalse_15"] ∀ (a b c : Prop), ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∧ ((b ∧ a) ∧ ¬(a ∧ b)) ===> False

-- let x := a ∨ a
-- let y := a ∧ ¬ x
-- ((y ∧ a) ∧ b) ===> False
#testOptimize [ "AndFalse_16" ] ∀ (a b : Prop), let x := a ∨ a; let y := a ∧ ¬ x; ((y ∧ a) ∧ b) ===> False


/-! Test cases for simplification rule `True ∧ e ==> e`. -/

-- True ∧ True ===> True
#testOptimize [ "AndTrue_1" ] True ∧ True ===> True

-- (True ∧ True) = True ===> True
#testOptimize [ "AndTrue_2" ] (True ∧ True) = True ===> True

-- a ∧ True ===> a
#testOptimize [ "AndTrue_3" ] ∀ (a : Prop), a ∧ True ===> ∀ (a : Prop), a

-- (a ∧ True) = a ===> True
#testOptimize [ "AndTrue_4" ] ∀ (a : Prop), (a ∧ True) = a ===> True

-- True ∧ a ===> a
#testOptimize [ "AndTrue_5" ] ∀ (a : Prop), True ∧ a ===> ∀ (a : Prop), a

-- True ∧ (a ∨ b) ===> a ∨ b
#testOptimize [ "AndTrue_6" ] ∀ (a b : Prop), True ∧ (a ∨ b) ===> ∀ (a b : Prop), a ∨ b

-- (a ∧ b) ∧ True ==> a ∧ b
#testOptimize [ "AndTrue_7" ] ∀ (a b : Prop), (a ∧ b) ∧ True ===> ∀ (a b : Prop), a ∧ b

-- (a ∧ True) ∧ b  ===> a ∧ b
#testOptimize [ "AndTrue_8" ] ∀ (a b : Prop), (a ∧ True) ∧ b ===> ∀ (a b : Prop), a ∧ b

-- (True ∧ a) ∧ b ===> a ∧ b
#testOptimize [ "AndTrue_9" ] ∀ (a b : Prop), (True ∧ a) ∧ b ===> ∀ (a b : Prop), a ∧ b

-- (a ∨ True) ∧ (a ∨ b) ===> a ∨ b
#testOptimize [ "AndTrue_10" ] ∀ (a b : Prop), (a ∨ True) ∧ (a ∨ b) ===> ∀ (a b : Prop), a ∨ b

-- (a ∧ b) ∧ (b ∨ ¬ b) ===> a ∧ b
#testOptimize [ "AndTrue_11"] ∀ (a b : Prop), (a ∧ b) ∧ (b ∨ ¬ b) ===> ∀ (a b : Prop), a ∧ b

-- (a ∨ ¬ a) ∧ (b ∨ ¬ b) ===> True
#testOptimize [ "AndTrue_12"] ∀ (a b : Prop), (a ∨ ¬ a) ∧ (b ∨ ¬ b) ===> True

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∧ ((b ∧ a) ∧ c)) ===> ((b ∧ a) ∧ c)
-- NOTE: reordering applied on operands
#testOptimize [ "AndTrue_13"] ∀ (a b c : Prop), ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∧ ((b ∧ a) ∧ c) ===>
                              ∀ (a b c : Prop), c ∧ (a ∧ b)

-- let x := a ∧ a
-- let y := a ∨ ¬ x
-- ((y ∧ a) ∧ b) ===> (a ∧ b)
#testOptimize [ "AndTrue_14" ] ∀ (a b : Prop), let x := a ∧ a; let y := a ∨ ¬x; ((y ∧ a) ∧ b) ===>
                               ∀ (a b : Prop), a ∧ b


/-! Test cases for simplification rule `e ∧ ¬ e ==> False`. -/

-- a ∧ ¬ a ===> False
#testOptimize [ "AndNeg_1" ] ∀ (a : Prop), a ∧ ¬ a ===> False

-- (a ∧ ¬ a) = False ===> True
#testOptimize [ "AndNeg_2" ] ∀ (a : Prop), (a ∧ ¬ a) = False ===> True

-- (a ∧ b) ∧ ¬ (b ∧ a) ===> False
#testOptimize [ "AndNeg_3" ] ∀ (a b : Prop), (a ∧ b) ∧ ¬ (b ∧ a) ===> False

-- (a ∨ b) ∧ ¬ (b ∨ a) ===> False
#testOptimize [ "AndNeg_4" ] ∀ (a b : Prop), (a ∨ b) ∧ ¬ (b ∨ a) ===> False

-- ¬ a ∧ a ===> False
#testOptimize [ "AndNeg_5" ] ∀ (a : Prop), ¬ a ∧ a ===> False

-- (¬ a ∧ a) = False ===> True
#testOptimize [ "AndNeg_6" ] ∀ (a : Prop), (¬ a ∧ a) = False ===> True

-- ¬ (a ∧ b) ∧ (b ∧ a) ===> False
#testOptimize [ "AndNeg_7" ] ∀ (a b : Prop), ¬ (a ∧ b) ∧ (b ∧ a) ===> False

-- ¬ (a ∨ b) ∧ (b ∨ a) ===> True
#testOptimize [ "AndNeg_8" ] ∀ (a b : Prop), ¬ (a ∨ b) ∧ (b ∨ a) ===> False

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬ a) ===> False
#testOptimize [ "AndNeg_9"] ∀ (a b c : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬ a ===> False

-- ((¬ a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ a) ===> False
#testOptimize [ "AndNeg_10"] ∀ (a b c : Prop), (¬ a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ a ===> False


/-! Test cases to ensure that simplification rule `e ∧ ¬ e ==> False` is not applied wrongly. -/

-- ¬ a ∧ b ===> ¬ a ∧ b
-- NOTE: reordering applied on operands
#testOptimize [ "AndNegUnchanged_1" ] ∀ (a b : Prop), ¬ a ∧ b ===> ∀ (a b : Prop), b ∧ ¬ a

-- b ∧ ¬ a ===> b ∧ ¬ a
#testOptimize [ "AndNegUnchanged_2" ] ∀ (a b : Prop), b ∧ ¬ a ===> ∀ (a b : Prop), b ∧ ¬ a

-- ¬ (a ∧ b) ∧ c ===> ¬ (a ∧ b) ∧ c
-- NOTE: reordering applied on operands
#testOptimize [ "AndNegUnchanged_3" ] ∀ (a b c : Prop), ¬ (a ∧ b) ∧ c ===>
                                      ∀ (a b c : Prop), c ∧ ¬ (a ∧ b)

-- c ∧ ¬ (a ∨ b) ===> c ∧ ¬ (a ∨ b)
#testOptimize [ "AndNegUnchanged_4" ] ∀ (a b c : Prop), c ∧ ¬ (a ∨ b) ===>
                                      ∀ (a b c : Prop), c ∧ ¬ (a ∨ b)

-- (a ∧ b) ∧ ¬ (c ∧ d) ===> ¬ (c ∧ d) ∧ (a ∧ b)
#testOptimize [ "AndNegUnchanged_5" ] ∀ (a b c d : Prop), (a ∧ b) ∧ ¬ (c ∧ d) ===>
                                      ∀ (a b c d : Prop), ¬ (c ∧ d) ∧ (a ∧ b)

-- ¬ a ∧ ¬ a ===> ¬ a
#testOptimize [ "AndNegUnchanged_6" ] ∀ (a : Prop), ¬ a ∧ ¬ a ===> ∀ (a : Prop), ¬ a

-- ¬ a ∧ ¬ b ==> ¬ a ∧ ¬ b
#testOptimize [ "AndNegUnchanged_7" ] ∀ (a b : Prop), (¬ a) ∧ ¬ b ===>
                                      ∀ (a b : Prop), (¬ a) ∧ ¬ b


/-! Test cases for simplification rule `e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)`. -/

-- a ∧ a ===> a
#testOptimize [ "AndSubsumption_1" ] ∀ (a : Prop), a ∧ a ===> ∀ (a : Prop), a

-- (a ∧ a) = a ===> True
#testOptimize [ "AndSubsumption_2" ] ∀ (a : Prop), (a ∧ a) = a ===> True

-- (a ∧ b) ∧ (b ∧ a) ===> a ∧ b
#testOptimize [ "AndSubsumption_3" ] ∀ (a b : Prop), (a ∧ b) ∧ (b ∧ a) ===> ∀ (a b : Prop), a ∧ b

-- ((b ∨ b) ∧ a) ∧ (a ∧ b) ===> a ∧ b
#testOptimize [ "AndSubsumption_4" ] ∀ (a b : Prop), ((b ∨ b) ∧ a) ∧ (a ∧ b) ===> ∀ (a b : Prop), a ∧ b

-- ((b ∨ b) ∧ a) ∧ ((a ∧ a) ∧ b) ===> a ∧ b
#testOptimize [ "AndSubsumption_5" ] ∀ (a b : Prop), ((b ∨ b) ∧ a) ∧ ((a ∧ a) ∧ b) ===> ∀ (a b : Prop), a ∧ b


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
    is not applied wrongly.
     - `False ∧ e ==> False`
     - `True ∧ e ==> e`
     - `e1 ∧ e2 ==> e1 (if e1 =ₚₜᵣ e2)`
-/

-- a ∧ b ===> a ∧ b
#testOptimize [ "AndUnchanged_1"] ∀ (a b : Prop), a ∧ b ===> ∀ (a b : Prop), a ∧ b

-- (a ∧ c) ∧ (b ∨ d) ===> (a ∧ c) ∧ (b ∨ d)
#testOptimize [ "AndUnchanged_2" ] ∀ (a b c d : Prop), (a ∧ c) ∧ (b ∨ d) ===>
                                   ∀ (a b c d : Prop), (a ∧ c) ∧ (b ∨ d)


/-! Test cases for normalization rule `e1 ∧ e2 ==> e2 ∧ e1 (if e2 <ₒ e1)`. -/

-- a ∧ b = a ∧ b ===> True
#testOptimize [ "AndCommut_1" ] ∀ (a b : Prop), (a ∧ b) = (a ∧ b) ===> True

-- a ∧ b = b ∧ a ===> True
#testOptimize [ "AndCommut_2" ] ∀ (a b : Prop), (a ∧ b) = (b ∧ a) ===> True

-- b ∧ a ===> a ∧ b (when `a` declared first)
#testOptimize [ "AndCommut_3" ] ∀ (a b : Prop), b ∧ a ===> ∀ (a b : Prop), a ∧ b

-- (a ∧ (b ∧ c)) = ((c ∧ b) ∧ a) ===> True
#testOptimize [ "AndCommut_4" ] ∀ (a b c : Prop), (a ∧ (b ∧ c)) = ((c ∧ b) ∧ a) ===> True


end Test.OptimizeAnd
