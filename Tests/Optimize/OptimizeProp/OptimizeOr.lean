import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeOr
/-! ## Test objectives to validate normalization and simplification rules on ``Or -/

/-! Test cases for simplification rule `False ∨ e ==> e`. -/

-- False ∨ True ===> True
#testOptimize [ "OrFalse_1" ] False ∨ True ===> True

-- (False ∨ True) = True ===> True
#testOptimize [ "OrFalse_2", proof ] (False ∨ True) = True ===> True

-- True ∨ False ===> True
#testOptimize [ "OrFalse_3" ] True ∨ False ===> True

-- False ∨ False ===> False
#testOptimize [ "OrFalse_4", proof ] False ∨ False ===> False

-- a ∨ False ===> a
#testOptimize [ "OrFalse_5" ] ∀ (a : Prop), a ∨ False ===> ∀ (a : Prop), a

-- (a ∨ False) = a ===> True
#testOptimize [ "OrFalse_6" ] ∀ (a : Prop), (a ∨ False) = a ===> True

-- False ∨ a ===> a
#testOptimize [ "OrFalse_7", proof ] ∀ (a : Prop), False ∨ a ===> ∀ (a : Prop), a

-- False ∨ (a ∧ b) ===> a ∧ b
#testOptimize [ "OrFalse_8", proof ] ∀ (a b : Prop), False ∨ (a ∧ b) ===> ∀ (a b : Prop), a ∧ b

-- (a ∨ b) ∨ False ===> a ∨ b
#testOptimize [ "OrFalse_9" ] ∀ (a b : Prop), (a ∨ b) ∨ False ===> ∀ (a b : Prop), a ∨ b

-- (a ∨ False) ∨ b  ===> a ∨ b
#testOptimize [ "OrFalse_10" ] ∀ (a b : Prop), (a ∨ False) ∨ b ===> ∀ (a b : Prop), a ∨ b

-- (False ∨ a) ∨ b  ===> a ∨ b
#testOptimize [ "OrFalse_11", proof ] ∀ (a b : Prop), (False ∨ a) ∨ b ===> ∀ (a b : Prop), a ∨ b

-- (a ∧ False) ∨ (a ∨ b) ===> a ∨ b
#testOptimize [ "OrFalse_12" ] ∀ (a b : Prop), (a ∧ False) ∨ (a ∨ b) ===>
                               ∀ (a b : Prop), a ∨ b

-- (a ∧ False) ∨ (b ∨ ¬ b) ===> True
#testOptimize [ "OrFalse_13"] ∀ (a b : Prop), (a ∧ False) ∨ (b ∨ ¬ b) ===> True

-- (a ∧ ¬ a) ∨ (b ∧ ¬ b) ===> False
#testOptimize [ "OrFalse_14"] ∀ (a b : Prop), (a ∧ ¬ a) ∨ (b ∧ ¬ b) ===> False

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∨ ((b ∧ a) ∧ ¬(a ∧ b)) ===> False
#testOptimize [ "OrFalse_15"] ∀ (a b c : Prop), ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∧ ¬a) ∨ ((b ∧ a) ∧ ¬(a ∧ b)) ===> False

/-! Test cases for simplification rule `True ∨ e ==> True`. -/

-- True ∨ True ===> True
#testOptimize [ "OrTrue_1", proof ] True ∨ True ===> True

-- (True ∨ True) = True ===> True
#testOptimize [ "OrTrue_2", proof ] (True ∨ True) = True ===> True

-- a ∨ True ===> True
#testOptimize [ "OrTrue_3" ] ∀ (a : Prop), a ∨ True ===> True

-- (a ∨ True) = True ===> True
#testOptimize [ "OrTrue_4" ] ∀ (a : Prop), (a ∨ True) = True ===> True

-- True ∨ a ===> True
#testOptimize [ "OrTrue_5", proof ] ∀ (a : Prop), True ∨ a ===> True

-- True ∨ (a ∧ b) ===> True
#testOptimize [ "OrTrue_6", proof ] ∀ (a b : Prop), True ∨ (a ∧ b) ===> True

-- (a ∨ b) ∨ True ===> True
#testOptimize [ "OrTrue_7" ] ∀ (a b : Prop), (a ∨ b) ∨ True ===> True

-- (a ∨ True) ∨ b  ===> True
#testOptimize [ "OrTrue_8" ] ∀ (a b : Prop), (a ∨ True) ∨ b ===> True

-- (True ∨ a) ∨ b ===> True
#testOptimize [ "OrTrue_9" ] ∀ (a b : Prop), (True ∨ a) ∨ b ===> True

-- (a ∨ True) ∨ (a ∨ b) ===> True
#testOptimize [ "OrTrue_10" ] ∀ (a b : Prop), (a ∨ True) ∨ (a ∨ b) ===> True

-- (a ∧ b) ∨ (b ∨ ¬ b) ===> True
#testOptimize [ "OrTrue_11"] ∀ (a b : Prop), (a ∧ b) ∨ (b ∨ ¬ b) ===> True

-- (a ∨ ¬ a) ∨ (b ∧ ¬ b) ===> True
#testOptimize [ "OrTrue_12"] ∀ (a b : Prop), (a ∨ ¬ a) ∨ (b ∧ ¬ b) ===> True

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∨ ((b ∧ a) ∧ c)) ===> True
#testOptimize [ "OrTrue_13"] ∀ (a b c : Prop), ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ∨ ((b ∧ a) ∧ c) ===> True


/-! Test cases for simplification rule `e ∨ ¬ e ==> True`. -/

-- a ∨ ¬ a ===> True
#testOptimize [ "OrNeg_1", proof ] ∀ (a : Prop), a ∨ ¬ a ===> True

-- (a ∨ ¬ a) = True ===> True
#testOptimize [ "OrNeg_2", proof ] ∀ (a : Prop), (a ∨ ¬ a) = True ===> True

-- (a ∧ b) ∨ ¬ (b ∧ a) ===> True
#testOptimize [ "OrNeg_3" ] ∀ (a b : Prop), (a ∧ b) ∨ ¬ (b ∧ a) ===> True

-- (a ∨ b) ∨ ¬ (b ∨ a) ===> True
#testOptimize [ "OrNeg_4" ] ∀ (a b : Prop), (a ∨ b) ∨ ¬ (b ∨ a) ===> True

-- ¬ a ∨ a ===> True
#testOptimize [ "OrNeg_5" ] ∀ (a : Prop), ¬ a ∨ a ===> True

-- (¬ a ∨ a) = True ===> True
#testOptimize [ "OrNeg_6" ] ∀ (a : Prop), (¬ a ∨ a) = True ===> True

-- ¬ (a ∧ b) ∨ (b ∧ a) ===> True
#testOptimize [ "OrNeg_7" ] ∀ (a b : Prop), ¬ (a ∧ b) ∨ (b ∧ a) ===> True

-- ¬ (a ∨ b) ∨ (b ∨ a) ===> True
#testOptimize [ "OrNeg_8" ] ∀ (a b : Prop), ¬ (a ∨ b) ∨ (b ∨ a) ===> True

-- ((a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a) ===> True
#testOptimize [ "OrNeg_9"] ∀ (a b c : Prop), (a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ ¬a ===> True

-- ((¬ a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ a) ===> True
#testOptimize [ "OrNeg_10"] ∀ (a b c : Prop), (¬ a ∨ ((b ∨ c) ∧ ¬(c ∨ b))) ∨ a ===> True


/-! Test cases to ensure that simplification rule `e ∨ ¬ e ==> True` is not applied wrongly. -/

-- ¬ a ∨ b ===> ¬ a ∨ b
-- NOTE: reordering applied on operands
#testOptimize [ "OrNegUnchanged_1" ] ∀ (a b : Prop), ¬ a ∨ b ===> ∀ (a b : Prop), b ∨ ¬ a

-- b ∨ ¬ a ===> b ∨ ¬ a
#testOptimize [ "OrNegUnchanged_2" ] ∀ (a b : Prop), b ∨ ¬ a ===> ∀ (a b : Prop), b ∨ ¬ a

-- ¬ (a ∧ b) ∨ c ===> ¬ (a ∧ b) ∨ c
-- NOTE: reordering applied on operands
#testOptimize [ "OrNegUnchanged_3" ] ∀ (a b c : Prop), ¬ (a ∧ b) ∨ c ===>
                                     ∀ (a b c : Prop), c ∨ ¬ (a ∧ b)

-- c ∨ ¬ (a ∨ b) ===> c ∨ ¬ (a ∨ b)
#testOptimize [ "OrNegUnchanged_4" ] ∀ (a b c : Prop), c ∨ ¬ (a ∨ b) ===>
                                     ∀ (a b c : Prop), c ∨ ¬ (a ∨ b)

-- (a ∧ b) ∨ ¬ (c ∧ d) ===> (a ∧ b) ∨ ¬ (c ∧ d)
-- NOTE: reordering applied on operands
#testOptimize [ "OrNegUnchanged_5" ] ∀ (a b c d : Prop), (a ∧ b) ∨ ¬ (c ∧ d) ===>
                                     ∀ (a b c d : Prop), ¬ (c ∧ d) ∨ (a ∧ b)

-- ¬ a ∨ ¬ a ===> ¬
#testOptimize [ "OrNegUnchanged_6" ] ∀ (a : Prop), ¬ a ∨ ¬ a ===> ∀ (a : Prop), ¬ a

-- ¬ a ∨ ¬ b ==> ¬ a ∨ ¬ b
#testOptimize [ "OrNegUnchanged_7" ] ∀ (a b : Prop), (¬ a) ∨ ¬ b ===>
                                     ∀ (a b : Prop), (¬ a) ∨ ¬ b



/-! Test cases for simplification rule `true = e ∨ false = e ==> True`. -/

-- ∀ (a : Bool), true = a ∨ false = a ===> True
#testOptimize [ "OrNegBoolEq_1", proof ] ∀ (a : Bool), true = a ∨ false = a ===> True

-- ∀ (a : Bool), true = a ∨ a = false ===> True
#testOptimize [ "OrNegBoolEq_2" ] ∀ (a : Bool), true = a ∨ a = false ===> True

-- ∀ (a : Bool), a = true ∨ a = false ===> True
#testOptimize [ "OrNegBoolEq_3" ] ∀ (a : Bool), a = true ∨ a = false ===> True

-- ∀ (a : Bool), a = false ∨ a = true ===> True
#testOptimize [ "OrNegBoolEq_4" ] ∀ (a : Bool), a = false ∨ a = true ===> True

-- ∀ (a b c : Bool), c = ((a && b) && !(b && a)) ∨ c = true ===> True
#testOptimize [ "OrNegBoolEq_5" ]
  ∀ (a b c : Bool), c = ((a && b) && !(b && a)) ∨ c = true ===> True

-- ∀ (a b c : Bool), c = ((a && b) && !(b && a)) ∨ c = true ===> True
#testOptimize [ "OrNegBoolEq_6" ]
  ∀ (a b c : Bool), c = ((a && b) && !(b && a)) ∨ c = (b || !b) ===> True



/-! Test cases to ensure that simplification rule `true = e ∨ false = e ==> True`
    is not wrongly applied.
-/

-- ∀ (a b : Bool), true = a ∨ false = b ===> ∀ (a b : Bool), true = (a || !b)
#testOptimize [ "OrNegBoolEqUnchanged_1" ]
  ∀ (a b : Bool), true = a ∨ false = b ===> ∀ (a b : Bool), true = (a || !b)

-- ∀ (a b : Bool), true = a ∨ b = false ===> ∀ (a b : Bool), true = (a || !b)
#testOptimize [ "OrNegBoolEqUnchanged_2" ]
  ∀ (a b : Bool), true = a ∨ b = false ===> ∀ (a b : Bool), true = (a || !b)

-- ∀ (a b c : Bool), c = ((a && b) && (b && a)) ∨ c = true ===>
-- ∀ (a b c : Bool), c = (a && b) ∨ true = c
#testOptimize [ "OrNegBoolEqUnchanged_3" ]
  ∀ (a b c : Bool), c = ((a && b) && (b && a)) ∨ c = true ===>
  ∀ (a b c : Bool), c = (a && b) ∨ true = c



/-! Test cases for simplification rule `e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)`. -/

-- a ∨ a ===> a
#testOptimize [ "OrSubsumption_1", proof ] ∀ (a : Prop), a ∨ a ===> ∀ (a : Prop), a

-- (a ∨ a) = a ===> True
#testOptimize [ "OrSubsumption_2", proof ] ∀ (a : Prop), (a ∨ a) = a ===> True


-- (a ∧ b) ∨ (b ∧ a) ===> a ∧ b
#testOptimize [ "OrSubsumption_3" ] ∀ (a b : Prop), (a ∧ b) ∨ (b ∧ a) ===> ∀ (a b : Prop), a ∧ b

-- ((b ∨ b) ∧ a) ∨ (a ∧ b) ===> a ∧ b
#testOptimize [ "OrSubsumption_4" ] ∀ (a b : Prop), ((b ∨ b) ∧ a) ∨ (a ∧ b) ===> ∀ (a b : Prop), a ∧ b

-- ((b ∨ b) ∧ a) ∨ ((a ∧ a) ∧ b) ===> a ∧ b
#testOptimize [ "OrSubsumption_5" ] ∀ (a b : Prop), ((b ∨ b) ∧ a) ∨ ((a ∧ a) ∧ b) ===> ∀ (a b : Prop), a ∧ b


/-! Test cases to ensure that the following simplification rules are not applied wrongly:
     - `False ∨ e ==> e`
     - `True ∨ e ==> True`
     - `e1 ∨ e2 ==> e1 (if e1 =ₚₜᵣ e2)`
-/

-- a ∨ b ===> a ∨ b
#testOptimize [ "OrUnchanged_1" ] ∀ (a b : Prop), a ∨ b ===> ∀ (a b : Prop), a ∨  b

-- (a ∧ c) ∨ (b ∨ d) ===> (a ∧ c) ∨ (b ∨ d)
#testOptimize [ "OrUnchanged_2" ] ∀ (a b c d : Prop), (a ∧ c) ∨ (b ∨ d) ===>
                                  ∀ (a b c d : Prop), (a ∧ c) ∨ (b ∨ d)


/-! Test cases for normalization rule `e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1)`. -/

-- a ∨ b = a ∨ b ===> True
#testOptimize [ "OrCommut_1" ] ∀ (a b : Prop), (a ∨ b) = (a ∨ b) ===> True

-- a ∨ b = b ∨ a ===> True
#testOptimize [ "OrCommut_2" ] ∀ (a b : Prop), (a ∨ b) = (b ∨ a) ===> True

-- b ∨ a ===> a ∨ b (when `a` declared first)
#testOptimize [ "OrCommut_3" ] ∀ (a b : Prop), b ∨ a ===> ∀ (a b : Prop), a ∨ b

-- (a ∨ (b ∨ c)) = ((c ∨ b) ∨ a) ===> True
#testOptimize [ "OrCommut_4" ] ∀ (a b c : Prop), (a ∨ (b ∨ c)) = ((c ∨ b) ∨ a) ===> True


/-! Test cases for the implicative reductions on `Or`:
     - `e1 ∨ (e1 → e2) ==> True`
     - `e1 ∨ (e2 → e1) ==> (e2 → e1)`
-/

-- a ∨ (a → b) ===> True
#testOptimize [ "OrImplies_1", proof ] ∀ (a b : Prop), a ∨ (a → b) ===> True

-- a ∨ (b → a) ===> (b → a)
#testOptimize [ "OrImplies_2", proof ] ∀ (a b : Prop), a ∨ (b → a) ===> ∀ (a b : Prop), (b → a)


/-! Test cases for the hypothesis-context reductions on `Or`:
     - `e1 ∨ e2 ==> True (if e1 holds in the hypothesis context)`
     - `e1 ∨ e2 ==> True (if e2 holds in the hypothesis context)`
     - `e1 ∨ e2 ==> e2 (if ¬ e1 holds in the hypothesis context)`
     - `e1 ∨ e2 ==> e1 (if ¬ e2 holds in the hypothesis context)`
-/

-- a → (a ∨ b)
#testOptimize [ "OrHyp_1", proof ] ∀ (a b : Prop), a → (a ∨ b) ===> True

-- b → (a ∨ b)
#testOptimize [ "OrHyp_2", proof ] ∀ (a b : Prop), b → (a ∨ b) ===> True

-- ¬ a → (a ∨ b) = b
#testOptimize [ "OrHyp_3", proof ] ∀ (a b : Prop), ¬ a → (a ∨ b) = b ===> True

-- ¬ b → (a ∨ b) = a
#testOptimize [ "OrHyp_4", proof ] ∀ (a b : Prop), ¬ b → (a ∨ b) = a ===> True


/-! Test case for the commutative reorder on `Or`: e1 ∨ e2 ==> e2 ∨ e1 (if e2 <ₒ e1). -/

-- b ∨ a ===> a ∨ b
#testOptimize [ "OrReorder_1", proof ] ∀ (a b : Prop), b ∨ a ===> ∀ (a b : Prop), a ∨ b


end Tests.OptimizeOr
