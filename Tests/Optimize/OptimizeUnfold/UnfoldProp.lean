import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldProp

/-! ## Test objectives to validate unfolding `Prop` operators -/


/-! Test cases to validate unfolding of `Prop` operators only when reduced to a constant value or via rewriting. -/

-- ∀ (p : Prop), False ∧ p ===> False
#testOptimize [ "UnfoldProp_1", proof ] ∀ (p : Prop), False ∧ p ===> False

-- ∀ (p : Prop), True ∧ p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldProp_2", proof ] ∀ (p : Prop), True ∧ p ===> ∀ (p : Prop), p

-- ∀ (p : Prop), ¬ p ∧ p ===> False
#testOptimize [ "UnfoldProp_3", proof ] ∀ (p : Prop), ¬ p ∧ p ===> False

-- ∀ (p : Prop), p ∧ p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldProp_4", proof ] ∀ (p : Prop), p ∧ p ===> ∀ (p : Prop), p

-- ∀ (p : Prop), False ∨ p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldProp_5", proof ] ∀ (p : Prop), False ∨ p ===> ∀ (p : Prop), p

-- ∀ (p : Prop), True ∨ p ===> True
#testOptimize [ "UnfoldProp_6", proof ] ∀ (p : Prop), True ∨ p ===> True

-- ∀ (p : Prop), ¬ p ∨ p ===> True
#testOptimize [ "UnfoldProp_7", proof ] ∀ (p : Prop), ¬ p ∨ p ===> True

-- ∀ (p : Prop), p ∨ p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldProp_8", proof ] ∀ (p : Prop), p ∨ p ===> ∀ (p : Prop), p

-- ¬ False ==> True
#testOptimize [ "UnfoldProp_9", proof ] ¬ False ===> True

-- ¬ True ==> False
#testOptimize [ "UnfoldProp_10", proof ] ¬ True ===> False

-- ∀ (p : Prop), ¬ ¬ p ===> ∀ (p : Prop), p
#testOptimize [ "UnfoldProp_11", proof ] ∀ (p : Prop), ¬ ¬ p ===> ∀ (p : Prop), p

-- ∀ (a : Bool), ¬ (true = a) ===>  ∀ (a : Bool), false = a
#testOptimize [ "UnfoldProp_12", proof ] ∀ (a : Bool), ¬ (true = a) ===>  ∀ (a : Bool), false = a

-- ∀ (a : Bool), ¬ (false = a) ===>  ∀ (a : Bool), true = a
#testOptimize [ "UnfoldProp_13", proof ] ∀ (a : Bool), ¬ (false = a) ===>  ∀ (a : Bool), true = a


/-! Test cases to validate when `Prop` operators must not be unfolded -/

-- ∀ (p q : Prop), p ∧ q ===> ∀ (p q : Prop), p ∧ q
#testOptimize [ "PropNotUnfolded_1", proof ] ∀ (p q : Prop), p ∧ q ===> ∀ (p q : Prop), p ∧ q

-- ∀ (p q : Prop), ¬ p ∧ q ===> ∀ (p q : Prop), q ∧ ¬ p
#testOptimize [ "PropNotUnfolded_2", proof ] ∀ (p q : Prop), ¬ p ∧ q ===> ∀ (p q : Prop), q ∧ ¬ p

-- ∀ (p q : Prop), p ∨ q ===> ∀ (p q : Prop), p ∨ q
#testOptimize [ "PropNotUnfolded_3", proof ] ∀ (p q : Prop), p ∨ q ===> ∀ (p q : Prop), p ∨ q

-- ∀ (p q : Prop), ¬ p ∨ q ===> ∀ (p q : Prop), q ∨ ¬ p
#testOptimize [ "PropNotUnfolded_4", proof ] ∀ (p q : Prop), ¬ p ∨ q ===> ∀ (p q : Prop), q ∨ ¬ p

-- ∀ (p : Prop), ¬ p ===> ∀ (p : Prop), ¬ p
#testOptimize [ "PropNotUnfolded_5", proof ] ∀ (p : Prop), ¬ p ===> ∀ (p : Prop), ¬ p

-- ∀ (p : Prop), ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p
#testOptimize [ "PropNotUnfolded_6", proof ] ∀ (p : Prop), ¬ (¬ (¬ p)) ===> ∀ (p : Prop), ¬ p

-- ∀ (a b : Bool), ¬ (a = b) ===>  ∀ (a : Bool), ¬ (a = b)
#testOptimize [ "PropNotUnfolded_7", proof ] ∀ (a b : Bool), ¬ (a = b) ===> ∀ (a b : Bool), ¬ (a = b)

end Tests.UnfoldProp
