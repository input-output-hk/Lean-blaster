import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeOr
/-! ## Test objectives to validate normalization and simplification rules on ``Or -/

-- True ∨ False ===> True
#testOptimize [ "OrTrueFalse" ] True ∨ False ===> True

-- False ∨ True ===> True
#testOptimize [ "OrFalseTrue" ] False ∨ True ===> True

-- True ∨ True ===> True
#testOptimize [ "OrTrueTrue" ] True ∨ True ===> True

-- False ∨ False ===> False
#testOptimize [ "OrFalseFalse" ] False ∨ False ===> False

-- a ∨ False ===> a
#testOptimize [ "OrFalseRight" ] ∀ (a : Prop), a ∨ False ===> ∀ (a : Prop), a

-- False ∨ a ===> a
#testOptimize [ "OrFalseLeft" ] ∀ (a : Prop), False ∨ a ===> ∀ (a : Prop), a

-- a ∨ True ===> True
#testOptimize [ "OrTrueRight" ] ∀ (a : Prop), a ∨ True ===> True

-- True ∨ a ===> True
#testOptimize [ "OrTrueLeft" ] ∀ (a : Prop), True ∨ a ===> True

-- a ∨ ¬ a ===> True
#testOptimize [ "OrNegRight" ] ∀ (a : Prop), a ∨ ¬ a ===> True

-- ¬ a ∨ a ===> True
#testOptimize [ "OrNegLeft" ] ∀ (a : Prop), ¬ a ∨ a ===> True

-- a ∨ a ===> a
#testOptimize [ "OrSubsumption" ] ∀ (a : Prop), a ∨ a ===> ∀ (a : Prop), a

-- a ∨ b ===> a ∨ b
#testOptimize [ "OrUnchanged_1" ] ∀ (a b : Prop), a ∨ b ===> ∀ (a b : Prop), a ∨  b

-- ¬ a ∨ b ===> ¬ a ∨ b
-- NOTE: reordering applied on operands
#testOptimize [ "OrUnchanged_2" ] ∀ (a b : Prop), (¬ a) ∨ b ===> ∀ (a b : Prop), b ∨ ¬ a

-- a ∨ ¬ b ===> a ∨ ¬ b
#testOptimize [ "OrUnchanged_3" ] ∀ (a b : Prop), a ∨ ¬ b ===> ∀ (a b : Prop), a ∨ ¬ b

end Tests.OptimizeOr
