import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeAnd
/-! ## Test objectives to validate normalization and simplification rules on ``And -/

-- True ∧ False ===> False
#testOptimize [ "AndTrueFalse" ] True ∧ False ===> False

-- False ∧ True ===> False
#testOptimize [ "AndFalseTrue" ] False ∧ True ===> False

-- True ∧ True ===> True
#testOptimize [ "AndTrueTrue" ] True ∧ True ===> True

-- False ∧ False ===> False
#testOptimize [ "AndFalseFalse" ] False ∧ False ===> False

-- a ∧ False ===> False
#testOptimize [ "AndFalseRight" ] ∀ (a : Prop), a ∧ False ===> False

-- False ∧ a ===> False
#testOptimize [ "AndFalseLeft" ] ∀ (a : Prop), False ∧ a ===> False

-- a ∧ True ===> a
#testOptimize [ "AndTrueRight" ] ∀ (a : Prop), a ∧ True ===> ∀ (a : Prop), a

-- True ∧ a ===> a
#testOptimize [ "AndTrueLeft" ] ∀ (a : Prop), True ∧ a ===> ∀ (a : Prop), a

-- a ∧ ¬ a ===> False
#testOptimize [ "AndNegRight" ] ∀ (a : Prop), a ∧ ¬ a ===> False

-- ¬ a ∧ a ===> False
#testOptimize [ "AndNegLeft" ] ∀ (a : Prop), ¬ a ∧ a ===> False

-- a ∧ a ===> a
#testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ===> ∀ (a : Prop), a

-- a ∧ b ===> a ∧ b
#testOptimize [ "AndUnchanged_1"] ∀ (a b : Prop), a ∧ b ===> ∀ (a b : Prop), a ∧ b

-- ¬ a ∧ b ===> ¬ a ∧ b
-- NOTE: reordering applied on operands
#testOptimize [ "AndUnchanged_2"] ∀ (a b : Prop), (¬ a) ∧ b ===> ∀ (a b : Prop), b ∧ ¬ a

-- a ∧ ¬ b ===> a ∧ ¬ b
#testOptimize [ "AndUnchanged_3"] ∀ (a b : Prop), a ∧ ¬ b ===> ∀ (a b : Prop), a ∧ ¬ b


end Test.OptimizeAnd
