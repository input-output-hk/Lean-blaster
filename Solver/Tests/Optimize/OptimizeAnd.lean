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

-- e ∧ False ===> False
#testOptimize [ "AndFalseRight" ] ∀ (a : Prop), a ∧ False ===> False

-- False ∧ e ===> False
#testOptimize [ "AndFalseLeft" ] ∀ (a : Prop), False ∧ a ===> False

-- e ∧ True ===> e
#testOptimize [ "AndTrueRight" ] ∀ (a : Prop), a ∧ True ===> ∀ (a : Prop), a

-- True ∧ e ===> e
#testOptimize [ "AndTrueLeft" ] ∀ (a : Prop), True ∧ a ===> ∀ (a : Prop), a

-- e ∧ ¬ e ===> False
#testOptimize [ "AndNegRight" ] ∀ (a : Prop), a ∧ ¬ a ===> False

-- ¬ e ∧ e ===> False
#testOptimize [ "AndNegLeft" ] ∀ (a : Prop), ¬ a ∧ a ===> False

-- e ∧ e ===> e
#testOptimize [ "AndSubsumption" ] ∀ (a : Prop), a ∧ a ===> ∀ (a : Prop), a

end Test.OptimizeAnd
