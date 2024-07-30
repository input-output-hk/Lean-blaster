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

-- e ∨ False ===> e
#testOptimize [ "OrFalseRight" ] ∀ (a : Prop), a ∨ False ===> ∀ (a : Prop), a

-- False ∨ e ===> e
#testOptimize [ "OrFalseLeft" ] ∀ (a : Prop), False ∨ a ===> ∀ (a : Prop), a

-- e ∨ True ===> True
#testOptimize [ "OrTrueRight" ] ∀ (a : Prop), a ∨ True ===> True

-- True ∨ e ===> True
#testOptimize [ "OrTrueLeft" ] ∀ (a : Prop), True ∨ a ===> True

-- e ∨ ¬ e ===> True
#testOptimize [ "OrNegRight" ] ∀ (a : Prop), a ∨ ¬ a ===> True

-- ¬ e ∨ e ===> True
#testOptimize [ "OrNegLeft" ] ∀ (a : Prop), ¬ a ∨ a ===> True

-- e ∨ e ===> e
#testOptimize [ "OrSubsumption" ] ∀ (a : Prop), a ∨ a ===> ∀ (a : Prop), a

end Tests.OptimizeOr
