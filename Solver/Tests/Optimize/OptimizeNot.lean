import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeNot
/-! ## Test objectives to validate normalization and simplification rules on ``Not -/

-- ¬ False ===> True
#testOptimize [ "NotFalse" ] ¬ False ===> True

-- ¬ True ===> False
#testOptimize [ "NotTrue" ] ¬ True ===> False

-- ¬ (¬ e) ===> e
#testOptimize [ "NotNotOne" ] ∀ (a : Prop), ¬ (¬ a) ===> ∀ (a : Prop), a

-- ¬ (¬ (¬ e)) ===> ¬ e
#testOptimize [ "NotNotTwo" ] ∀ (a : Prop), ¬ (¬ (¬ a)) ===> ∀ (a : Prop), ¬ a

-- ¬ (¬ (¬ (¬ e))) ===> e
#testOptimize [ "NotNotThree" ] ∀ (a : Prop), ¬ (¬ (¬ (¬ a))) ===> ∀ (a : Prop), a


end Tests.OptimizeNot
