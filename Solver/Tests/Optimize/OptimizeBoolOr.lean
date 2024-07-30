import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolOr
/-! ## Test objectives to validate normalization and simplification rules on ``or -/

-- true || false ===> true
#testOptimize [ "BoolOrTrueFalse" ] true || false ===> true

-- false || true ===> true
#testOptimize [ "BoolOrFalseTrue" ] false || true ===> true

-- true || true ===> true
#testOptimize [ "BoolOrTrueTrue" ] true || true ===> true

-- false || false ===> false
#testOptimize [ "BoolOrFalseFalse" ] false || false ===> false

-- e || false ===> e
#testOptimize [ "BoolOrFalseRight" ] ∀ (a : Bool), (a || false) = a ===> True

-- false || e ===> false
#testOptimize [ "BoolOrFalseLeft" ] ∀ (a : Bool), (false || a) = a ===> True

-- e || true ===> true
#testOptimize [ "BoolOrTrueRight" ] ∀ (a : Bool), (a || true) = true ===> True

-- true || e ===> e
#testOptimize [ "BoolOrTrueLeft" ] ∀ (a : Bool), (true || a) = true ===> True

-- e || not e ===> true
#testOptimize [ "BoolOrNegRight" ] ∀ (a : Bool), (a || not a) = true ===> True

-- not e || e ===> true
#testOptimize [ "BoolOrNegLeft" ] ∀ (a : Bool), (not a || a) = true ===> True

-- e || e ===> e
#testOptimize [ "BoolOrSubsumption" ] ∀ (a : Bool), (a || a) = a ===> True

end Tests.OptimizeBoolOr
