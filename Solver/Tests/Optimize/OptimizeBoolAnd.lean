import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeBoolAnd
/-! ## Test objectives to validate normalization and simplification rules on ``and -/

-- true && false ===> false
#testOptimize [ "BoolAndTrueFalse" ] true && false ===> false

-- false && true ===> false
#testOptimize [ "BoolAndFalseTrue" ] false && true ===> false

-- true && true ===> true
#testOptimize [ "BoolAndTrueTrue" ] true && true ===> true

-- false && false ===> false
#testOptimize [ "BoolAndFalseFalse" ] false && false ===> false

-- e && false ===> false
#testOptimize [ "BoolAndFalseRight" ] ∀ (a : Bool), (a && false) = false ===> True

-- false && e ===> false
#testOptimize [ "BoolAndFalseLeft" ] ∀ (a : Bool), (false && a) = false ===> True

-- e && true ===> e
#testOptimize [ "BoolAndTrueRight" ] ∀ (a : Bool), (a && true) = a ===> True

-- true && e ===> e
#testOptimize [ "BoolAndTrueLeft" ] ∀ (a : Bool), (true && a) = a ===> True

-- e && not e ===> false
#testOptimize [ "BoolAndNegRight" ] ∀ (a : Bool), (a && not a) = false ===> True

-- not e && e ===> false
#testOptimize [ "BoolAndNegLeft" ] ∀ (a : Bool), (not a && a) = false ===> True

-- e && e ===> e
#testOptimize [ "BoolAndSubsumption" ] ∀ (a : Bool), (a && a) = a ===> True

end Test.OptimizeBoolAnd
