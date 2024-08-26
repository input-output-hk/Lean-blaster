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

-- a || false ===> a
#testOptimize [ "BoolOrFalseRight" ] ∀ (a : Bool), (a || false) = a ===> True

-- false || a ===> false
#testOptimize [ "BoolOrFalseLeft" ] ∀ (a : Bool), (false || a) = a ===> True

-- a || true ===> true
#testOptimize [ "BoolOrTrueRight" ] ∀ (a : Bool), (a || true) = true ===> True

-- true || a ===> e
#testOptimize [ "BoolOrTrueLeft" ] ∀ (a : Bool), (true || a) = true ===> True

-- a || not a ===> true
#testOptimize [ "BoolOrNegRight" ] ∀ (a : Bool), (a || not a) = true ===> True

-- not a || a ===> true
#testOptimize [ "BoolOrNegLeft" ] ∀ (a : Bool), (not a || a) = true ===> True

-- a || a ===> a
#testOptimize [ "BoolOrSubsumption" ] ∀ (a : Bool), (a || a) = a ===> True

-- a || b ===> a || b
#testOptimize [ "BoolOrUnchanged_1" ] ∀ (a b : Bool), (a || b) ===> ∀ (a b : Bool), true = (a || b)

-- !a || b ===> !a || b
-- NOTE: reordering applied on operands
#testOptimize [ "BoolOrUnchanged_2" ] ∀ (a b : Bool), (!a || b) ===> ∀ (a b : Bool), true = (b || !a)

-- a || !b ===> a || !b
#testOptimize [ "BoolOrUnchanged_3" ] ∀ (a b : Bool), (a || !b) ===> ∀ (a b : Bool), true = (a || !b)

end Tests.OptimizeBoolOr
