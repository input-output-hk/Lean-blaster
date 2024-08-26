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

-- a && false ===> false
#testOptimize [ "BoolAndFalseRight" ] ∀ (a : Bool), (a && false) = false ===> True

-- false && a ===> false
#testOptimize [ "BoolAndFalseLeft" ] ∀ (a : Bool), (false && a) = false ===> True

-- a && true ===> a
#testOptimize [ "BoolAndTrueRight" ] ∀ (a : Bool), (a && true) = a ===> True

-- true && a ===> a
#testOptimize [ "BoolAndTrueLeft" ] ∀ (a : Bool), (true && a) = a ===> True

-- a && not a ===> false
#testOptimize [ "BoolAndNegRight" ] ∀ (a : Bool), (a && not a) = false ===> True

-- not a && a ===> false
#testOptimize [ "BoolAndNegLeft" ] ∀ (a : Bool), (not a && a) = false ===> True

-- a && a ===> a
#testOptimize [ "BoolAndSubsumption" ] ∀ (a : Bool), (a && a) = a ===> True

-- a && b ===> a && b
#testOptimize [ "BoolAndUnchanged_1" ] ∀ (a b : Bool), (a && b) ===> ∀ (a b : Bool), true = (a && b)

-- !a && b ===> !a && b
-- NOTE: reordering applied on operands
#testOptimize [ "BoolAndUnchanged_2" ] ∀ (a b : Bool), (!a && b) ===> ∀ (a b : Bool), true = (b && !a)

-- a && !b ===> a && !b
#testOptimize [ "BoolAndUnchanged_3" ] ∀ (a b : Bool), (a && !b) ===> ∀ (a b : Bool), true = (a && !b)


end Test.OptimizeBoolAnd
