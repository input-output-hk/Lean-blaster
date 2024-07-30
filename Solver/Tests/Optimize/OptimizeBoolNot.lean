import Lean
import Solver.Optimize.Basic
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeBoolNot
/-! ## Test objectives to validate normalization and simplification rules on ``not -/

-- not false ===> true
#testOptimize [ "BoolNotFalseOne" ] not false ===> true

-- ! false ===> true
#testOptimize [ "BoolNotFalseTwo" ] ! false ===> true

-- not true ===> false
#testOptimize [ "BoolNotTrueOne" ] not true ===> false

-- ! true ===> false
#testOptimize [ "BoolNotTrueTwo" ] ! true ===> false

-- not (not e) ===> e
#testOptimize [ "BoolNotBoolNotOne" ] ∀ (a : Bool), not (not a) = a ===> True

-- not (not (not e)) ===> not e
#testOptimize [ "BoolNotBoolNotTwo" ] ∀ (a : Bool), not (not (not a)) = not a ===> True

-- not (not (not (not e))) ===> e
#testOptimize [ "BoolNotBoolNotThree" ] ∀ (a : Bool), not (not (not (not a))) = a ===> True

-- ! (! e) ===> e
#testOptimize [ "BoolNotBoolNotFour" ] ∀ (a : Bool), (! (! a)) = a ===> True

-- ! (! (! e)) ===> ! e
#testOptimize [ "BoolNotBoolNotFive" ] ∀ (a : Bool), (! (! (! a))) = (! a) ===> True

-- ! (! (! (! e))) ===> e
#testOptimize [ "BoolNotBoolNotSix" ] ∀ (a : Bool), (! (! (! (! a)))) = a ===> True


end Tests.OptimizeBoolNot
