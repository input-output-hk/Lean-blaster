import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeString
/-! ## Test objectives to validate normalization and simplification rules on ``String -/

/-! Test cases for simplification rules:
  - `"" ++ e ==> e`
  - `e ++ "" ==> e`
-/

-- ∀ (e: String), "" ++ e = e ===> True
#testOptimize [ "StringAppend_1", proof ] ∀ (e : String), "" ++ e = e ===> True

-- ∀ (e: String), e ++ "" = e ===> True
#testOptimize [ "StringAppend_2", proof ] ∀ (e : String), e ++ "" = e ===> True

/-! Test cases for normalization on `String.mk` -/
-- String.mk ['a', 'b', 'c'] = "abc" ===> True
#testOptimize [ "StringMk_1", proof ] String.mk ['a', 'b', 'c'] = "abc" ===> True

-- String.mk ['a', 'b', 'c'] ===> "abc"
#testOptimize [ "StringMk_2", proof ] String.mk ['a', 'b', 'c']  ===> "abc"

/-! Test cases for order relations over String -/

-- ∀ (s t : String), (s ≤ t) = (¬ (t < s)) ===> True
#testOptimize [ "StringLe_1", proof ] ∀ (s t : String), (s ≤ t) = (¬ (t < s)) ===> True

-- ∀ (s t : String), (s ≤ t) = (s ≤ t) ===> True
#testOptimize [ "StringLe_2", proof ] ∀ (s t : String), (s ≤ t) = (s ≤ t) ===> True

-- ∀ (s t : String), (s < t) = (s < t) ===> True
#testOptimize [ "StringLt_1", proof ] ∀ (s t : String), (s < t) = (s < t) ===> True

-- ∀ (s t : String), (s ≥ t) = (t ≤ s) ===> True
#testOptimize [ "StringGe_1", proof ] ∀ (s t : String), (s ≥ t) = (t ≤ s) ===> True

-- ∀ (s t : String), (s > t) = (t < s) ===> True
#testOptimize [ "StringGt_1", proof ] ∀ (s t : String), (s > t) = (t < s) ===> True

end Tests.OptimizeString
