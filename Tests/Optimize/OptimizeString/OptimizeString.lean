import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeString
/-! ## Test objectives to validate normalization and simplification rules on ``String -/

/-! Test cases for simplification rules:
  - `"" ++ e ==> e`
  - `e ++ "" ==> e`
-/

-- ∀ (e : String), "" ++ e = e ===> True
#testOptimize [ "StringAppend_1", proof ] ∀ (e : String), "" ++ e = e ===> True

-- ∀ (e : String), e ++ "" = e ===> True
#testOptimize [ "StringAppend_2", proof ] ∀ (e : String), e ++ "" = e ===> True

-- ∀ (t s : String), t = "" ++ s ===> ∀ (t s : String), t = s
#testOptimize [ "StringAppend_3", proof ] ∀ (t s : String), t = "" ++ s ===> ∀ (t s : String), t = s

-- ∀ (t s : String), t = s ++ "" ===> ∀ (t s : String), t = s
#testOptimize [ "StringAppend_4", proof ] ∀ (t s : String), t = s ++ "" ===> ∀ (t s : String), t = s

/-! Test cases for constant folding on `String.append` and `String.length`:
  - `S1 ++ S2 ==> S1 "++" S2`
  - `String.length S ==> "String.length" S`
-/

-- ∀ (s : String), s = "abc" ++ "de" ===> ∀ (s : String), "abcde" = s
#testOptimize [ "StringAppendCst_1", proof ]
  ∀ (s : String), s = "abc" ++ "de" ===> ∀ (s : String), "abcde" = s

-- ∀ (s : String), s = "abc" ++ "de" → s = "abcde" ===> True
#testOptimize [ "StringAppendCst_2", proof ] ∀ (s : String), s = "abc" ++ "de" → s = "abcde" ===> True

-- ∀ (n : Nat), n = String.length "abc" ===> ∀ (n : Nat), 3 = n
#testOptimize [ "StringLengthCst_1", proof ] (norm-result: 1)
  ∀ (n : Nat), n = String.length "abc" ===> ∀ (n : Nat), 3 = n

-- ∀ (n : Nat), n = String.length "abc" → n = 3 ===> True
#testOptimize [ "StringLengthCst_2", proof ] ∀ (n : Nat), n = String.length "abc" → n = 3 ===> True

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

/-! Test cases for simplification rules on `LT.lt` over String:
  - `S1 < S2 ==> S1 "<" S2`
  - `e < e ==> False`
-/

-- "abc" < "abd" ===> True
#testOptimize [ "StringLt_2", proof ] "abc" < "abd" ===> True

-- "abd" < "abc" ===> False
#testOptimize [ "StringLt_3", proof ] "abd" < "abc" ===> False

-- ∀ (b : Prop), b = ("abc" < "abd") ===> ∀ (b : Prop), b
#testOptimize [ "StringLt_4", proof ] ∀ (b : Prop), b = ("abc" < "abd") ===> ∀ (b : Prop), b

-- ∀ (b : Prop), b = ("abd" < "abc") ===> ∀ (b : Prop), ¬ b
#testOptimize [ "StringLt_5", proof ] ∀ (b : Prop), b = ("abd" < "abc") ===> ∀ (b : Prop), ¬ b

-- ∀ (s : String), ¬ (s < s) ===> True
#testOptimize [ "StringLt_6", proof ] ∀ (s : String), ¬ (s < s) ===> True

-- ∀ (s : String) (b : Prop), b = (s < s) ===> ∀ (b : Prop), ¬ b
#testOptimize [ "StringLt_7", proof ] ∀ (s : String) (b : Prop), b = (s < s) ===> ∀ (b : Prop), ¬ b

/-! Test cases for normalization rule `e1 ≤ e2 ==> ¬ (e2 < e1)` over String -/

-- "abc" ≤ "abd" ===> True
#testOptimize [ "StringLe_3", proof ] "abc" ≤ "abd" ===> True

-- ∀ (s : String), s ≤ s ===> True
#testOptimize [ "StringLe_4", proof ] ∀ (s : String), s ≤ s ===> True

-- ∀ (b : Prop), b = ("abc" ≤ "abd") ===> ∀ (b : Prop), b
#testOptimize [ "StringLe_5", proof ] ∀ (b : Prop), b = ("abc" ≤ "abd") ===> ∀ (b : Prop), b

-- ∀ (s t : String), (s ≤ t) = (t < s) ===> False
#testOptimize [ "StringLe_6", proof ] ∀ (s t : String), (s ≤ t) = (t < s) ===> False

end Tests.OptimizeString
