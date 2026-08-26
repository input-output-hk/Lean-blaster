import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeIff
/-! ## Test objectives to validate the `Iff` expansion rule -/

/-! Test cases for the expansion rule `p ↔ q ==> (p → q) ∧ (q → p)`. -/

-- (p ↔ q) ===> (p → q) ∧ (q → p)
#testOptimize [ "Iff_1", proof ] ∀ (p q : Prop), (p ↔ q) ===> ∀ (p q : Prop), (p → q) ∧ (q → p)

-- (p ↔ q) = ((p → q) ∧ (q → p)) ===> True
#testOptimize [ "Iff_2", proof ] ∀ (p q : Prop), (p ↔ q) = ((p → q) ∧ (q → p)) ===> True

end Test.OptimizeIff
