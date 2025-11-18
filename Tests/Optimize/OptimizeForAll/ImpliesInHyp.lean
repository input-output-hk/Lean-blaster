import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ImpliesInHyp
/-! ## Test objectives to validate simplification rule
      - e1 → e2 ==> True (if ∃ e1 → e2 := _ ∈ hypothesisContext.hypothesisMap)
-/

/-! Test cases to ensure that the rule is properly applied. -/

-- ∀ (a b : Prop), (a → b) → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_1" ]
  ∀ (a b : Prop), (a → b) → (a → b) ===> True

-- ∀ (a b c : Prop), (a → b) ∧ c → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_2" ]
  ∀ (a b c : Prop), (a → b) ∧ c → (a → b) ===> True

-- ∀ (a b c : Prop), c ∧ (a → b) → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_3" ]
  ∀ (a b c : Prop), c ∧ (a → b) → (a → b) ===> True

-- ∀ (a b c d : Prop), c ∧ d ∧ (a → b) → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_4" ]
  ∀ (a b c d : Prop), c ∧ d ∧ (a → b) → (a → b) ===> True

-- ∀ (a b c d : Prop), c ∧ (a → b) ∧ d → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_5" ]
  ∀ (a b c d : Prop), c ∧ (a → b) ∧ d → (a → b) ===> True

-- (∀ (c d : Prop), c → d) → ∀ (a b : Prop), a → b ===> True
#testOptimize [ "ImpliesInHyp_6" ]
  (∀ (c d : Prop), c → d) → ∀ (a b : Prop), a → b ===> True

-- ∀ (c : Bool) (a b : Prop), (if c then a else b) → (true = c → a) ===> True
#testOptimize [ "ImpliesInHyp_7" ]
 ∀ (c : Bool) (a b : Prop), (if c then a else b) → (true = c → a) ===> True

-- ∀ (c : Bool) (a b : Prop), (if c then a else b) → (false = c → b) ===> True
#testOptimize [ "ImpliesInHyp_8" ]
 ∀ (c : Bool) (a b : Prop), (if c then a else b) → (false = c → b) ===> True

-- ∀ (c : Bool) (a b : Prop), (if c then a else b) → (true = c → a) ∧ (false = c → b) ===> True
#testOptimize [ "ImpliesInHyp_9" ]
 ∀ (c : Bool) (a b : Prop), (if c then a else b) → (true = c → a) ∧ (false = c → b) ===> True

 -- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
 --   (if h : c then f h a else b) → ∀ (h : c), f h a ===> True
#testOptimize [ "ImpliesInHyp_10" ]
 ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
   (if h : c then f h a else b) → ∀ (h : c), f h a ===> True

-- ∀ (c : Bool) (a b : Prop) (g : ¬ c → Prop → Prop),
--   (if h : c then a else g h b) → ∀ (h : ¬ c), g h b ===> True
#testOptimize [ "ImpliesInHyp_11" ]
 ∀ (c : Bool) (a b : Prop) (g : ¬ c → Prop → Prop),
   (if h : c then a else g h b) → ∀ (h : ¬ c), g h b ===> True

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
--   (if h : c then f h a else b) → ∀ (h : c), f h a ∧ (false = c → b) ===> True
#testOptimize [ "ImpliesInHyp_12" ]
 ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop),
   (if h : c then f h a else b) → ∀ (h : c), f h a ∧ (false = c → b) ===> True

-- ∀ (c : Bool) (a b : Prop) (g : ¬ c → Prop → Prop),
--   (if h : c then a else g h b) → (true = c → a) ∧ ∀ (h : ¬ c), g h b ===> True
#testOptimize [ "ImpliesInHyp_13" ]
 ∀ (c : Bool) (a b : Prop) (g : ¬ c → Prop → Prop),
   (if h : c then a else g h b) → (true = c → a) ∧ ∀ (h : ¬ c), g h b ===> True

-- ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop) (g : ¬ c → Prop → Prop),
--   (if h : c then f h a else g h b) → ∀ (h : c), f h a ∧ ∀ (h : ¬ c), g h b ===> True
#testOptimize [ "ImpliesInHyp_14" ]
 ∀ (c : Bool) (a b : Prop) (f : c → Prop → Prop) (g : ¬ c → Prop → Prop),
   (if h : c then f h a else g h b) → ∀ (h : c), f h a ∧ ∀ (h : ¬ c), g h b ===> True


-- ∀ (a b c : Prop), (a → b) → (a → c) → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_15" ]
  ∀ (a b c : Prop), (a → b) → (a → c) → (a → b) ===> True

-- ∀ (a b c d : Prop), (a → b) → (b → c) → (c → d) → (a → b) ===> True
#testOptimize [ "ImpliesInHyp_16" ]
  ∀ (a b c d : Prop), (a → b) → (b → c) → (c → d) → (a → b) ===> True

-- ∀ (p q : Prop), (∀ (c d : Prop), c → d) → (p → q) → ∀ (a b : Prop), a → b ===> True
#testOptimize [ "ImpliesInHyp_17" ]
  ∀ (p q : Prop), (∀ (c d : Prop), c → d) → (p → q) → ∀ (a b : Prop), a → b ===> True


/-! Test cases to ensure that the rule is not properly applied. -/

-- ∀ (a b c : Prop), (a → c) → (a → b) ===>
-- ∀ (a b c : Prop), (a → c) → (a → b)
#testOptimize [ "ImpliesInHypUnchanged_1" ]
  ∀ (a b c : Prop), (a → c) → (a → b) ===>
  ∀ (a b c : Prop), (a → c) → (a → b)

-- ∀ (a b c : Prop), (a → c) ∧ a → (a → b) ===>
-- ∀ (a b c : Prop), (a ∧ c) → b
#testOptimize [ "ImpliesInHypUnchanged_2" ]
  ∀ (a b c : Prop), (a → c) ∧ a → (a → b) ===>
  ∀ (a b c : Prop), (a ∧ c) → b

-- ∀ (a b c d : Prop), d ∧ (a → c) → (a → b) ===>
-- ∀ (a b c d : Prop), d ∧ (a → c) → (a → b) ===>
#testOptimize [ "ImpliesInHypUnchanged_3" ]
  ∀ (a b c d : Prop), d ∧ (a → c) → (a → b) ===>
  ∀ (a b c d : Prop), d ∧ (a → c) → (a → b)

-- ∀ (c : Bool) (a b d : Prop), (if c then a else b) → (true = c → d) ===>
-- ∀ (c : Bool) (a b d : Prop), (false = c → b) ∧ (true = c → a) → (true = c → d)
#testOptimize [ "ImpliesInHypUnchanged_4" ]
 ∀ (c : Bool) (a b d : Prop), (if c then a else b) → (true = c → d) ===>
 ∀ (c : Bool) (a b d : Prop), (false = c → b) ∧ (true = c → a) → (true = c → d)

-- ∀ (c : Bool) (a b d : Prop), (if c then a else d) → (false = c → b) ===>
-- ∀ (c : Bool) (a b d : Prop), (false = c → d) ∧ (true = c → a) → (false = c → b)
#testOptimize [ "ImpliesInHypUnchanged_5" ]
 ∀ (c : Bool) (a b d : Prop), (if c then a else d) → (false = c → b) ===>
 ∀ (c : Bool) (a b d : Prop), (false = c → d) ∧ (true = c → a) → (false = c → b)

-- ∀ (c : Bool) (a b d : Prop), (if c then a else d) → (true = c → a) ∧ (false = c → b) ===>
-- ∀ (c : Bool) (a b d : Prop), (false = c → d) ∧ (true = c → a) → (false = c → b)
#testOptimize [ "ImpliesInHypUnchanged_6" ]
 ∀ (c : Bool) (a b d : Prop), (if c then a else d) → (true = c → a) ∧ (false = c → b) ===>
 ∀ (c : Bool) (a b d : Prop), (false = c → d) ∧ (true = c → a) → (false = c → b)


-- ∀ (c : Bool) (a b d : Prop) (f : c → Prop → Prop),
--   (if h : c then f h d else b) → ∀ (h : c), f h a ===>
-- ∀ (c : Bool) (a b d : Prop) (f : true = c → Prop → Prop),
--   ((false = c → b) ∧ ∀ (h : true = c), f h d) → ∀ (h : true = c), f h a
#testOptimize [ "ImpliesInHypUnchanged_7" ]
 ∀ (c : Bool) (a b d : Prop) (f : c → Prop → Prop),
   (if h : c then f h d else b) → ∀ (h : c), f h a ===>
 ∀ (c : Bool) (a b d : Prop) (f : true = c → Prop → Prop),
   ((false = c → b) ∧ ∀ (h : true = c), f h d) → ∀ (h : true = c), f h a

-- ∀ (c : Bool) (a b d : Prop) (g : ¬ c → Prop → Prop),
--   (if h : c then a else g h d) → ∀ (h : ¬ c), g h b ===>
-- ∀ (c : Bool) (a b d : Prop) (g : false = c → Prop → Prop),
--   (∀ (h : false = c), g h d) ∧ (true = c → a) → ∀ (h : false = c), g h b
#testOptimize [ "ImpliesInHypUnchanged_8" ]
 ∀ (c : Bool) (a b d : Prop) (g : ¬ c → Prop → Prop),
   (if h : c then a else g h d) → ∀ (h : ¬ c), g h b ===>
 ∀ (c : Bool) (a b d : Prop) (g : false = c → Prop → Prop),
   (∀ (h : false = c), g h d) ∧ (true = c → a) → ∀ (h : false = c), g h b

end Test.ImpliesInHyp
