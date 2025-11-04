import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ReduceITE

/-! ## Test objectives to validate reduction rules on `ite` -/

/-! Test cases for reduction rule `if c then (if c then e1 else e2) else e3 ==> if c then e1 else e3`. -/

-- ∀ (c : Bool) (x y z : Int), (if c then (if c then x else y) else z) < x ===>
-- ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x
#testOptimize [ "ReduceThenITE_1" ]
  ∀ (c : Bool) (x y z : Int), (if c then (if c then x else y) else z) < x ===>
  ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x

-- ∀ (c : Bool) (x y z : Int), (if c then (if c then (if c then x else z) else y) else z) < x ===>
-- ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x
#testOptimize [ "ReduceThenITE_2" ]
  ∀ (c : Bool) (x y z : Int), (if c then (if c then (if c then x else z) else y) else z) < x ===>
  ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x

-- ∀ (c : Bool) (x y z : Int),
-- (if c then (if c then x else y) else z) = (if true = c then x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenITE_3" ]
  ∀ (c : Bool) (x y z : Int),
   (if c then (if c then x else y) else z) = (if true = c then x else z) ===> True

-- ∀ (c : Bool) (x y z : Int),
--  (if c then (if c then (if c then x else z) else y) else z) =
--  (if true = c then x else z) < x ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenITE_4" ]
  ∀ (c : Bool) (x y z : Int),
    (if c then (if c then (if c then x else z) else y) else z) =
    (if true = c then x else z) ===> True


/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
     - `if c then (if c then e1 else e2) else e3 ==> if c then e1 else e3`
-/

-- ∀ (c d : Bool) (x y z : Int), (if c then (if d then x else y) else z) < x ===>
-- ∀ (c d : Bool) (x y z : Int), (if true = c then (if true = d then x else y) else z) < x
#testOptimize [ "ReduceThenITEUnchanged_1" ]
  ∀ (c d : Bool) (x y z : Int), (if c then (if d then x else y) else z) < x ===>
  ∀ (c d : Bool) (x y z : Int), (if true = c then (if true = d then x else y) else z) < x

-- ∀ (c d e : Bool) (x y z : Int),
--  (if c then (if d then (if e then x else z) else y) else z) < x ===>
-- ∀ (c d e : Bool) (x y z : Int),
-- (if true = c then (if true = d then (if true = e then x else z) else y) else z) < x
#testOptimize [ "ReduceThenITEUnchanged_2" ]
  ∀ (c d e : Bool) (x y z : Int),
    (if c then (if d then (if e then x else z) else y) else z) < x ===>
  ∀ (c d e : Bool) (x y z : Int),
    (if true = c then (if true = d then (if true = e then x else z) else y) else z) < x


/-! Test cases for reduction rule `if c then e1 else (if c then e2 else e3) ==> if c then e1 else e3`. -/

-- ∀ (c : Bool) (x y z : Int), (if c then x else (if c then y else z)) < x ===>
-- ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x
#testOptimize [ "ReduceElseITE_1" ]
  ∀ (c : Bool) (x y z : Int), (if c then x else (if c then y else z)) < x ===>
  ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x

-- ∀ (c : Bool) (x y z : Int), (if c then x else (if c then (if c then x else z) else y)) < x ===>
-- ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x
#testOptimize [ "ReduceElseITE_2" ]
  ∀ (c : Bool) (x y z : Int), (if c then x else (if c then (if c then x else z) else y)) < x ===>
  ∀ (c : Bool) (x y : Int), (if true = c then x else y) < x

-- ∀ (c : Bool) (x y z : Int), (if c then x else (if c then y else (if c then x else z))) < x ===>
-- ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x
#testOptimize [ "ReduceElseITE_3" ]
  ∀ (c : Bool) (x y z : Int), (if c then x else (if c then y else (if c then x else z))) < x ===>
  ∀ (c : Bool) (x z : Int), (if true = c then x else z) < x

-- ∀ (c : Bool) (x y z : Int),
-- (if c then x else (if c then y else z)) = (if true = c then x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseITE_4" ]
  ∀ (c : Bool) (x y z : Int),
   (if c then x else (if c then y else z)) = (if true = c then x else z) ===> True

-- ∀ (c : Bool) (x y z : Int),
--  (if c then x else (if c then (if c then x else z) else y)) =
--  (if true = c then x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseITE_5" ]
  ∀ (c : Bool) (x y z : Int),
    (if c then x else (if c then (if c then x else z) else y)) =
    (if c then x else y) ===> True

-- ∀ (c : Bool) (x y z : Int),
--  (if c then x else (if c then y else (if c then x else z))) =
--  (if true = c then x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseITE_6" ]
  ∀ (c : Bool) (x y z : Int),
    (if c then x else (if c then y else (if c then x else z))) =
    (if true = c then x else z) ===> True

/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
     - `if c then e1 else (if c then e2 else e3) ==> if c then e1 else e3`.
-/

-- ∀ (c d : Bool) (x y z : Int), (if c then x else (if d then y else z)) < x ===>
-- ∀ (c d : Bool) (x y z : Int), (if true = c then x else (if true = d then y else z)) < x
#testOptimize [ "ReduceElseITEUnchanged_1" ]
  ∀ (c d : Bool) (x y z : Int), (if c then x else (if d then y else z)) < x ===>
  ∀ (c d : Bool) (x y z : Int), (if true = c then x else (if true = d then y else z)) < x

-- ∀ (c d e : Bool) (x y z : Int), (if c then x else (if d then (if e then x else z) else y)) < x ===>
--  ∀ (c d e : Bool) (x y z : Int),
--   (if true = c then x else (if true = d then (if true = e then x else z) else y)) < x
#testOptimize [ "ReduceElseITEUnchanged_2" ]
  ∀ (c d e : Bool) (x y z : Int), (if c then x else (if d then (if e then x else z) else y)) < x ===>
  ∀ (c d e : Bool) (x y z : Int),
     (if true = c then x else (if true = d then (if true = e then x else z) else y)) < x


-- ∀ (c d e : Bool) (x y z : Int), (if c then x else (if d then y else (if e then x else z))) < x ===>
-- ∀ (c d e : Bool) (x y z : Int),
--  (if true = c then x else (if true = d then y else (if true = e then x else z))) < x

#testOptimize [ "ReduceElseITEUnchanged_3" ]
  ∀ (c d e : Bool) (x y z : Int), (if c then x else (if d then y else (if e then x else z))) < x ===>
  ∀ (c d e : Bool) (x y z : Int),
    (if true = c then x else (if true = d then y else (if true = e then x else z))) < x

end Test.ReduceITE
