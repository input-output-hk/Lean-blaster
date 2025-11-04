import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ReduceDITE

/-! ## Test objectives to validate reduction rules on `ite` -/

/-! Test cases for reduction rule
     - `dite c then (fun h : c => if c then e1 else e2) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → (if h : c then (if c then t h x else y) else z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--   [Decidable c] → (if h : c then t h x else z) < x
#testOptimize [ "ReduceThenDITE_ITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → (if h : c then (if c then t h x else y) else z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    [Decidable c] → (if h : c then t h x else z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then (if c then (if c then t h x else z) else y) else z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--   [Decidable c] → (if h : c then t h x else z) < x
#testOptimize [ "ReduceThenDITE_ITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then (if c then (if c then t h x else z) else y) else z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    [Decidable c] → (if h : c then t h x else z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then (if c then t h x else y) else z) = (if h : c then t h x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenDITE_ITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then (if c then t h x else y) else z) = (if h : c then t h x else z) ===> True

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then (if c then (if c then t h x else z) else y) else z) =
--   (if h : c then t h x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenDITE_ITE_4" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then (if c then (if c then t h x else z) else y) else z) =
    (if h : c then t h x else z) ===> True


/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
     - `dite c then (fun h : c => if c then e1 else e2) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`
-/

-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
--   (if h : c then (if d then t h x else y) else z) < x ===>
-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
--   (if h : c then (if d then t h x else y) else z) < x
#testOptimize [ "ReduceThenDITE_ITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then (if d then t h x else y) else z) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then (if d then t h x else y) else z) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then (if d then (if e then t h x else z) else y) else z) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then (if d then (if e then t h x else z) else y) else z) < x
#testOptimize [ "ReduceThenDITE_ITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then (if d then (if e then t h x else z) else y) else z) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then (if d then (if e then t h x else z) else y) else z) < x


/-! Test cases for reduction rule
     - `dite c then (fun h : c => dite c (fun h : c => e1) (fun h : ¬ c => e2)) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) =
--   (if h1 : c then t h1 x else e h1 z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenDITE_DITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) =
    (if h1 : c then t h1 x else e h1 z) ===> True

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) =
--   (if h1 : c then t h1 x else e h1 z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceThenDITE_DITE_4" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) =
    (if h1 : c then t h1 x else e h1 z) ===> True


/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
     - `dite c then (fun h : c => dite c (fun h : c => e1) (fun h : ¬ c => e2)) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`
-/

-- ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
--   [Decidable c] → [Decidable d] →
--     (if h1 : c then (if h2 : d then t h2 x else y) else e h1 z) < x ===>
-- ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
--   [Decidable c] → [Decidable d] →
--     (if h1 : c then (if h2 : d then t h2 x else y) else e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then (if h2 : d then t h2 x else y) else e h1 z) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then (if h2 : d then t h2 x else y) else e h1 z) < x

-- ∀ (c d e : Prop) (x y z : Int)
--   (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x ===>
-- ∀ (c d e : Prop) (x y z : Int)
--   (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x
#testOptimize [ "ReduceThenDITE_DITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int)
    (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x ===>
  ∀ (c d e : Prop) (x y z : Int)
    (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x


/-! Test cases for reduction rule
      - `dite c then (fun h : c => e1) (fun h : ¬ c => if c then e2 else e3)` ==>
           dite c then (fun h : c => e1) (fun h : ¬ c => e3)`.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then y else z)) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else z) < x
#testOptimize [ "ReduceElseDITE_ITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then y else z)) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then (if c then x else z) else y)) < x ===>
-- ∀ (c : Prop) (x y : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else y) < x
#testOptimize [ "ReduceElseDITE_ITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then (if c then x else z) else y)) < x ===>
  ∀ (c : Prop) (x y : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else y) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then y else (if c then x else z))) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else z) < x
#testOptimize [ "ReduceElseDITE_ITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then y else (if c then x else z))) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then y else z)) = (if h : c then t h x else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_ITE_4" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then y else z)) = (if h : c then t h x else z) ===> True

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then (if c then x else z) else y)) =
--   (if h : c then t h x else y) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_ITE_5" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then (if c then x else z) else y)) =
    (if h : c then t h x else y) ===> True

-- ∀ (c : Prop) (x y z : Int) (f : c → Int → Int), [Decidable c] →
--   (if h : c then (f h x) else (if c then y else (if c then x else z))) =
--   (if h : c then (f h x) else z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_ITE_6" ]
  ∀ (c : Prop) (x y z : Int) (f : c → Int → Int), [Decidable c] →
    (if h : c then (f h x) else (if c then y else (if c then x else z))) =
    (if h : c then (f h x) else z) ===> True


/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
      - `dite c then (fun h : c => e1) (fun h : ¬ c => if c then e2 else e3)` ==>
           dite c then (fun h : c => e1) (fun h : ¬ c => e3)`.
-/

-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
--   (if h : c then t h x else (if d then y else z)) < x ===>
-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
--   (if h : c then t h x else (if d then y else z)) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then t h x else (if d then y else z)) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then t h x else (if d then y else z)) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then (if e then x else z) else y)) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then (if e then x else z) else y)) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then (if e then x else z) else y)) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then (if e then x else z) else y)) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then y else (if e then x else z))) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then y else (if e then x else z))) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_3" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then y else (if e then x else z))) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then y else (if e then x else z))) < x


/-! Test cases for reduction rule
     - `dite c then (fun h : c => e1) (fun h : ¬ c => dite c (fun h : => e2) (fun h : ¬ c => e3))` ==>
         dite c then (fun h : c => e1) else (fun h : ¬ c => e3)`.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else e h1 z) < x
#testOptimize [ "ReduceElseDITE_DITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) < x ===>
-- ∀ (c : Prop) (x y : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else e h1 y) < x
#testOptimize [ "ReduceElseDITE_DITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) < x ===>
  ∀ (c : Prop) (x y : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else e h1 y) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--    (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--    (if h1 : c then t h1 x else e h1 z) < x
#testOptimize [ "ReduceElseDITE_DITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
     (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
     (if h1 : c then t h1 x else e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) =
--   (if h1 : c then t h1 x else e h1 z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_DITE_4" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) =
    (if h1 : c then t h1 x else e h1 z) ===> True

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) =
--   (if h1 : c then t h1 x else e h1 y) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_DITE_5" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) =
    (if h1 : c then t h1 x else e h1 y) ===> True

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) =
--   (if h1 : c then t h1 x else e h1 z) ===> True
-- NOTE: Test case to validate structural equivalence after rewriting
#testOptimize [ "ReduceElseDITE_DITE_6" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) =
    (if h1 : c then t h1 x else e h1 z) ===> True


/-! Test cases to ensure that the following reduction rule cannot be applied wrongly:
    - `dite c then (fun h : c => e1) (fun h : ¬ c => dite c (fun h : => e2) (fun h : ¬ c => e3))` ==>
         dite c then (fun h : c => e1) else (fun h : ¬ c => e3)`.
-/

-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
--   [Decidable c] → [Decidable d] →
--     (if h1 : c then t h1 x else (if h2 : d then y else e h2 z)) < x ===>
-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
--   [Decidable c] → [Decidable d] →
--     (if h1 : c then t h1 x else (if h2 : d then y else e h2 z)) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then t h1 x else (if h2 : d then y else e h2 z)) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then t h1 x else (if h2 : d then y else e h2 z)) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_3" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x


end Test.ReduceDITE
