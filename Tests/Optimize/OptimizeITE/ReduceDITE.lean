import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ReduceDITE

/-! ## Test objectives to validate reduction rules on `ite` -/

/-! Test cases for reduction rule
     - `dite c then (fun h : c => if c then e1 else e2) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → (if h : c then (if c then t h x else y) else z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--   Blaster.dite' c (fun h : c => t h x) (fun _h : ¬ c => z) < x
#testOptimize [ "ReduceThenDITE_ITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → (if h : c then (if c then t h x else y) else z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    Blaster.dite' c (fun h : c => t h x) (fun _h : ¬ c => z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then (if c then (if c then t h x else z) else y) else z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--    Blaster.dite' c (fun h : c => t h x) (fun _h : ¬ c => z) < x
#testOptimize [ "ReduceThenDITE_ITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then (if c then (if c then t h x else z) else y) else z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    Blaster.dite' c (fun h : c => t h x) (fun _h : ¬ c => z) < x

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
-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int),
--  Blaster.dite' c
--   (fun h : c => Blaster.dite' d (fun _ : d => t h x) (fun _ : ¬ d => y))
--   (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceThenDITE_ITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then (if d then t h x else y) else z) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int),
    Blaster.dite' c
     (fun h : c => Blaster.dite' d (fun _ : d => t h x) (fun _ : ¬ d => y))
     (fun _ : ¬ c => z) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then (if d then (if e then t h x else z) else y) else z) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--    Blaster.dite' c
--      (fun h : c =>
--        Blaster.dite' d
--          (fun _ : d => Blaster.dite' e (fun _ : e => t h x) (fun _ : ¬ e => z))
--          (fun _ : ¬ d => y))
--      (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceThenDITE_ITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then (if d then (if e then t h x else z) else y) else z) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
     Blaster.dite' c
       (fun h : c =>
         Blaster.dite' d
           (fun _ : d => Blaster.dite' e (fun _ : e => t h x) (fun _ : ¬ e => z))
           (fun _ : ¬ d => y))
       (fun _ : ¬ c => z) < x


/-! Test cases for reduction rule
     - `dite c then (fun h : c => dite c (fun h : c => e1) (fun h : ¬ c => e2)) (fun h : ¬ c => e3)` ==>
          dite c then (fun h : c => e1) (fun h : ¬ c => e3)`

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
--    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then t h2 x else y) else e h1 z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
--    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y) else e h1 z) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x

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
--  Blaster.dite' c
--    (fun _ : c => Blaster.dite' d (fun h2 : d => t h2 x) (fun _ : ¬ d => y))
--    (fun h1 : ¬ c => e h1 z) < x
#testOptimize [ "ReduceThenDITE_DITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then (if h2 : d then t h2 x else y) else e h1 z) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : d → Int → Int) (e : ¬ c → Int → Int),
      Blaster.dite' c
        (fun _ : c => Blaster.dite' d (fun h2 : d => t h2 x) (fun _ : ¬ d => y))
        (fun h1 : ¬ c => e h1 z) < x

-- ∀ (c d e : Prop) (x y z : Int)
--   (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x ===>
-- ∀ (c d e : Prop) (x y z : Int)
--   (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
--  Blaster.dite' c
--    (fun _ : c =>
--      (Blaster.dite' d
--        (fun _ : d => Blaster.dite' e (fun h3 : e => t h3 x) (fun _ : ¬ e => z))
--        (fun h2 : ¬ d => f h2 y)))
--    (fun h1 : ¬ c => g h1 z) < x
#testOptimize [ "ReduceThenDITE_DITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int)
    (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then (if h2 : d then (if h3 : e then t h3 x else z) else f h2 y) else g h1 z) < x ===>
  ∀ (c d e : Prop) (x y z : Int)
    (t : e → Int → Int) (f : ¬ d → Int → Int) (g : ¬ c → Int → Int),
      Blaster.dite' c
        (fun _ : c =>
          (Blaster.dite' d
            (fun _ : d => Blaster.dite' e (fun h3 : e => t h3 x) (fun _ : ¬ e => z))
            (fun h2 : ¬ d => f h2 y)))
        (fun h1 : ¬ c => g h1 z) < x


/-! Test cases for reduction rule
      - `dite c then (fun h : c => e1) (fun h : ¬ c => if c then e2 else e3)` ==>
           dite c then (fun h : c => e1) (fun h : ¬ c => e3)`.

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then y else z)) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--   Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceElseDITE_ITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then y else z)) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then (if c then x else z) else y)) < x ===>
-- ∀ (c : Prop) (x y : Int) (t : c → Int → Int),
--   Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => y) < x
#testOptimize [ "ReduceElseDITE_ITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then (if c then x else z) else y)) < x ===>
  ∀ (c : Prop) (x y : Int) (t : c → Int → Int),
    Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => y) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
--   (if h : c then t h x else (if c then y else (if c then x else z))) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
--    Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceElseDITE_ITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] →
    (if h : c then t h x else (if c then y else (if c then x else z))) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int),
    Blaster.dite' c (fun h : c => t h x) (fun _ : ¬ c => z) < x

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
-- ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int),
--  Blaster.dite' c
--   (fun h : c => t h x)
--   (fun _ : ¬ c => (Blaster.dite' d (fun _ : d => y) (fun _ : ¬ d => z))) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int), [Decidable c] → [Decidable d] →
    (if h : c then t h x else (if d then y else z)) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int),
    Blaster.dite' c
      (fun h : c => t h x)
      (fun _ : ¬ c => (Blaster.dite' d (fun _ : d => y) (fun _ : ¬ d => z))) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then (if e then x else z) else y)) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--  Blaster.dite' c
--   (fun h : c => t h x)
--   (fun _ : ¬ c =>
--    Blaster.dite' d
--      (fun _ : d => Blaster.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
--      (fun _ : ¬ d => y)) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then (if e then x else z) else y)) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
      Blaster.dite' c
       (fun h : c => t h x)
       (fun _ : ¬ c =>
         Blaster.dite' d
           (fun _ : d => Blaster.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
           (fun _ : ¬ d => y)) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h : c then t h x else (if d then y else (if e then x else z))) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
--  Blaster.dite' c
--    (fun h : c => t h x)
--    (fun _ : ¬ c =>
--     Blaster.dite' d
--       (fun _ : d => y)
--       (fun _ : ¬ d => Blaster.dite' e (fun _ : e => x) (fun _ : ¬ e => z))) < x
#testOptimize [ "ReduceElseDITE_ITEUnchanged_3" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h : c then t h x else (if d then y else (if e then x else z))) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int),
     Blaster.dite' c
       (fun h : c => t h x)
       (fun _ : ¬ c =>
         Blaster.dite' d
           (fun _ : d => y)
           (fun _ : ¬ d => Blaster.dite' e (fun _ : e => x) (fun _ : ¬ e => z))) < x

/-! Test cases for reduction rule
     - `dite c then (fun h : c => e1) (fun h : ¬ c => dite c (fun h : => e2) (fun h : ¬ c => e3))` ==>
         dite c then (fun h : c => e1) else (fun h : ¬ c => e3)`.

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
--    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x
#testOptimize [ "ReduceElseDITE_DITE_1" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then y else e h2 z)) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--   (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) < x ===>
-- ∀ (c : Prop) (x y : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
--   Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 y) < x
#testOptimize [ "ReduceElseDITE_DITE_2" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
    (if h1 : c then t h1 x else (if h2 : c then (if h3 : c then t h3 x else z) else e h2 y)) < x ===>
  ∀ (c : Prop) (x y : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 y) < x

-- ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
--    (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) < x ===>
-- ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
--    Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x
#testOptimize [ "ReduceElseDITE_DITE_3" ]
  ∀ (c : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int), [Decidable c] →
     (if h1 : c then t h1 x else (if h2 : c then t h2 y else (if h3 : c then x else e h3 z))) < x ===>
  ∀ (c : Prop) (x z : Int) (t : c → Int → Int) (e : ¬ c → Int → Int),
     Blaster.dite' c (fun h1 : c => t h1 x) (fun h1 : ¬ c => e h1 z) < x

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
--  Blaster.dite' c
--   (fun h1 : c => t h1 x)
--   (fun _ : ¬ c => (Blaster.dite' d (fun _ : d => y) (fun h2 : ¬ d => e h2 z))) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
    [Decidable c] → [Decidable d] →
      (if h1 : c then t h1 x else (if h2 : d then y else e h2 z)) < x ===>
  ∀ (c d : Prop) (x y z : Int) (t : c → Int → Int) (e : ¬ d → Int → Int),
      Blaster.dite' c
       (fun h1 : c => t h1 x)
       (fun _ : ¬ c => (Blaster.dite' d (fun _ : d => y) (fun h2 : ¬ d => e h2 z))) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
--  Blaster.dite' c
--   (fun h1 : c => t h1 x)
--   (fun _ : ¬ c =>
--     (Blaster.dite' d
--       (fun _ : d => Blaster.dite' e (fun h3 : e => g h3 x) (fun _ : ¬ e => z))
--       (fun h2 : ¬ d => f h2 y))) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then (if h3 : e then g h3 x else z) else f h2 y)) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : ¬ d → Int → Int) (g : e → Int → Int),
     Blaster.dite' c
       (fun h1 : c => t h1 x)
       (fun _ : ¬ c =>
         (Blaster.dite' d
           (fun _ : d => Blaster.dite' e (fun h3 : e => g h3 x) (fun _ : ¬ e => z))
           (fun h2 : ¬ d => f h2 y))) < x

-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
--   [Decidable c] → [Decidable d] → [Decidable e] →
--     (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x ===>
-- ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
--  Blaster.dite' c
--   (fun h1 : c => t h1 x)
--   (fun _ : ¬ c =>
--     Blaster.dite' d
--       (fun h2 : d => f h2 y)
--       (fun _ : ¬ d  => Blaster.dite' e (fun _ : e => x) (fun h3 : ¬ e => g h3 z))) < x
#testOptimize [ "ReduceElseDITE_DITEUnchanged_3" ]
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
    [Decidable c] → [Decidable d] → [Decidable e] →
      (if h1 : c then t h1 x else (if h2 : d then f h2 y else (if h3 : e then x else g h3 z))) < x ===>
  ∀ (c d e : Prop) (x y z : Int) (t : c → Int → Int) (f : d → Int → Int) (g : ¬ e → Int → Int),
     Blaster.dite' c
       (fun h1 : c => t h1 x)
       (fun _ : ¬ c =>
         Blaster.dite' d
           (fun h2 : d => f h2 y)
           (fun _ : ¬ d  => Blaster.dite' e (fun _ : e => x) (fun h3 : ¬ e => g h3 z))) < x


end Test.ReduceDITE
