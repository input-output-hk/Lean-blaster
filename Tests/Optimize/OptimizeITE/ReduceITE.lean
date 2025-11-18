import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ReduceITE

/-! ## Test objectives to validate reduction rules on `ite` -/

/-! Test cases for reduction rule `if c then (if c then e1 else e2) else e3 ==> if c then e1 else e3`.

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (b c : Bool) (x y z : Int), (if b = c then (if b = c then x else y) else z) < x ===>
-- ∀ (b c : Bool) (x z : Int),
--    Solver.dite' (b = c) (fun _ : b = c => x) (fun _ : ¬ (b = c) => z) < x
#testOptimize [ "ReduceThenITE_1" ]
  ∀ (b c : Bool) (x y z : Int), (if b = c then (if b = c then x else y) else z) < x ===>
  ∀ (b c : Bool) (x z : Int),
     Solver.dite' (b = c) (fun _ : b = c => x) (fun _ : ¬ (b = c) => z) < x

-- ∀ (c : Prop) (x y z : Int), [Decidable c] →
--   (if c then (if c then (if c then x else z) else y) else z) < x ===>
-- ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceThenITE_2" ]
  ∀ (c : Prop) (x y z : Int), [Decidable c] →
    (if c then (if c then (if c then x else z) else y) else z) < x ===>
  ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x

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

-- ∀ (c d : Prop) (x y z : Int), [Decidable c] → [Decidable d] →
--   (if c then (if d then x else y) else z) < x ===>
-- ∀ (c d : Prop) (x y z : Int),
--   Solver.dite' c
--     (fun _ : c => Solver.dite' d (fun _ : d => x) (fun _ : ¬ d => y))
--     (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceThenITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int), [Decidable c] → [Decidable d] →
    (if c then (if d then x else y) else z) < x ===>
  ∀ (c d : Prop) (x y z : Int),
    Solver.dite' c
      (fun _ : c => Solver.dite' d (fun _ : d => x) (fun _ : ¬ d => y))
      (fun _ : ¬ c => z) < x

-- ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
--   (if c then (if d then (if e then x else z) else y) else z) < x ===>
-- ∀ (c d e : Prop) (x y z : Int),
--   Solver.dite' c
--     (fun _ : c =>
--       Solver.dite' d
--         (fun _ : d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
--         (fun _ : ¬ d => y))
--     (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceThenITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
    (if c then (if d then (if e then x else z) else y) else z) < x ===>
  ∀ (c d e : Prop) (x y z : Int),
    Solver.dite' c
      (fun _ : c =>
        Solver.dite' d
          (fun _ : d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
          (fun _ : ¬ d => y))
      (fun _ : ¬ c => z) < x


/-! Test cases for reduction rule `if c then e1 else (if c then e2 else e3) ==> if c then e1 else e3`.

    NOTE: This reduction rule no more exists as it has been replaced
          by a more generic normalization rule based on hypothesis context.
-/

-- ∀ (c : Prop) (x y z : Int), [Decidable c] → (if c then x else (if c then y else z)) < x ===>
-- ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceElseITE_1" ]
  ∀ (c : Prop) (x y z : Int), [Decidable c] → (if c then x else (if c then y else z)) < x ===>
  ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x

-- ∀ (c : Prop) (x y z : Int), [Decidable  c] → (if c then x else (if c then (if c then x else z) else y)) < x ===>
-- ∀ (c : Prop) (x y : Int), Solver.dite' c (fun _ : c => x ) (fun _ : ¬ c => y) < x
#testOptimize [ "ReduceElseITE_2" ]
  ∀ (c : Prop) (x y z : Int), [Decidable  c] → (if c then x else (if c then (if c then x else z) else y)) < x ===>
  ∀ (c : Prop) (x y : Int), Solver.dite' c (fun _ : c => x ) (fun _ : ¬ c => y) < x

-- ∀ (c : Prop) (x y z : Int), [Decidable c] → (if c then x else (if c then y else (if c then x else z))) < x ===>
-- ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x
#testOptimize [ "ReduceElseITE_3" ]
  ∀ (c : Prop) (x y z : Int), [Decidable c] → (if c then x else (if c then y else (if c then x else z))) < x ===>
  ∀ (c : Prop) (x z : Int), Solver.dite' c (fun _ : c => x) (fun _ : ¬ c => z) < x

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

-- ∀ (c d : Prop) (x y z : Int), [Decidable c] → [Decidable d] → (if c then x else (if d then y else z)) < x ===>
-- ∀ (c d : Prop) (x y z : Int),
--      Solver.dite' c
--        (fun _ : c => x)
--        (fun _ : ¬ c => Solver.dite' d (fun _ : d => y) (fun _ : ¬ d => z)) < x
#testOptimize [ "ReduceElseITEUnchanged_1" ]
  ∀ (c d : Prop) (x y z : Int), [Decidable c] → [Decidable d] →
    (if c then x else (if d then y else z)) < x ===>
  ∀ (c d : Prop) (x y z : Int),
       Solver.dite' c
         (fun _ : c => x)
         (fun _ : ¬ c => Solver.dite' d (fun _ : d => y) (fun _ : ¬ d => z)) < x

-- ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
--     (if c then x else (if d then (if e then x else z) else y)) < x ===>
-- ∀ (c d e : Prop) (x y z : Int),
--    Solver.dite' c
--      (fun _ : c => x)
--      (fun _ : ¬ c =>
--        Solver.dite' d
--        (fun _ : d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
--        (fun _ : ¬ d => y)) < x
#testOptimize [ "ReduceElseITEUnchanged_2" ]
  ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
      (if c then x else (if d then (if e then x else z) else y)) < x ===>
  ∀ (c d e : Prop) (x y z : Int),
     Solver.dite' c
       (fun _ : c => x)
       (fun _ : ¬ c =>
         Solver.dite' d
         (fun _ : d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))
         (fun _ : ¬ d => y)) < x

-- ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
--     (if c then x else (if d then y else (if e then x else z))) < x ===>
-- ∀ (c d e : Prop) (x y z : Int),
--   Solver.dite' c
--     (fun _ : c => x)
--     (fun _ : ¬ c =>
--        Solver.dite' d
--          (fun _ : d => y)
--          (fun _ : ¬ d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))) < x
#testOptimize [ "ReduceElseITEUnchanged_3" ]
  ∀ (c d e : Prop) (x y z : Int), [Decidable c] → [Decidable d] → [Decidable e] →
      (if c then x else (if d then y else (if e then x else z))) < x ===>
  ∀ (c d e : Prop) (x y z : Int),
    Solver.dite' c
      (fun _ : c => x)
      (fun _ : ¬ c =>
         Solver.dite' d
           (fun _ : d => y)
           (fun _ : ¬ d => Solver.dite' e (fun _ : e => x) (fun _ : ¬ e => z))) < x

end Test.ReduceITE
