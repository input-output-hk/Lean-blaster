import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstCtorProp

/-! ## Test objectives to validate ite/match over constructor propagation. -/

/-! Test cases to validate when ite over constructor propagation must be applied. -/

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int), [Decidable c] →
--   (if c then some x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int),
--     xs = Solver.dite' c (fun _ => some x :: []) (fun _ => none :: [])
#testOptimize [ "IteOverCtor_1" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int), [Decidable c] →
    (if c then some x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int),
      xs = Solver.dite' c (fun _ => some x :: []) (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
--   (if c then (if b then some x else none) else none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
--   xs = Solver.dite' c
--        (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))
--        (fun _ => none :: [])
#testOptimize [ "IteOverCtor_2" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then (if b then some x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    xs = Solver.dite' c
         (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))
         (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
--   (if c then some x else (if b then some x else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
--   xs = Solver.dite' c
--        (fun _ => some x :: [])
--        (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))
#testOptimize [ "IteOverCtor_3" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then some x else (if b then some x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    xs = Solver.dite' c
         (fun _ => some x :: [])
         (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then some x else some y
--     else if b then some x else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   xs =
--   Solver.dite' c
--   (fun _ => Solver.dite' d (fun _ => some x :: []) (fun _ => some y :: []))
--   (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))
#testOptimize [ "IteOverCtor_4" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 :: [] = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  xs =
  Solver.dite' c
  (fun _ => Solver.dite' d (fun _ => some x :: []) (fun _ => some y :: []))
  (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))


-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else some y
--     else if b then some x else none;
--   let op2 := if b then [] else some y :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--  xs = Solver.dite' c
--       (fun _ =>
--          Solver.dite' d
--          (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ =>  some x :: some y :: []))
--          (fun _ => Solver.dite' b (fun _ => some y :: []) (fun _ => some y :: some y :: [])))
--       (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: some y :: []))
#testOptimize [ "IteOverCtor_5" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else some y
    else if b then some x else none;
  let op2 := if b then [] else some y :: []
  (op1 :: op2) = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
 xs = Solver.dite' c
      (fun _ =>
         Solver.dite' d
         (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ =>  some x :: some y :: []))
         (fun _ => Solver.dite' b (fun _ => some y :: []) (fun _ => some y :: some y :: [])))
      (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: some y :: []))

-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int), [Decidable c] →
--   (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int),
--   xs = Solver.dite' c
--        (fun _ => (λ n => some (Int.add x n)) :: [])
--        (fun _ => (λ n => some (Int.add x (Int.neg n))) :: [])
-- NOTE: Test cases to ensure that ite returning function are properly handled
#testOptimize [ "IteOverCtor_6" ]
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int), [Decidable c] →
    (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int),
    xs = Solver.dite' c
         (fun _ => (λ n => some (Int.add x n)) :: [])
         (fun _ => (λ n => some (Int.add x (Int.neg n))) :: [])


-- ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
--   (if c then x else none) :: [] = xs ===>
-- ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
--   xs = if true = c then x :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_7" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int), [Decidable c] →
    (if c then x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int),
    xs = Solver.dite' c (fun _ => x :: []) (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
--   [Decidable b] → [Decidable c] →
--   (if c then (if b then x else none) else none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
--   xs = Solver.dite' c
--        (fun _ => (Solver.dite' b (fun _ => x :: []) (fun _ => none :: [])))
--        (fun _ => none :: [])
-- NOTE: Test cases to ensure that even non constant ite are also propagated
#testOptimize [ "IteOverCtor_8" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    [Decidable b] → [Decidable c] →
    (if c then (if b then x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    xs = Solver.dite' c
         (fun _ => (Solver.dite' b (fun _ => x :: []) (fun _ => none :: [])))
         (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] →
--     (if c then some x else (if b then p else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   xs = Solver.dite' c
--        (fun _ => some x :: [])
--        (fun _ => Solver.dite' b (fun _ => p :: []) (fun _ => none :: []))
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_9" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    [Decidable b] → [Decidable c] →
      (if c then some x else (if b then p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    xs = Solver.dite' c
         (fun _ => some x :: [])
         (fun _ => Solver.dite' b (fun _ => p :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then some x else p
--     else if b then some x else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--    xs = Solver.dite' c
--         (fun _ => Solver.dite' d (fun _ => some x :: []) (fun _ => p :: []))
--         (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_10" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else p
    else if b then some x else none;
  op1 :: [] = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
   xs = Solver.dite' c
        (fun _ => Solver.dite' d (fun _ => some x :: []) (fun _ => p :: []))
        (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: []))


-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else p
--     else if b then some x else none;
--   let op2 := if b then [] else p :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   xs = Solver.dite' c
--        (fun _ =>
--          Solver.dite' d
--          (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => some x :: p :: []))
--          (fun _ => Solver.dite' b (fun _ => p :: []) (fun _ => p :: p :: [])))
--        (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: p :: []))
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_11" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then [] else p :: []
  (op1 :: op2) = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  xs = Solver.dite' c
       (fun _ =>
         Solver.dite' d
         (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => some x :: p :: []))
         (fun _ => Solver.dite' b (fun _ => p :: []) (fun _ => p :: p :: [])))
       (fun _ => Solver.dite' b (fun _ => some x :: []) (fun _ => none :: p :: []))

-- ∀ (c : Bool) (x y z : Int),
--   some ((if c then λ n => x + n else λ n => x - n) z) = some y ===>
-- ∀ (c : Bool) (x y z : Int),
--  (false = c → some y = some (Int.add x (Int.neg z))) ∧
--  (true = c → some y = some (Int.add x z))
-- NOTE: Can be reduced to
--  (false = c → y = Int.add x (Int.neg z)) ∧
--  (true = c → y = Int.add x z)
-- with additional simplification rules.
#testOptimize [ "IteOverCtor_12" ]
  ∀ (c : Bool) (x y z : Int),
    some ((if c then λ n => x + n else λ n => x - n) z) = some y ===>
  ∀ (c : Bool) (x y z : Int),
    (false = c → some y = some (Int.add x (Int.neg z))) ∧
    (true = c → some y = some (Int.add x z))


/-! Test cases to validate when dite over constructor constant propagation must be applied. -/

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--   (if h : c then t h x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
--   xs = Solver.dite' c (fun h : c => t h x :: []) (fun _ => none :: [])
#testOptimize [ "DIteOverCtor_1" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
    (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
    xs = Solver.dite' c (fun h : c => t h x :: []) (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--   [Decidable b] → [Decidable c] →
--     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--     xs = Solver.dite' c
--          (fun _ => Solver.dite' b (fun h2 : _ => t h2 x :: []) (fun _ => none :: []))
--          (fun h1 : _ => f h1 none :: [])
#testOptimize [ "DIteOverCtor_2" ]
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
   [Decidable b] → [Decidable c] →
     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
     xs = Solver.dite' c
          (fun _ => Solver.dite' b (fun h2 : _ => t h2 x :: []) (fun _ => none :: []))
          (fun h1 : _ => f h1 none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int),
--     xs = Solver.dite' c
--          (fun h1 : _ => t h1 x :: [])
--          (fun _ => Solver.dite' b (fun h2 : _ => f h2 x :: []) (fun _ => none :: []))
#testOptimize [ "DIteOverCtor_3" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int),
      xs = Solver.dite' c
           (fun h1 : _ => t h1 x :: [])
           (fun _ => Solver.dite' b (fun h2 : _ => f h2 x :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
--    (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
--    (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c
--     then if h2 : d then t h1 x else f h2 y
--     else if h3 : b then g h3 x else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
--    (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
--    (g : b → Int → Option Int),
--   xs =
--   Solver.dite' c
--   (fun h1 : _ => Solver.dite' d (fun _ => t h1 x :: []) (fun h2 : _ => f h2 y :: []))
--   (fun _ => Solver.dite' b (fun h3 : _ => g h3 x :: []) (fun _ => none :: []))
#testOptimize [ "DIteOverCtor_4" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
   (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
   (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c
    then if h2 : d then t h1 x else f h2 y
    else if h3 : b then g h3 x else none;
  op1 :: [] = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
   (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
   (g : b → Int → Option Int),
  xs =
  Solver.dite' c
  (fun h1 : _ => Solver.dite' d (fun _ => t h1 x :: []) (fun h2 : _ => f h2 y :: []))
  (fun _ => Solver.dite' b (fun h3 : _ => g h3 x :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
--   (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
--   (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c then if h2 : d then t h1 x else f h2 y
--     else if h3 : b then g h3 x else none;
--   let op2 := if h4 : b then g h4 y :: [] else []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
--   (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
--   (g : b → Int → Option Int),
--  xs = Solver.dite' c
--       (fun h1 : _ =>
--         Solver.dite' d
--         (fun _ =>
--           Solver.dite' b (fun h4 : _ => t h1 x :: g h4 y :: []) (fun _ => t h1 x :: []))
--         (fun h2 : _ =>
--           Solver.dite' b (fun h4 : _ => f h2 y :: g h4 y :: []) (fun _ => f h2 y :: [])))
--       (fun _ =>
--         Solver.dite' b (fun h3 : _ => g h3 x :: g h3 y :: []) (fun _ => none :: []))
#testOptimize [ "DIteOverCtor_5" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
  (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
  (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c then if h2 : d then t h1 x else f h2 y
    else if h3 : b then g h3 x else none;
  let op2 := if h4 : b then g h4 y :: [] else []
  (op1 :: op2) = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int)
  (t : c → Int → Option Int) (f : ¬ d → Int → Option Int)
  (g : b → Int → Option Int),
 xs = Solver.dite' c
      (fun h1 : _ =>
        Solver.dite' d
        (fun _ =>
          Solver.dite' b (fun h4 : _ => t h1 x :: g h4 y :: []) (fun _ => t h1 x :: []))
        (fun h2 : _ =>
          Solver.dite' b (fun h4 : _ => f h2 y :: g h4 y :: []) (fun _ => f h2 y :: [])))
      (fun _ =>
        Solver.dite' b (fun h3 : _ => g h3 x :: g h3 y :: []) (fun _ => none :: []))

-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
--     (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int),
--   xs = Solver.dite' c
--        (fun h : _ => (λ n => t h (Int.add x n)) :: [])
--        (fun h : _ => (λ n => e h (Int.add x (Int.neg n))) :: [])
-- NOTE: Test cases to ensure that dite returning function are properly handled
#testOptimize [ "DIteOverCtor_6" ]
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
      (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int),
    xs = Solver.dite' c
         (fun h : _ => (λ n => t h (Int.add x n)) :: [])
         (fun h : _ => (λ n => e h (Int.add x (Int.neg n))) :: [])

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--    (if h : c then t h x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
--    xs = Solver.dite' c (fun h : _ => t h x :: []) (fun _ => none :: [])
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_7" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
     (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
     xs = Solver.dite' c (fun h : _ => t h x :: []) (fun _ => none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Int) (f : ¬ c → Int → Option Int),
--     xs = Solver.dite' c
--          (fun _ => Solver.dite' b (fun h2 : _ => some (t h2 x) :: []) (fun _ => none :: []))
--          (fun h1 : _ => f h1 x :: [])
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_8" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int),
      xs = Solver.dite' c
           (fun _ => Solver.dite' b (fun h2 : _ => some (t h2 x) :: []) (fun _ => none :: []))
           (fun h1 : _ => f h1 x :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int),
--    xs = Solver.dite' c
--         (fun h1 : _ => t h1 x :: [])
--         (fun _ => Solver.dite' b (fun h2 : _ => f h2 p :: []) (fun _ => none :: []))
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_9" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int),
     xs = Solver.dite' c
          (fun h1 : _ => t h1 x :: [])
          (fun _ => Solver.dite' b (fun h2 : _ => f h2 p :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : d → Int → Int) (f : b → Int → Int) (g : c → Int → Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c
--     then if h2 : d then some (t h2 x) else g h1 p
--     else if h3 : b then some (f h3 x) else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : d → Int → Int) (f : b → Int → Int) (g : c → Int → Option Int),
--    xs = Solver.dite' c
--         (fun h1 : _ => Solver.dite' d (fun h2 : _ => some (t h2 x) :: []) (fun _ => (g h1 p) :: []))
--         (fun _ => Solver.dite' b (fun h3 : _ => some (f h3 x) :: []) (fun _ => none :: []))
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_10" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : b → Int → Int) (g : c → Int → Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c
    then if h2 : d then some (t h2 x) else g h1 p
    else if h3 : b then some (f h3 x) else none;
  op1 :: [] = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : b → Int → Int) (g : c → Int → Option Int),
   xs = Solver.dite' c
        (fun h1 : _ => Solver.dite' d (fun h2 : _ => some (t h2 x) :: []) (fun _ => (g h1 p) :: []))
        (fun _ => Solver.dite' b (fun h3 : _ => some (f h3 x) :: []) (fun _ => none :: []))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : d → Int → Int) (f : c → Int → Option Int) (g : b → Int → Int)
--   (j : ¬ b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c then if h2 : d then some (t h2 x) else f h1 p
--     else if h3 : b then some (g h3 x) else none;
--   let op2 := if h4 : b then [] else j h4 p :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : d → Int → Int) (f : c → Int → Option Int) (g : b → Int → Int)
--   (j : ¬ b → Int → Option Int),
--   xs = Solver.dite' c
--        (fun h1 : _ =>
--          Solver.dite' d
--          (fun h2 : _ =>
--            Solver.dite' b
--            (fun _ => some (t h2 x) :: [])
--            (fun h4 : _ => some (t h2 x) :: (j h4 p) :: []))
--          (fun _ =>
--            Solver.dite' b (fun _ => f h1 p :: []) (fun h4 : _ => f h1 p :: j h4 p :: [])))
--        (fun _ =>
--          Solver.dite' b
--          (fun h3 : _ => some (g h3 x) :: [])
--          (fun h3 : _ => none :: (j h3 p) :: []))
#testOptimize [ "DIteOverCtor_11" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : c → Int → Option Int) (g : b → Int → Int)
  (j : ¬ b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c then if h2 : d then some (t h2 x) else f h1 p
    else if h3 : b then some (g h3 x) else none;
  let op2 := if h4 : b then [] else j h4 p :: []
  (op1 :: op2) = xs ===>
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
  (t : d → Int → Int) (f : c → Int → Option Int) (g : b → Int → Int)
  (j : ¬ b → Int → Option Int),
  xs = Solver.dite' c
       (fun h1 : _ =>
         Solver.dite' d
         (fun h2 : _ =>
           Solver.dite' b
           (fun _ => some (t h2 x) :: [])
           (fun h4 : _ => some (t h2 x) :: (j h4 p) :: []))
         (fun _ =>
           Solver.dite' b (fun _ => f h1 p :: []) (fun h4 : _ => f h1 p :: j h4 p :: [])))
       (fun _ =>
         Solver.dite' b
         (fun h3 : _ => some (g h3 x) :: [])
         (fun h3 : _ => none :: (j h3 p) :: []))

-- ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : ¬ true = c → Int → Int),
--   some ((if h : true = c then λ n => t h (x + n) else λ n => f h (x - n)) z) = some y ===>
-- ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : false = c → Int → Int),
--   (∀ h : false = c, some y = some (f h (Int.add x (Int.neg z)))) ∧
--   (∀ h : true = c, some y = some (t h (Int.add x z)))
-- NOTE: Can be reduced to
--   (∀ h : false = c, y = f h (Int.add x (Int.neg z))) ∧
--   (∀ h : true = c, y = t h (Int.add x z))
-- with additional simplification rules.
#testOptimize [ "DIteOverCtor_13" ]
  ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : ¬ true = c → Int → Int),
    some ((if h : true = c then λ n => t h (x + n) else λ n => f h (x - n)) z) = some y ===>
  ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : false = c → Int → Int),
    (∀ h : false = c, some y = some (f h (Int.add x (Int.neg z)))) ∧
    (∀ h : true = c, some y = some (t h (Int.add x z)))

-- ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
--   r = some (dite c t e) ===>
-- ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool),
--   r = Solver.dite' c (fun h : _ => some (t h)) (fun h : _ => some (e h))
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_14" ]
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
    r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool),
    r = Solver.dite' c (fun h : _ => some (t h)) (fun h : _ => some (e h))

-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   [Decidable c] → r = some (dite c t e) ===>
-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   r = Solver.dite' c (fun h : _ => some (λ x => t h x)) (fun h : _ => some (λ x => e h x))
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_15" ]
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    r = Solver.dite' c (fun h : _ => some (λ x => t h x)) (fun h : _ => some (λ x => e h x))

/-! Test cases to validate when match over constructor constant propagation must be applied. -/

inductive Color where
  | red : Color → Color
  | transparent : Color
  | blue : Color → Color
  | black : Color

def toColorOne (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some _ => .blue .transparent

-- ∀ (n : Option Nat) (xs : List Color), toColorOne n :: [] = xs ===>
-- ∀ (n : Option Nat) (xs : List Color),
--      xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
--             (fun (_ : Unit) => .black :: [])
--             (fun (_ : Unit) => .transparent :: [])
--             (fun (_ : Unit) => .red .transparent :: [])
--             (fun (_ : Unit) => .blue .black :: [])
--             (fun (_ : Nat) => .blue .transparent :: []) )
#testOptimize [ "MatchOverCtor_1" ]
  ∀ (n : Option Nat) (xs : List Color), toColorOne n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
       xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
              (fun (_ : Unit) => .black :: [])
              (fun (_ : Unit) => .transparent :: [])
              (fun (_ : Unit) => .red .transparent :: [])
              (fun (_ : Unit) => .blue .black :: [])
              (fun (_ : Nat) => .blue .transparent :: []) )

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color),
--    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
--           (fun (_ : Unit) => .black :: [])
--           (fun (_ : α) => .blue .transparent :: []) )
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_2" ]
  ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color),
    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
           (fun (_ : Unit) => .black :: [])
           (fun (_ : α) => .blue .transparent :: []) )

def toColorThree (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some n => if n < 10 then .blue .transparent
             else if n < 100 then .red .black
             else .red .transparent

-- ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
-- ∀ (n : Option Nat) (xs : List Color),
--   xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
--          (fun (_ : Unit) => .black :: [])
--          (fun (_ : Unit) => .transparent :: [])
--          (fun (_ : Unit) => .red .transparent :: [])
--          (fun (_ : Unit) => .blue .black :: [])
--          (fun (a : Nat) =>
--            Solver.dite' (a < 10)
--              (fun _ => .blue .transparent :: [])
--              (fun _ =>
--                Solver.dite' (a < 100)
--                (fun _ => .red .black :: [])
--                (fun _ => .red .transparent :: []))) )
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that simplification rule can transitively detect
-- that all path reduce to constant values
#testOptimize [ "MatchOverCtor_3" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
           (fun (_ : Unit) => .black :: [])
           (fun (_ : Unit) => .transparent :: [])
           (fun (_ : Unit) => .red .transparent :: [])
           (fun (_ : Unit) => .blue .black :: [])
           (fun (a : Nat) =>
             Solver.dite' (a < 10)
               (fun _ => .blue .transparent :: [])
               (fun _ =>
                 Solver.dite' (a < 100)
                 (fun _ => .red .black :: [])
                 (fun _ => .red .transparent :: []))) )

def beqColor : Color → Color → Bool
| .red x, .red y
| .blue x, .blue y => beqColor x y
| .transparent, .transparent
| .black, .black => true
| _, _ => false

def beqColorDegree : Color → Color → (Nat → Bool)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then true else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => true
| _, _ => λ _n => false

-- ∀ (x y : Color) (xs : List (Nat → Bool)), beqColorDegree x y :: [] = xs ===>
-- ∀ (x y : Color) (xs : List (Nat → Bool)),
--  xs = ( beqColor.match_1 (fun (_ : Color) (_ : Color) => List (Nat → Bool)) x y
--         (fun (c1 : Color) (c2 : Color) =>
--           (λ n => Solver.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2)) :: [])
--         (fun ( c1 : Color) (c2 : Color) =>
--           (λ n => Solver.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2)) :: [])
--         (fun (_ : Unit) => (λ _n => true) :: [])
--         (fun (_ : Unit) => (λ _n => true) :: [])
--         (fun (_ : Color) (_ : Color ) => (λ _n => false) :: []) )
-- NOTE: Test cases to ensure that match returning function are properly handled
-- NOTE: Lean4 already applied structural equivalence between beqColorDegree.match_1 and beqColor.match_1
#testOptimize [ "MatchOverCtor_4" ] (norm-result: 1)
  ∀ (x y : Color) (xs : List (Nat → Bool)), beqColorDegree x y :: [] = xs ===>
  ∀ (x y : Color) (xs : List (Nat → Bool)),
   xs = ( beqColor.match_1 (fun (_ : Color) (_ : Color) => List (Nat → Bool)) x y
          (fun (c1 : Color) (c2 : Color) =>
            (λ n => Solver.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2)) :: [])
          (fun ( c1 : Color) (c2 : Color) =>
            (λ n => Solver.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2)) :: [])
          (fun (_ : Unit) => (λ _n => true) :: [])
          (fun (_ : Unit) => (λ _n => true) :: [])
          (fun (_ : Color) (_ : Color ) => (λ _n => false) :: []) )

-- ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop), [Decidable c] →
--   let op := if c then [] else .transparent :: [];
--   toColorTwo n :: op = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop),
--   xs = Solver.dite' c
--       (fun _ =>
--          toColorTwo.match_1 (fun (_ : Option α) => List Color) n
--          (fun (_ : Unit) => [.black])
--          (fun (_ : α) => [.blue .transparent] ) )
--       (fun _ =>
--          toColorTwo.match_1 (fun (_ : Option α) => List Color) n
--          (fun (_ : Unit) => [.black, .transparent])
--          (fun (_ : α) => [.blue .transparent, .transparent]) )
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_5" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop), [Decidable c] →
    let op := if c then [] else .transparent :: [];
    toColorTwo n :: op = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop),
    xs =  Solver.dite' c
          (fun _ =>
             toColorTwo.match_1 (fun (_ : Option α) => List Color) n
             (fun (_ : Unit) => [.black])
             (fun (_ : α) => [.blue .transparent] ) )
          (fun _ =>
             toColorTwo.match_1 (fun (_ : Option α) => List Color) n
             (fun (_ : Unit) => [.black, .transparent])
             (fun (_ : α) => [.blue .transparent, .transparent]) )

end Tests.ConstCtorProp
