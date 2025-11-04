import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstCtorProp

/-! ## Test objectives to validate ite/match over constructor propagation. -/

/-! Test cases to validate when ite over constructor propagation must be applied. -/

-- ∀ (c : Bool) (xs : List (Option Int)) (x : Int), (if c then some x else none) :: [] = xs ===>
-- ∀ (c : Bool) (xs : List (Option Int)) (x : Int), xs = (if true = c then some x :: [] else none :: [])
#testOptimize [ "IteOverCtor_1" ]
  ∀ (c : Bool) (xs : List (Option Int)) (x : Int), (if c then some x else none) :: [] = xs ===>
  ∀ (c : Bool) (xs : List (Option Int)) (x : Int), xs = (if true = c then some x :: [] else none :: [])

-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
--  (if c then (if b then some x else none) else none) :: [] = xs ===>
-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
--   xs = (if true = c then (if true = b then some x :: [] else none :: []) else none :: [] = xs
#testOptimize [ "IteOverCtor_2" ]
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
    (if c then (if b then some x else none) else none) :: [] = xs ===>
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
    xs = (if true = c then (if true = b then some x :: [] else none :: []) else none :: [])

-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
--   (if c then some x else (if b then some x else none)) :: [] = xs ===>
-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
--   xs = (if true = c then some x :: [] else (if true = b then some x :: [] else none :: []))
#testOptimize [ "IteOverCtor_3" ]
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
    (if c then some x else (if b then some x else none)) :: [] = xs ===>
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
    xs = (if true = c then some x :: [] else (if true = b then some x :: [] else none :: []))


-- ∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
-- let op1 :=
--   if c
--   then if d then some x else some y
--   else if b then some x else none;
--  op1 :: [] = xs ===>
-- ∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
--  xs =
--  if true = c
--  then (if true = d then some x :: [] else some y :: [])
--  else (if true = b then some x :: [] else none :: [])
#testOptimize [ "IteOverCtor_4" ]
∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 :: [] = xs ===>
∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
  xs =
  if true = c
  then (if true = d then some x :: [] else some y :: [])
  else (if true = b then some x :: [] else none :: [])


-- ∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
-- let op1 :=
--   if c
--   then if d then some x else some y
--   else if b then some x else none;
-- let op2 :=
--    if b then [] else some y :: []
--  op1 :: op2 = xs ===>
-- ∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
--  xs =
--  if true = c
--  then if true = d
--       then if b then some x :: [] else some x :: some y :: []
--       else if b then some y :: [] else some y :: some y :: []
--  else if true = b
--       then some x :: [] else some y :: []
#testOptimize [ "IteOverCtor_5" ]
∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
  let op1 :=
    if c then if d then some x else some y
    else if b then some x else none;
  let op2 := if b then [] else some y :: []
  (op1 :: op2) = xs ===>
∀ (b c d : Bool) (xs : List (Option Int)) (x y : Int),
 xs = if true = c
      then if true = d
           then if true = b then some x :: [] else some x :: some y :: []
           else if true = b then some y :: [] else some y :: some y :: []
      else if true = b
           then some x :: [] else none :: some y :: []

-- ∀ (c : Bool) (xs : List (Int → Option Int)) (x : Int),
--   (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
-- ∀ (c : Bool) (xs : List (Int → Option Int)) (x : Int),
--   xs = if true = c then (λ n => some (Int.add x n)) :: [] else (λ n => some (Int.add x (Int.neg n))) :: []
-- NOTE: Test cases to ensure that ite returning function are properly handled
#testOptimize [ "IteOverCtor_6" ]
  ∀ (c : Bool) (xs : List (Int → Option Int)) (x : Int),
    (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
  ∀ (c : Bool) (xs : List (Int → Option Int)) (x : Int),
    xs = if true = c then (λ n => some (Int.add x n)) :: [] else (λ n => some (Int.add x (Int.neg n))) :: []


-- ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
--   (if c then x else none) :: [] = xs ===>
-- ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
--   xs = if true = c then x :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_7" ]
  ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
    (if c then x else none) :: [] = xs ===>
  ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
    xs = if true = c then x :: [] else none :: []

-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Option Int),
--  (if c then (if b then x else none) else none) :: [] = xs ===>
-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Option Int),
--  xs = if true = c then (if true = b then x :: [] else none :: [] ) else none :: []
-- NOTE: Test cases to ensure that even non constant ite are also propagated
#testOptimize [ "IteOverCtor_8" ]
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Option Int),
    (if c then (if b then x else none) else none) :: [] = xs ===>
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Option Int),
    xs = if true = c then (if true = b then x :: [] else none :: [] ) else none :: []

-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   (if c then some x else (if b then p else none)) :: [] = xs ===>
-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
--  xs = if true = c then some x :: [] else if true = b then p :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_9" ]
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
    (if c then some x else (if b then p else none)) :: [] = xs ===>
  ∀ (b c : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
    xs = if true = c then some x :: [] else if true = b then p :: [] else none :: []


-- ∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
-- let op1 :=
--   if c
--   then if d then some x else p
--   else if b then some x else none;
--  op1 :: [] = xs ===>
-- ∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   xs = if true = c
--        then if true = d then some x :: [] else p :: []
--        else if true = b then some x :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_10" ]
∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
  let op1 :=
    if c
    then if d then some x else p
    else if b then some x else none;
  op1 :: [] = xs ===>
∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
   xs = if true = c
        then if true = d then some x :: [] else p :: []
        else if true = b then some x :: [] else none :: []


-- ∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
-- let op1 :=
--   if c
--   then if d then some x else p
--   else if b then some x else none;
-- let op2 :=
--    if b then [] else p :: []
--  op1 :: op2 = xs ===>
-- ∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   xs = if true = c
--        then if true = d
--             then if true = b then some x :: [] else some x :: p :: []
--             else if true = b then p :: [] else p :: p :: []
--        else if true = b then some x :: [] else none :: p :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "IteOverCtor_11" ]
∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then [] else p :: []
  (op1 :: op2) = xs ===>
∀ (b c d : Bool) (xs : List (Option Int)) (x : Int) (p : Option Int),
  xs = if true = c
       then if true = d
            then if true = b then some x :: [] else some x :: p :: []
            else if true = b then p :: [] else p :: p :: []
       else if true = b then some x :: [] else none :: p :: []

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
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--   xs = (if h : c then t h x :: [] else none :: [])
#testOptimize [ "DIteOverCtor_1" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
    (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
    xs = (if h : c then t h x :: [] else none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--    (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--    [Decidable b] → [Decidable c] →
--      (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
--  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--    (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--    [Decidable b] → [Decidable c] →
--      xs = (if h1 : c then (if h2 : b then t h2 x :: [] else none :: []) else f h1 none :: [])
#testOptimize [ "DIteOverCtor_2" ]
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
   [Decidable b] → [Decidable c] →
     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
   [Decidable b] → [Decidable c] →
     xs = (if h1 : c then (if h2 : b then t h2 x :: [] else none :: []) else f h1 none :: [])

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     xs = (if h1 : c then t h1 x :: [] else (if h2 : b then f h2 x :: [] else none :: []))
#testOptimize [ "DIteOverCtor_3" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      xs = (if h1 : c then t h1 x :: [] else (if h2 : b then f h2 x :: [] else none :: []))


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
--    (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--   xs =
--   if h1 : c
--   then (if h2 : d then t h1 x :: [] else f h2 y :: [])
--   else (if h3 : b then g h3 x :: [] else none :: [])
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
   (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  xs =
  if h1 : c
  then (if h2 : d then t h1 x :: [] else f h2 y :: [])
  else (if h3 : b then g h3 x :: [] else none :: [])


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
--   (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--  xs = if h1 : c
--       then if h2 : d
--            then if h4 : b then t h1 x :: g h4 y :: [] else t h1 x :: []
--            else if h4 : b then f h2 y :: g h4 y :: [] else f h2 y :: []
--       else if h3 : b
--            then g h3 x :: g h3 y :: [] else none :: []
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
  (g : b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
 xs = if h1 : c
      then if h2 : d
           then if h4 : b then t h1 x :: g h4 y :: [] else t h1 x :: []
           else if h4 : b then f h2 y :: g h4 y :: [] else f h2 y :: []
      else if h3 : b
           then g h3 x :: g h3 y :: [] else none :: []

-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
--     (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
--   xs = if h : c then (λ n => t h (Int.add x n)) :: [] else (λ n => e h (Int.add x (Int.neg n))) :: []
-- NOTE: Test cases to ensure that dite returning function are properly handled
#testOptimize [ "DIteOverCtor_6" ]
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
      (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
    xs = if h : c then (λ n => t h (Int.add x n)) :: [] else (λ n => e h (Int.add x (Int.neg n))) :: []


-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--    (if h : c then t h x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--    xs = if h : c then t h x :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_7" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
     (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
     xs = if h : c then t h x :: [] else none :: []

 -- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
 --    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
 --      (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
 -- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
 --    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
 --      xs = if h1 : c then (if h2 : b then some (t h2 x) :: [] else none :: []) else f h1 x :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_8" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
      xs = if h1 : c then (if h2 : b then some (t h2 x) :: [] else none :: []) else f h1 x :: []

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--    xs = if h1 : c then t h1 x :: [] else if h2 : b then f h2 p :: [] else none :: []
-- NOTE: Test cases to ensure that even non constant ite are propagated
#testOptimize [ "DIteOverCtor_9" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
     xs = if h1 : c then t h1 x :: [] else if h2 : b then f h2 p :: [] else none :: []

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
--   [Decidable b] → [Decidable c] → [Decidable d] →
--    xs = if h1 : c
--         then if h2 : d then some (t h2 x) :: [] else (g h1 p) :: []
--         else if h3 : b then some (f h3 x) :: [] else none :: []
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
  [Decidable b] → [Decidable c] → [Decidable d] →
   xs = if h1 : c
        then if h2 : d then some (t h2 x) :: [] else (g h1 p) :: []
        else if h3 : b then some (f h3 x) :: [] else none :: []

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
--   (j : ¬ b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
--   xs = if h1 : c
--        then if h2 : d
--             then if h4 : b then some (t h2 x) :: [] else some (t h2 x) :: (j h4 p) :: []
--             else if h4 : b then f h1 p :: [] else f h1 p :: j h4 p :: []
--        else if h3 : b then some (g h3 x) :: [] else none :: (j h3 p) :: []
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
  (j : ¬ b → Int → Option Int), [Decidable b] → [Decidable c] → [Decidable d] →
  xs = if h1 : c
       then if h2 : d
            then if h4 : b then some (t h2 x) :: [] else some (t h2 x) :: (j h4 p) :: []
            else if h4 : b then f h1 p :: [] else f h1 p :: j h4 p :: []
       else if h3 : b then some (g h3 x) :: [] else none :: (j h3 p) :: []

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
-- ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
--   r = if h : c then some (t h) else some (e h)
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_14" ]
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
    r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
    r = if h : c then some (t h) else some (e h)

-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   [Decidable c] → r = some (dite c t e) ===>
-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   [Decidable c] → r = if h : c then some (λ x => t h x) else some (λ x => e h x)
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_15" ]
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → r = if h : c then some (λ x => t h x) else some (λ x => e h x)

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
--             (fun (_ : PUnit) => .black :: [])
--             (fun (_ : PUnit) => .transparent :: [])
--             (fun (_ : PUnit) => .red .transparent :: [])
--             (fun (_ : PUnit) => .blue .black :: [])
--             (fun (_ : Nat) => .blue .transparent :: []) )
#testOptimize [ "MatchOverCtor_1" ]
  ∀ (n : Option Nat) (xs : List Color), toColorOne n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
       xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
              (fun (_ : PUnit) => .black :: [])
              (fun (_ : PUnit) => .transparent :: [])
              (fun (_ : PUnit) => .red .transparent :: [])
              (fun (_ : PUnit) => .blue .black :: [])
              (fun (_ : Nat) => .blue .transparent :: []) )

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color),
--    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
--           (fun (_ : PUnit) => .black :: [])
--           (fun (_ : α) => .blue .transparent :: []) )
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_2" ]
  ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color),
    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
           (fun (_ : PUnit) => .black :: [])
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
--          (fun (_ : PUnit) => .black :: [])
--          (fun (_ : PUnit) => .transparent :: [])
--          (fun (_ : PUnit) => .red .transparent :: [])
--          (fun (_ : PUnit) => .blue .black :: [])
--          (fun (a : Nat) =>
--            if a < 10 then .blue .transparent :: []
--            else if a < 100 then .red .black :: []
--            else .red .transparent :: [] ) )
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that simplification rule can transitively detect
-- that all path reduce to constant values
#testOptimize [ "MatchOverCtor_3" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    xs = ( toColorOne.match_1 (fun (_ : Option Nat) => List Color) n
           (fun (_ : PUnit) => .black :: [])
           (fun (_ : PUnit) => .transparent :: [])
           (fun (_ : PUnit) => .red .transparent :: [])
           (fun (_ : PUnit) => .blue .black :: [])
           (fun (a : Nat) =>
             if a < 10 then .blue .transparent :: []
             else if a < 100 then .red .black :: []
             else .red .transparent :: [] ) )

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
--         (fun ( c1 : Color) (c2 : Color) => (λ n => if 0 = n then true else beqColor c1 c2) :: [])
--         (fun ( c1 : Color) (c2 : Color) => (λ n => if 0 = n then true else beqColor c1 c2) :: [])
--         (fun (_ : PUnit) => (λ _n => true) :: [])
--         (fun (_ : PUnit) => (λ _n => true) :: [])
--         (fun (_ : Color) (_ : Color ) => (λ _n => false) :: []) )
-- NOTE: Test cases to ensure that match returning function are properly handled
-- NOTE: Lean4 already applied structural equivalence between beqColorDegree.match_1 and beqColor.match_1
#testOptimize [ "MatchOverCtor_4" ] (norm-result: 1)
  ∀ (x y : Color) (xs : List (Nat → Bool)), beqColorDegree x y :: [] = xs ===>
  ∀ (x y : Color) (xs : List (Nat → Bool)),
   xs = ( beqColor.match_1 (fun (_ : Color) (_ : Color) => List (Nat → Bool)) x y
          (fun ( c1 : Color) (c2 : Color) => (λ n => if 0 = n then true else beqColor c1 c2) :: [])
          (fun ( c1 : Color) (c2 : Color) => (λ n => if 0 = n then true else beqColor c1 c2) :: [])
          (fun (_ : PUnit) => (λ _n => true) :: [])
          (fun (_ : PUnit) => (λ _n => true) :: [])
          (fun (_ : Color) (_ : Color ) => (λ _n => false) :: []) )

-- ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color),
--    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
--           (fun (_ : PUnit) => .black :: [])
--           (fun (_ : α) => .blue .transparent :: []) )
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_5" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Bool),
    let op := if c then [] else .transparent :: [];
    toColorTwo n :: op = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Bool),
    xs = ( toColorTwo.match_1 (fun (_ : Option α) => List Color) n
           (fun (_ : PUnit) =>
             if true = c then .black :: [] else .black :: .transparent :: [])
           (fun (_ : α) =>
             if true = c
             then .blue .transparent :: []
             else .blue .transparent :: .transparent :: []) )

end Tests.ConstCtorProp
