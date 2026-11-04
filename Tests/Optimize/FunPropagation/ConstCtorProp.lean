import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstCtorProp

/-! ## Test objectives to validate that ite/match over constructor propagation is no more applied.

    `funPropagation?` is no more applied on constructor applications: an ite/dite/match argument of a
    constructor is kept in place (e.g., `[Blaster.dite' c (fun _ => some x) (fun _ => none)] = xs` instead
    of `xs = Blaster.dite' c (fun _ => [some x]) (fun _ => [none])`). The test cases below validate that the
    arguments of the constructor are optimized (ite/match normalization, nested ite/match, context reuse,
    functions as ite/match results, dependent match types) without being pushed through the constructor. -/

/-! Test cases to validate that ite over constructor propagation is no more applied. -/

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int), [Decidable c] →
--   (if c then some x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int),
--   [Blaster.dite' c (fun _ => some x) (fun _ => none)] = xs
#testOptimize [ "IteOverCtor_1" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int), [Decidable c] →
    (if c then some x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int),
    [Blaster.dite' c (fun _ => some x) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
--   (if c then (if b then some x else none) else none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
--   [Blaster.dite' c (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none)) (fun _ => none)] = xs
#testOptimize [ "IteOverCtor_2" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then (if b then some x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    [Blaster.dite' c (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none)) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
--   (if c then some x else (if b then some x else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
--   [Blaster.dite' c (fun _ => some x) (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs
#testOptimize [ "IteOverCtor_3" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int), [Decidable b] → [Decidable c] →
    (if c then some x else (if b then some x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int),
    [Blaster.dite' c (fun _ => some x) (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then some x else some y
--     else if b then some x else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   [Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => some y))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs
#testOptimize [ "IteOverCtor_4" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
    [Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => some y))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else some y
--     else if b then some x else none;
--   let op2 := if b then [] else some y :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
--   (Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => some y))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
--   Blaster.dite' b (fun _ => []) (fun _ => [some y]) = xs
#testOptimize [ "IteOverCtor_5" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else some y
    else if b then some x else none;
  let op2 := if b then [] else some y :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x y : Int),
    (Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => some y))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
    Blaster.dite' b (fun _ => []) (fun _ => [some y]) = xs

-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int), [Decidable c] →
--   (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int),
--   [Blaster.dite' c (fun _ => λ n => some (Int.add x n)) (fun _ => λ n => some (Int.add x (Int.neg n)))] = xs
-- NOTE: Test cases to ensure that ite returning function are properly handled (not propagated)
#testOptimize [ "IteOverCtor_6" ]
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int), [Decidable c] →
    (if c then λ n => some (x + n) else λ n => some (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int),
    [Blaster.dite' c (fun _ => λ n => some (Int.add x n)) (fun _ => λ n => some (Int.add x (Int.neg n)))] = xs

-- ∀ (c : Bool) (xs : List (Option Int)) (x : Option Int),
--   (if c then x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int),
--   [Blaster.dite' c (fun _ => x) (fun _ => none)] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "IteOverCtor_7" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int), [Decidable c] →
    (if c then x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Option Int),
    [Blaster.dite' c (fun _ => x) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
--   [Decidable b] → [Decidable c] →
--   (if c then (if b then x else none) else none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
--   [Blaster.dite' c (fun _ => Blaster.dite' b (fun _ => x) (fun _ => none)) (fun _ => none)] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "IteOverCtor_8" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    [Decidable b] → [Decidable c] →
    (if c then (if b then x else none) else none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Option Int),
    [Blaster.dite' c (fun _ => Blaster.dite' b (fun _ => x) (fun _ => none)) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] →
--     (if c then some x else (if b then p else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Blaster.dite' c (fun _ => some x) (fun _ => Blaster.dite' b (fun _ => p) (fun _ => none))] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "IteOverCtor_9" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    [Decidable b] → [Decidable c] →
      (if c then some x else (if b then p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    [Blaster.dite' c (fun _ => some x) (fun _ => Blaster.dite' b (fun _ => p) (fun _ => none))] = xs

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then some x else p
--     else if b then some x else none;
--   op1 :: [] = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "IteOverCtor_10" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else p
    else if b then some x else none;
  op1 :: [] = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    [Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))] = xs

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else p
--     else if b then some x else none;
--   let op2 := if b then [] else p :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   (Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
--   Blaster.dite' b (fun _ => []) (fun _ => [p]) = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "IteOverCtor_11" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    (Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
    Blaster.dite' b (fun _ => []) (fun _ => [p]) = xs

-- ∀ (c : Bool) (x y z : Int),
--   some ((if c then λ n => x + n else λ n => x - n) z) = some y ===>
-- ∀ (c : Bool) (x y z : Int),
--   some y = some (Blaster.dite' (true = c) (λ _ => Int.add x z) (λ _ => Int.add x (Int.neg z)))
-- NOTE: Can be reduced to
--   Blaster.dite' (true = c) (λ _ => y = Int.add x z)) (λ _ => y = Int.add x (Int.neg z))
-- with additional simplification rules.
#testOptimize [ "IteOverCtor_12" ]
  ∀ (c : Bool) (x y z : Int),
    some ((if c then λ n => x + n else λ n => x - n) z) = some y ===>
  ∀ (c : Bool) (x y z : Int),
    some y = some (Blaster.dite' (true = c) (λ _ => Int.add x z) (λ _ => Int.add x (Int.neg z)))

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else p
--     else if b then some x else none;
--   let op2 := if b then if c then [] else p :: [] else p :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   (Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
--   Blaster.dite' b (fun _ => Blaster.dite' c (fun _ => []) (fun _ => [p])) (fun _ => [p]) = xs
-- NOTE: Test cases to ensure that context reuse are properly handled
#testOptimize [ "IteOverCtor_12" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then if c then [] else p :: [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    (Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
    Blaster.dite' b (fun _ => Blaster.dite' c (fun _ => []) (fun _ => [p])) (fun _ => [p]) = xs

-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c then if d then some x else p
--     else if b then some x else none;
--   let op2 := if b then if c ∨ d then [] else p :: [] else p :: []
--   (op1 :: op2) = xs ===>
-- ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
--   (Blaster.dite' c
--     (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
--     (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
--   Blaster.dite' b (fun _ => Blaster.dite' (c ∨ d) (fun _ => []) (fun _ => [p])) (fun _ => [p]) = xs
-- NOTE: Test cases to ensure that context reuse are properly handled
#testOptimize [ "IteOverCtor_13" ]
∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c then if d then some x else p
    else if b then some x else none;
  let op2 := if b then if c ∨ d then [] else p :: [] else p :: []
  (op1 :: op2) = xs ===>
  ∀ (b c d : Prop) (xs : List (Option Int)) (x : Int) (p : Option Int),
    (Blaster.dite' c
      (fun _ => Blaster.dite' d (fun _ => some x) (fun _ => p))
      (fun _ => Blaster.dite' b (fun _ => some x) (fun _ => none))) ::
    Blaster.dite' b (fun _ => Blaster.dite' (c ∨ d) (fun _ => []) (fun _ => [p])) (fun _ => [p]) = xs

/-! Test cases to validate that dite over constructor propagation is no more applied. -/

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--   (if h : c then t h x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
--   [Blaster.dite' c (fun h : c => t h x) (fun _ => none)] = xs
#testOptimize [ "DIteOverCtor_1" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
    (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
    [Blaster.dite' c (fun h : c => t h x) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--   [Decidable b] → [Decidable c] →
--     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
--   [Blaster.dite' c
--     (fun _ => Blaster.dite' b (fun h2 : _ => t h2 x) (fun _ => none))
--     (fun h1 : _ => f h1 none)] = xs
#testOptimize [ "DIteOverCtor_2" ]
 ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
   (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
   [Decidable b] → [Decidable c] →
     (if h1 : c then (if h2 : b then t h2 x else none) else f h1 none) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Option Int) (f : ¬ c → Option Int → Option Int),
    [Blaster.dite' c
      (fun _ => Blaster.dite' b (fun h2 : _ => t h2 x) (fun _ => none))
      (fun h1 : _ => f h1 none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int),
--   [Blaster.dite' c
--     (fun h1 : _ => t h1 x)
--     (fun _ => Blaster.dite' b (fun h2 : _ => f h2 x) (fun _ => none))] = xs
#testOptimize [ "DIteOverCtor_3" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 x else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int),
    [Blaster.dite' c
      (fun h1 : _ => t h1 x)
      (fun _ => Blaster.dite' b (fun h2 : _ => f h2 x) (fun _ => none))] = xs

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
--   [Blaster.dite' c
--     (fun h1 : _ => Blaster.dite' d (fun _ => t h1 x) (fun h2 : _ => f h2 y))
--     (fun _ => Blaster.dite' b (fun h3 : _ => g h3 x) (fun _ => none))] = xs
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
    [Blaster.dite' c
      (fun h1 : _ => Blaster.dite' d (fun _ => t h1 x) (fun h2 : _ => f h2 y))
      (fun _ => Blaster.dite' b (fun h3 : _ => g h3 x) (fun _ => none))] = xs

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
--   (Blaster.dite' c
--     (fun h1 : _ => Blaster.dite' d (fun _ => t h1 x) (fun h2 : _ => f h2 y))
--     (fun _ => Blaster.dite' b (fun h3 : _ => g h3 x) (fun _ => none))) ::
--   Blaster.dite' b (fun h4 : _ => [g h4 y]) (fun _ => []) = xs
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
    (Blaster.dite' c
      (fun h1 : _ => Blaster.dite' d (fun _ => t h1 x) (fun h2 : _ => f h2 y))
      (fun _ => Blaster.dite' b (fun h3 : _ => g h3 x) (fun _ => none))) ::
    Blaster.dite' b (fun h4 : _ => [g h4 y]) (fun _ => []) = xs

-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
--     (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
--   (t : c → Int → Option Int) (e : ¬ c → Int → Option Int),
--   [Blaster.dite' c
--     (fun h : _ => λ n => t h (Int.add x n))
--     (fun h : _ => λ n => e h (Int.add x (Int.neg n)))] = xs
-- NOTE: Test cases to ensure that dite returning function are properly handled (not propagated)
#testOptimize [ "DIteOverCtor_6" ]
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int), [Decidable c] →
      (if h : c then λ n => t h (x + n) else λ n => e h (x - n)) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Int → Option Int)) (x : Int)
    (t : c → Int → Option Int) (e : ¬ c → Int → Option Int),
    [Blaster.dite' c
      (fun h : _ => λ n => t h (Int.add x n))
      (fun h : _ => λ n => e h (Int.add x (Int.neg n)))] = xs

-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
--    (if h : c then t h x else none) :: [] = xs ===>
-- ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
--   [Blaster.dite' c (fun h : _ => t h x) (fun _ => none)] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "DIteOverCtor_7" ]
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int), [Decidable c] →
     (if h : c then t h x else none) :: [] = xs ===>
  ∀ (c : Prop) (xs : List (Option Int)) (x : Int) (t : c → Int → Option Int),
    [Blaster.dite' c (fun h : _ => t h x) (fun _ => none)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
--   (t : b → Int → Int) (f : ¬ c → Int → Option Int),
--   [Blaster.dite' c
--     (fun _ => Blaster.dite' b (fun h2 : _ => some (t h2 x)) (fun _ => none))
--     (fun h1 : _ => f h1 x)] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "DIteOverCtor_8" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then (if h2 : b then some (t h2 x) else none) else f h1 x) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int)
    (t : b → Int → Int) (f : ¬ c → Int → Option Int),
    [Blaster.dite' c
      (fun _ => Blaster.dite' b (fun h2 : _ => some (t h2 x)) (fun _ => none))
      (fun h1 : _ => f h1 x)] = xs

-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
--     (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
-- ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
--   (t : c → Int → Option Int) (f : b → Int → Option Int),
--   [Blaster.dite' c
--     (fun h1 : _ => t h1 x)
--     (fun _ => Blaster.dite' b (fun h2 : _ => f h2 p) (fun _ => none))] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
#testOptimize [ "DIteOverCtor_9" ]
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int), [Decidable b] → [Decidable c] →
      (if h1 : c then t h1 x else (if h2 : b then f h2 p else none)) :: [] = xs ===>
  ∀ (b c : Prop) (xs : List (Option Int)) (x : Int) (p : Int)
    (t : c → Int → Option Int) (f : b → Int → Option Int),
    [Blaster.dite' c
      (fun h1 : _ => t h1 x)
      (fun _ => Blaster.dite' b (fun h2 : _ => f h2 p) (fun _ => none))] = xs

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
--   [Blaster.dite' c
--     (fun h1 : _ => Blaster.dite' d (fun h2 : _ => some (t h2 x)) (fun _ => g h1 p))
--     (fun _ => Blaster.dite' b (fun h3 : _ => some (f h3 x)) (fun _ => none))] = xs
-- NOTE: Test cases to ensure that even non constant ite are not propagated
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
    [Blaster.dite' c
      (fun h1 : _ => Blaster.dite' d (fun h2 : _ => some (t h2 x)) (fun _ => g h1 p))
      (fun _ => Blaster.dite' b (fun h3 : _ => some (f h3 x)) (fun _ => none))] = xs

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
--   (Blaster.dite' c
--     (fun h1 : _ => Blaster.dite' d (fun h2 : _ => some (t h2 x)) (fun _ => f h1 p))
--     (fun _ => Blaster.dite' b (fun h3 : _ => some (g h3 x)) (fun _ => none))) ::
--   Blaster.dite' b (fun _ => []) (fun h4 : _ => [j h4 p]) = xs
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
    (Blaster.dite' c
      (fun h1 : _ => Blaster.dite' d (fun h2 : _ => some (t h2 x)) (fun _ => f h1 p))
      (fun _ => Blaster.dite' b (fun h3 : _ => some (g h3 x)) (fun _ => none))) ::
    Blaster.dite' b (fun _ => []) (fun h4 : _ => [j h4 p]) = xs

-- ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : ¬ true = c → Int → Int),
--   some ((if h : true = c then λ n => t h (x + n) else λ n => f h (x - n)) z) = some y ===>
-- ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : false = c → Int → Int),
--   some y = some (Blaster.dite' (true = c)
--                   (λ h : _ => t h (Int.add x z))
--                   (λ h : _ => f (Blaster.false_eq_of_not_true_eq h) (Int.add x (Int.neg z))))
-- NOTE: Can be reduced to
--   Blaster.dite' (true = c)
--   (λ h : _ => y = t h (Int.add x z))
--   (λ h : _ => y = f (Blaster.false_eq_of_not_true_eq h) (Int.add x (Int.neg z)))
-- with additional simplification rules.
#testOptimize [ "DIteOverCtor_13" ]
  ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : ¬ true = c → Int → Int),
    some ((if h : true = c then λ n => t h (x + n) else λ n => f h (x - n)) z) = some y ===>
  ∀ (c : Bool) (x y z : Int) (t : true = c → Int → Int) (f : false = c → Int → Int),
    some y = some (Blaster.dite' (true = c)
                    (λ h : _ => t h (Int.add x z))
                    (λ h : _ => f (Blaster.false_eq_of_not_true_eq h) (Int.add x (Int.neg z))))

-- ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
--   r = some (dite c t e) ===>
-- ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool),
--   some (Blaster.dite' c t e) = r
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_14" ]
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] →
    r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option Bool) (t : c → Bool) (e : ¬ c → Bool),
    some (Blaster.dite' c t e) = r

-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   [Decidable c] → r = some (dite c t e) ===>
-- ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--   some (Blaster.dite' c t e) = r
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverCtor_15" ]
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → r = some (dite c t e) ===>
  ∀ (c : Prop) (r : Option (Int → Bool)) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    some (Blaster.dite' c t e) = r

/-! Test cases to validate that match over constructor propagation is no more applied. -/

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
--   [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--      (fun (_ : Unit) => .black)
--      (fun (_ : Unit) => .transparent)
--      (fun (_ : Unit) => .red .transparent)
--      (fun (_ : Unit) => .blue .black)
--      (fun (_ : Nat) => .blue .transparent)] = xs
#testOptimize [ "MatchOverCtor_1" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorOne n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
       (fun (_ : Unit) => .black)
       (fun (_ : Unit) => .transparent)
       (fun (_ : Unit) => .red .transparent)
       (fun (_ : Unit) => .blue .black)
       (fun (_ : Nat) => .blue .transparent)] = xs

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color),
--   [toColorTwo.match_1 (fun (_ : Option α) => Color) n
--      (fun (_ : Unit) => .black)
--      (fun (_ : α) => .blue .transparent)] = xs
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_2" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color), toColorTwo n :: [] = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color),
    [toColorTwo.match_1 (fun (_ : Option α) => Color) n
       (fun (_ : Unit) => .black)
       (fun (_ : α) => .blue .transparent)] = xs

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
--   [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--      (fun (_ : Unit) => .black)
--      (fun (_ : Unit) => .transparent)
--      (fun (_ : Unit) => .red .transparent)
--      (fun (_ : Unit) => .blue .black)
--      (fun (a : Nat) =>
--        Blaster.dite' (a < 10)
--          (fun _ => .blue .transparent)
--          (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent)))] = xs
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that the nested ite in the last alternative are normalized
-- while the match is kept as argument of the list constructor
#testOptimize [ "MatchOverCtor_3" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
       (fun (_ : Unit) => .black)
       (fun (_ : Unit) => .transparent)
       (fun (_ : Unit) => .red .transparent)
       (fun (_ : Unit) => .blue .black)
       (fun (a : Nat) =>
         Blaster.dite' (a < 10)
           (fun _ => .blue .transparent)
           (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent)))] = xs

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
--   [beqColor.match_1 (fun (_ : Color) (_ : Color) => Nat → Bool) x y
--      (fun (c1 : Color) (c2 : Color) =>
--        λ n => Blaster.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2))
--      (fun (c1 : Color) (c2 : Color) =>
--        λ n => Blaster.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2))
--      (fun (_ : Unit) => λ _n => true)
--      (fun (_ : Unit) => λ _n => true)
--      (fun (_ : Color) (_ : Color) => λ _n => false)] = xs
-- NOTE: Test cases to ensure that match returning function are properly handled (not propagated)
-- NOTE: Lean4 already applied structural equivalence between beqColorDegree.match_1 and beqColor.match_1
#testOptimize [ "MatchOverCtor_4" ] (norm-result: 1)
  ∀ (x y : Color) (xs : List (Nat → Bool)), beqColorDegree x y :: [] = xs ===>
  ∀ (x y : Color) (xs : List (Nat → Bool)),
    [beqColor.match_1 (fun (_ : Color) (_ : Color) => Nat → Bool) x y
       (fun (c1 : Color) (c2 : Color) =>
         λ n => Blaster.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2))
       (fun (c1 : Color) (c2 : Color) =>
         λ n => Blaster.dite' (0 = n) (fun _ => true) (fun _ => beqColor c1 c2))
       (fun (_ : Unit) => λ _n => true)
       (fun (_ : Unit) => λ _n => true)
       (fun (_ : Color) (_ : Color) => λ _n => false)] = xs

-- ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop), [Decidable c] →
--   let op := if c then [] else .transparent :: [];
--   toColorTwo n :: op = xs ===>
-- ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop),
--   (toColorTwo.match_1 (fun (_ : Option α) => Color) n
--      (fun (_ : Unit) => .black)
--      (fun (_ : α) => .blue .transparent)) ::
--   Blaster.dite' c (fun _ => []) (fun _ => [.transparent]) = xs
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverCtor_5" ] (norm-result: 1)
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop), [Decidable c] →
    let op := if c then [] else .transparent :: [];
    toColorTwo n :: op = xs ===>
  ∀ (α : Type) (n : Option α) (xs : List Color) (c : Prop),
    (toColorTwo.match_1 (fun (_ : Option α) => Color) n
       (fun (_ : Unit) => .black)
       (fun (_ : α) => .blue .transparent)) ::
    Blaster.dite' c (fun _ => []) (fun _ => [.transparent]) = xs

-- ∀ (n : Option Nat) (xs : List Color), toColorThree n :: [] = xs ===>
-- ∀ (n : Option Nat) (xs : List Color),
--   [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--      (fun (_ : Unit) => .black)
--      (fun (_ : Unit) => .transparent)
--      (fun (_ : Unit) => .red .transparent)
--      (fun (_ : Unit) => .blue .black)
--      (fun (a : Nat) =>
--        Blaster.dite' (a < 10)
--          (fun _ => .blue .transparent)
--          (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent))),
--    toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--        (fun (_ : Unit) => .black)
--        (fun (_ : Unit) => .transparent)
--        (fun (_ : Unit) => .red .transparent)
--        (fun (_ : Unit) => .blue .black)
--        (fun (a : Nat) =>
--          Blaster.dite' (a < 10)
--            (fun _ => .blue .transparent)
--            (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent)))] = xs
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that context reuse are properly handled
#testOptimize [ "MatchOverCtor_6" ] (norm-result: 1)
  ∀ (n : Option Nat) (xs : List Color), toColorThree n :: toColorThree n :: [] = xs ===>
  ∀ (n : Option Nat) (xs : List Color),
    [toColorOne.match_1 (fun (_ : Option Nat) => Color) n
       (fun (_ : Unit) => .black)
       (fun (_ : Unit) => .transparent)
       (fun (_ : Unit) => .red .transparent)
       (fun (_ : Unit) => .blue .black)
       (fun (a : Nat) =>
         Blaster.dite' (a < 10)
           (fun _ => .blue .transparent)
           (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent))),
     toColorOne.match_1 (fun (_ : Option Nat) => Color) n
         (fun (_ : Unit) => .black)
         (fun (_ : Unit) => .transparent)
         (fun (_ : Unit) => .red .transparent)
         (fun (_ : Unit) => .blue .black)
         (fun (a : Nat) =>
           Blaster.dite' (a < 10)
             (fun _ => .blue .transparent)
             (fun _ => Blaster.dite' (a < 100) (fun _ => .red .black) (fun _ => .red .transparent)))] = xs

/-! Test cases to validate that match over constructor propagation is no more applied when the match
    type is a dependent lambda (indexed inductive datatype in the discriminators and/or in the return type). -/

inductive FnIdx : Nat → Type where
  | z : FnIdx 0
  | s : FnIdx 1

def fnVal (n : Nat) (v : FnIdx n) : Nat :=
  match n, v with
  | .(0), .z => 1
  | .(1), .s => 2

def fnOut (n : Nat) (v : FnIdx n) : FnIdx n :=
  match n, v with
  | .(0), .z => .z
  | .(1), .s => .s

-- ∀ (k : Nat) (w : FnIdx k) (x : Option Nat), some (fnVal k w) = x ===>
-- ∀ (k : Nat) (w : FnIdx k) (x : Option Nat),
--   some (match k, w with
--         | .(0), .z => 1
--         | .(1), .s => 2) = x
-- NOTE: Test case to validate that the match with a dependent binder (`v : FnIdx n`) in its match type
-- is kept as argument of the constructor (the constructor is not pushed in the alternatives).
#testOptimize [ "MatchOverCtor_7" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (x : Option Nat), some (fnVal k w) = x ===>
  ∀ (k : Nat) (w : FnIdx k) (x : Option Nat),
    some (match k, w with
          | .(0), .z => 1
          | .(1), .s => 2) = x

-- ∀ (k : Nat) (w : FnIdx k) (y : Option (FnIdx k)), some (fnOut k w) = y ===>
-- ∀ (k : Nat) (w : FnIdx k) (y : Option (FnIdx k)),
--   some (match (generalizing := false) k, w with
--         | .(0), .z => FnIdx.z
--         | .(1), .s => FnIdx.s) = y
-- NOTE: Test case to validate that the match whose return type depends on a discriminator (`FnIdx n`)
-- is kept as argument of the constructor with its original match type (the constructor is not pushed
-- in the alternatives, hence no motive `Option (FnIdx n)` has to be computed).
#testOptimize [ "MatchOverCtor_8" ] (norm-result: 1)
  ∀ (k : Nat) (w : FnIdx k) (y : Option (FnIdx k)), some (fnOut k w) = y ===>
  ∀ (k : Nat) (w : FnIdx k) (y : Option (FnIdx k)),
    some (match (generalizing := false) k, w with
          | .(0), .z => FnIdx.z
          | .(1), .s => FnIdx.s) = y

end Tests.ConstCtorProp
