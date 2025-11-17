import Lean
import Tests.Utils

open Lean Elab Command Term Meta

namespace Tests.ConstFunProp

/-! ## Test objectives to validate ite/match over function propagation. -/

-- Test cases when all arguments ctor or match/ite over ctor, prop or fun
-- Test cases when eq true/false
-- Test cases to validate when rule must not be applied when ite/match is a function

/-! Test cases to validate when ite over function propagation must be applied. -/

-- ∀ (c : Bool) (x y : Int), some y = if c then some x else none ===>
-- ∀ (c : Bool) (x y : Int), true = c ∧ some x = some y
-- NOTE: Can be reduced to `true = c ∧ x = y` with additional simplification rules
#testOptimize [ "IteOverFun_1" ]
  ∀ (c : Bool) (x y : Int), some y = if c then some x else none ===>
  ∀ (c : Bool) (x y : Int), true = c ∧ some x = some y

-- ∀ (b c : Bool) (x y z : Int),
--  (if c then (if b then some x else none) else some y) = some z ===>
-- ∀ (b c : Bool) (x y z : Int),
--  (false = c → some y = some z) ∧
--  (true = c → (true = b ∧ some x = some z))
-- NOTE: Can be reduced to `(false = c → y = z) ∧ (true = c → (true = b ∧ x = z))`
-- with additional simplification rules
#testOptimize [ "IteOverFun_2" ]
  ∀ (b c : Bool) (x y z : Int),
    (if c then (if b then some x else none) else some y) = some z ===>
  ∀ (b c : Bool) (x y z : Int),
    (false = c → some y = some z) ∧
    (true = c → (true = b ∧ some x = some z))

-- ∀ (b c : Bool) (x y z : Int),
--    (if c then some x else (if b then some y else none)) = some z ===>
-- ∀ (b c : Bool) (xs : List (Option Int)) (x : Int),
--   (false = c → (true = b ∧ some y = some z)) ∧
--   (false = c → (true = b ∧ (true = b → some y = some z))) ∧
-- NOTE: Can be reduced to `(false = c → (true = b ∧ y = z)) ∧ (true = c → x = z)`
-- with additional simplification rules
#testOptimize [ "IteOverFun_3" ]
  ∀ (b c : Bool) (x y z : Int),
     (if c then some x else (if b then some y else none)) = some z ===>
  ∀ (b c : Bool) (x y z : Int),
     (false = c → (true = b ∧ some y = some z)) ∧
     (true = c → some x = some z)


-- ∀ (b c d : Bool) (x y z : Int),
-- let op1 :=
--   if c
--   then if d then some x else some y
--   else if b then some x else none;
--  op1 = some z ===>
-- ∀ (b c d : Bool) (x y z : Int),
--  (false = c → (true = b ∧ some x = some z)) ∧
--  (true = c → ((false = d → some y = some z) ∧ (true = d → some x = some z)))
-- NOTE: Can be reduced to
--  (false = c → (true = b ∧ x = z)) ∧
--  (true = c → ((false = d → y = z) ∧ (true = d → x = z)))
-- with additional simplification rules
#testOptimize [ "IteOverFun_4" ]
∀ (b c d : Bool) (x y z : Int),
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 = some z ===>
∀ (b c d : Bool) (x y z : Int),
  (false = c → (true = b ∧ some x = some z)) ∧
  (true = c → ((false = d → some y = some z) ∧ (true = d → some x = some z)))


-- ∀ (b c d : Bool) (x y z : Int),
-- let op1 :=
--   if c
--   then if d then some x else some y
--   else if b then some x else none;
-- let op2 := if b then some z else some y
--  op1 = op2 ===>
-- ∀ (b c d : Bool) (x y z : Int),
-- (false = b → true = c ∧ (true = d → some x = some y)) ∧
-- (true = b →
--     (false = c → some x = some z) ∧
--     (true = c → (false = d → some y = some z) ∧ (true = d → some x = some z)))
-- NOTE: Can be reduced to
-- (false = b → true = c ∧ (true = d → x = y)) ∧
-- (true = b →
--     (false = c → x = z) ∧
--     (true = c → (false = d → y = z) ∧ (true = d → x = z)))
-- with additional simplification rules
#testOptimize [ "IteOverFun_5" ]
∀ (b c d : Bool) (x y z : Int),
  let op1 :=
    if c then if d then some x else some y
    else if b then some x else none;
  let op2 := if b then some z else some y
  op1 = op2 ===>
∀ (b c d : Bool) (x y z : Int),
   (false = b → true = c ∧ (true = d → some x = some y)) ∧
   (true = b →
       (false = c → some x = some z) ∧
       (true = c → (false = d → some y = some z) ∧ (true = d → some x = some z)))

-- ∀ (c : Bool) (w x y z : Int), List.length (if c then [w, x, y] else [y, z]) > 0 ===> True
#testOptimize [ "IteOverFun_6" ]
  ∀ (c : Bool) (w x y z : Int), List.length (if c then [w, x, y] else [y, z]) > 0 ===> True

-- ∀ (c : Prop) (xs : List Int) (w x y : Int), [Decidable c] →
--   List.length (if c then x :: xs else [w, x, y]) > 0 ===>
-- ∀ (c : Prop) (xs : List Int),
--   0 < Solver.dite' c (fun _ => Nat.add 1 (List.length xs)) (fun _ => 3)
-- NOTE: Can be reduced to true with additional simplification rules on
-- relational operators and ite propagation rules.
#testOptimize [ "IteOverFun_7" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List Int) (w x y : Int), [Decidable c] →
    List.length (if c then x :: xs else [w, x, y]) > 0 ===>
  ∀ (c : Prop) (xs : List Int),
    0 < Solver.dite' c (fun _ => Nat.add 1 (List.length xs)) (fun _ => 3)

-- ∀ (a b c : Bool), true = if c then a else b ===>
-- ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)
-- NOTE: Test case to validate ite propagation on equality true
#testOptimize [ "IteOverFun_8" ]
  ∀ (a b c : Bool), true = if c then a else b ===>
  ∀ (a b c : Bool), (false = c → true = b) ∧ (true = c → true = a)

-- ∀ (a b c : Bool), false = if c then a else b ===>
-- ∀ (a b c : Bool), (false = c → false = b) ∧ (true = c → false = a)
-- NOTE: Test case to validate ite propagation on equality false
#testOptimize [ "IteOverFun_9" ]
  ∀ (a b c : Bool), false = if c then a else b ===>
  ∀ (a b c : Bool), (false = c → false = b) ∧ (true = c → false = a)

--  ∀ (c : Bool) (x y z : Int),
--   (if c then λ n => some (x + n) else λ n => some (x - n)) z = some y ===>
-- ∀ (c : Bool) (x y z : Int),
--  (false = c → some y = some (Int.add x (Int.neg z))) ∧
--  (true = c → some y = some (Int.add x z))
-- NOTE: Test cases to ensure that ite returning function are properly handled
-- NOTE: Can be reduced to
--  (false = c → y = Int.add x (Int.neg z)) ∧
--  (true = c → y = Int.add x z)
-- with additional simplification rules
#testOptimize [ "IteOverFun_10" ]
  ∀ (c : Bool) (x y z : Int),
    (if c then λ n => some (x + n) else λ n => some (x - n)) z = some y ===>
  ∀ (c : Bool) (x y z : Int),
    (false = c → some y = some (Int.add x (Int.neg z))) ∧
    (true = c → some y = some (Int.add x z))

-- ∀ (α : Type) (c : Bool) (w x y z : α) (lt : α → α → Bool), [BEq α] →
--   List.lex (if c then [w, x, y] else [y, z]) [w, y, z] lt ===>
-- ∀ (α : Type) (c : Bool) (w x y z : α) (lt : α → α → Bool), [BEq α] →
--   (false = c → true = (lt y w || (lt z y || z == y) && y == w)) ∧
--   (true = c → true = (lt w w || (lt x y || lt y z && x == y) && w == w))
-- NOTE: Test case to consider implicit parameters
#testOptimize [ "IteOverFun_10" ]
  ∀ (α : Type) (c : Bool) (w x y z : α) (lt : α → α → Bool), [BEq α] →
    List.lex (if c then [w, x, y] else [y, z]) [w, y, z] lt ===>
  ∀ (α : Type) (c : Bool) (w x y z : α) (lt : α → α → Bool), [BEq α] →
    (false = c → true = (lt y w || (lt z y || z == y) && y == w)) ∧
    (true = c → true = (lt w w || (lt x y || lt y z && x == y) && w == w))

/-! Test cases to validate when ite over function propagation must NOT be applied. -/

-- ∀ (c : Prop) (x : Option Int) (y : Int), [Decidable c] →
--   (if c then x else none) = some y ===>
-- ∀ (c : Prop) (x : Option Int) (y : Int),
--   some y = Solver.dite' c (fun _ => x) (fun _ => none)
-- NOTE: Test cases to ensure that non constant ite cannot be propagated
#testOptimize [ "IteOverFunUnchanged_1" ]
  ∀ (c : Prop) (x : Option Int) (y : Int), [Decidable c] →
    (if c then x else none) = some y ===>
  ∀ (c : Prop) (x : Option Int) (y : Int),
    some y = Solver.dite' c (fun _ => x) (fun _ => none)

-- ∀ (b c : Prop) (x : Option Int) (y z : Int), [Decidable b] → [Decidable c] →
--   (if c then (if b then x else none) else some y) = some z ===>
-- ∀ (b c : Prop) (x : Option Int) (y z : Int),
--   some z = Solver.dite' c
--            (fun _ => Solver.dite' b (fun _ => x) (fun _ => none))
--            (fun _ => some y)
-- NOTE: Test cases to ensure that non constant ite cannot be propagated
#testOptimize [ "IteOverFunUnchanged_2" ]
  ∀ (b c : Prop) (x : Option Int) (y z : Int), [Decidable b] → [Decidable c] →
    (if c then (if b then x else none) else some y) = some z ===>
  ∀ (b c : Prop) (x : Option Int) (y z : Int),
    some z = Solver.dite' c
             (fun _ => Solver.dite' b (fun _ => x) (fun _ => none))
             (fun _ => some y)

-- ∀ (b c : Prop) (x : Int) (y z : Option Int), [Decidable b] → [Decidable c] →
--    (if c then some x else (if b then y else none)) = z ===>
-- ∀ (b c : Prop) (x : Int) (y z : Option Int),
--    z = Solver.dite' c
--        (fun _ => some x)
--        (fun _ => Solver.dite' b (fun _ => y) (fun _ => none))
-- NOTE: Test cases to ensure that non constant ite cannot be propagated
#testOptimize [ "IteOverFunUnchanged_3" ]
  ∀ (b c : Prop) (x : Int) (y z : Option Int), [Decidable b] → [Decidable c] →
     (if c then some x else (if b then y else none)) = z ===>
  ∀ (b c : Prop) (x : Int) (y z : Option Int),
     z = Solver.dite' c
         (fun _ => some x)
         (fun _ => Solver.dite' b (fun _ => y) (fun _ => none))

-- ∀ (b c d : Prop) (x y : Int) (z : Option Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if c
--     then if d then some x else some y
--     else if b then some x else none;
--   op1 = z ===>
-- ∀ (b c d : Prop) (x y : Int) (z : Option Int),
--    z = Solver.dite' c
--        (fun _ => Solver.dite' d (fun _ => some x) (fun _ => some y))
--        (fun _ => Solver.dite' b (fun _ => some x) (fun _ => none))
-- NOTE: Test cases to ensure that ite cannot be propagated when at
-- least one function's argument is not a constant.
#testOptimize [ "IteOverFunUnchanged_4" ]
∀ (b c d : Prop) (x y : Int) (z : Option Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if c
    then if d then some x else some y
    else if b then some x else none;
  op1 = z ===>
∀ (b c d : Prop) (x y : Int) (z : Option Int),
   z = Solver.dite' c
       (fun _ => Solver.dite' d (fun _ => some x) (fun _ => some y))
       (fun _ => Solver.dite' b (fun _ => some x) (fun _ => none))

-- ∀ (c : Prop) (xs : List Int) (w x : Int), [Decidable c] →
--   List.length (if c then [w, x] else xs) > 0 ===>
-- ∀ (c : Prop) (xs : List Int) (w x : Int),
--   0 < List.length (Solver.dite' c (fun _ => [w, x]) (fun _ => xs))
#testOptimize [ "IteOverFunUnchanged_5" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List Int) (w x : Int), [Decidable c] →
    List.length (if c then [w, x] else xs) > 0 ===>
  ∀ (c : Prop) (xs : List Int) (w x : Int),
    0 < List.length (Solver.dite' c (fun _ => [w, x]) (fun _ => xs))

-- ∀ (a b x : Bool) (c : Prop), [Decidable c] → x = if c then a else b ===>
-- ∀ (a b x : Bool) (c : Prop), x = Solver.dite' c (fun _ => a) (fun _ => b)
#testOptimize [ "IteOverFunUnchanged_6" ]
  ∀ (a b x : Bool) (c : Prop), [Decidable c] → x = if c then a else b ===>
  ∀ (a b x : Bool) (c : Prop), x = Solver.dite' c (fun _ => a) (fun _ => b)


/-! Test cases to validate when dite over function propagation must be applied. -/

-- ∀ (c : Bool) (x y : Int) (f : c → Int → Int),
--   some y = if h : c then some (f h x) else none ===>
-- ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
--   true = c ∧ ∀ (h : true = c), some y = some (f h x)
-- NOTE: Can be reduced to true = c ∧ ∀ (h : true = c), y = f h x
-- with additional simplification rules
#testOptimize [ "DIteOverFun_1" ]
  ∀ (c : Bool) (x y : Int) (f : c → Int → Int),
    some y = if h : c then some (f h x) else none ===>
  ∀ (c : Bool) (x y : Int) (f : true = c → Int → Int),
    true = c ∧ ∀ (h : true = c), some y = some (f h x)

-- ∀ (b c : Bool) (x y z : Int) (f : ¬ c → Int → Int) (g : b → Int → Int),
--   (if h1 : c then (if h2 : b then some (g h2 x) else none) else some (f h1 y)) = some z ===>
-- ∀ (b c : Bool) (x y z : Int) (f : false = c → Int → Int) (g : true = b → Int → Int),
--   (∀ (h1 : false = c), some z = some (f h1 y)) ∧
--   (true = c → (true = b ∧ ∀ (h2 : true = b), some z = some (g h2 x)))
-- NOTE: Can be reduced to
-- (∀ (h1 : false = c), z = f h1 y) ∧
-- (true = c → (true = b ∧ ∀ (h2 : true = b), z = g h2 x))
-- with additional simplification rules
#testOptimize [ "DIteOverFun_2" ]
  ∀ (b c : Bool) (x y z : Int) (f : ¬ c → Int → Int) (g : b → Int → Int),
    (if h1 : c then (if h2 : b then some (g h2 x) else none) else some (f h1 y)) = some z ===>
  ∀ (b c : Bool) (x y z : Int) (f : false = c → Int → Int) (g : true = b → Int → Int),
    (∀ (h1 : false = c), some z = some (f h1 y)) ∧
    (true = c → (true = b ∧ ∀ (h2 : true = b), some z = some (g h2 x)))

-- ∀ (b c : Bool) (x y z : Int) (f : c → Int → Int) (g : b → Int → Int),
--    (if h1 : c then some (f h1 x) else (if h2 : b then some (g h2 y) else none)) = some z ===>
-- ∀ (b c : Bool) (x y z : Int) (f : true = c → Int → Int) (g : true = b → Int → Int),
--    (false = c → (true = b ∧ ∀ (h2 : true = b), some z = some (g h2 y))) ∧
--    (∀ (h1 : true = c), some z = some (f h1 x))
-- NOTE: Can be reduced to
--    (false = c → (true = b ∧ ∀ (h2 : true = b), z = g h2 y)) ∧
--    (∀ (h1 : true = c), z = f h1 x)
-- with additional simplification rules
#testOptimize [ "DIteOverFun_3" ]
  ∀ (b c : Bool) (x y z : Int) (f : c → Int → Int) (g : b → Int → Int),
     (if h1 : c then some (f h1 x) else (if h2 : b then some (g h2 y) else none)) = some z ===>
  ∀ (b c : Bool) (x y z : Int) (f : true = c → Int → Int) (g : true = b → Int → Int),
     (false = c → (true = b ∧ ∀ (h2 : true = b), some z = some (g h2 y))) ∧
     (∀ (h1 : true = c), some z = some (f h1 x))

-- ∀ (b c d : Bool) (x y z : Int)
--   (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
--   let op1 :=
--     if h1 : c
--     then if h2 : d then some (g h2 x) else some (f h1 y)
--     else if h3 : b then some (t h3 x) else none;
--   op1 = some z ===>
-- ∀ (b c d : Bool) (x y z : Int)
--   (f : true = c → Int → Int) (g : true = d → Int → Int) (t : true = b → Int → Int),
--   (false = c → (true = b ∧ ∀ (h3 : true = b), some z = some (t h3 x))) ∧
--   ∀ (h1 : true = c),
--     (false = d → some z = some (f h1 y)) ∧
--     ∀ (h2 : true = d), some z = some (g h2 x)
-- NOTE: Can be reduced to
--   (false = c → (true = b ∧ ∀ (h3 : true = b), z = t h3 x)) ∧
--   ∀ (h1 : true = c),
--     (false = d → z = f h1 y) ∧
--     ∀ (h2 : true = d), z = g h2 x
-- with additional simplification rules
#testOptimize [ "DIteOverFun_4" ]
∀ (b c d : Bool) (x y z : Int)
  (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
  let op1 :=
    if h1 : c
    then if h2 : d then some (g h2 x) else some (f h1 y)
    else if h3 : b then some (t h3 x) else none;
  op1 = some z ===>
∀ (b c d : Bool) (x y z : Int)
  (f : true = c → Int → Int) (g : true = d → Int → Int) (t : true = b → Int → Int),
  (false = c → (true = b ∧ ∀ (h3 : true = b), some z = some (t h3 x))) ∧
  ∀ (h1 : true = c),
    (false = d → some z = some (f h1 y)) ∧
    ∀ (h2 : true = d), some z = some (g h2 x)


-- ∀ (b c d : Bool) (x y z : Int)
--   (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
--   let op1 :=
--     if h1 : c then if h2 : d then some (g h2 x) else some (f h1 y)
--     else if h3 : b then some (t h3 x) else none;
--   let op2 := if h4 : b then some (t h4 z) else some y
--   op1 = op2 ===>
-- ∀ (b c d : Bool) (x y z : Int)
--   (f : true = c → Int → Int) (g : true = d → Int → Int) (t : true = b → Int → Int),
--   (false = b →
--       true = c ∧
--       ∀ (h1 : true = c), (false = d → some y = some (f h1 y)) ∧
--       ∀ (h2 : true = d), some y = some (g h2 x)) ∧
--    ∀ (h4 : true = b),
--      (false = c → some (t h4 x) = some (t h4 z)) ∧
--      ∀ (h1 : true = c), (false = d → some (f h1 y) = some (t h4 z)) ∧
--      ∀ (h2 : true = d), some (g h2 x) = some (t h4 z)
-- NOTE: Can be reduced to
--   (false = b →
--       true = c ∧
--       ∀ (h1 : true = c), (false = d → y = f h1 y) ∧
--       ∀ (h2 : true = d), y = g h2 x) ∧
--    ∀ (h4 : true = b),
--      (false = c → (t h4 x) = t h4 z) ∧
--      ∀ (h1 : true = c), (false = d → (f h1 y) = t h4 z) ∧
--      ∀ (h2 : true = d), (g h2 x) = t h4 z
-- with additional simplification rule
#testOptimize [ "DIteOverFun_5" ]
∀ (b c d : Bool) (x y z : Int)
  (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
  let op1 :=
    if h1 : c then if h2 : d then some (g h2 x) else some (f h1 y)
    else if h3 : b then some (t h3 x) else none;
  let op2 := if h4 : b then some (t h4 z) else some y
  op1 = op2 ===>
∀ (b c d : Bool) (x y z : Int)
  (f : true = c → Int → Int) (g : true = d → Int → Int) (t : true = b → Int → Int),
    (false = b →
        true = c ∧
          ∀ (h1 : true = c), (false = d → some y = some (f h1 y)) ∧
          ∀ (h2 : true = d), some y = some (g h2 x)) ∧
    ∀ (h4 : true = b),
        (false = c → some (t h4 x) = some (t h4 z)) ∧
        ∀ (h1 : true = c), (false = d → some (f h1 y) = some (t h4 z)) ∧
        ∀ (h2 : true = d), some (g h2 x) = some (t h4 z)


-- ∀ (c : Bool) (w x y z : Int) (f : c → Int → Int),
--   List.length (if h : c then [w, (f h x), y] else [y, z]) > 0 ===> True
#testOptimize [ "DIteOverFun_6" ]
  ∀ (c : Bool) (w x y z : Int) (f : c → Int → Int),
    List.length (if h : c then [w, (f h x), y] else [y, z]) > 0 ===> True

-- ∀ (c : Prop) (xs : List Int) (w x y : Int) (f : ¬ c → Int → Int), [Decidable c] →
--   List.length (if h : c then x :: xs else [w, x, f h y]) > 0 ===>
-- ∀ (c : Prop) (xs : List Int),
--   0 < Solver.dite' c (fun _ => Nat.add 1 (List.length xs)) (fun _ => 3)
-- NOTE: Can be reduced to true with additional simplification rules on
-- relational operators and ite propagation rules.
#testOptimize [ "DIteOverFun_7" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List Int) (w x y : Int) (f : ¬ c → Int → Int), [Decidable c] →
    List.length (if h : c then x :: xs else [w, x, f h y]) > 0 ===>
  ∀ (c : Prop) (xs : List Int),
    0 < Solver.dite' c (fun _ => Nat.add 1 (List.length xs)) (fun _ => 3)

-- ∀ (a b c : Bool) (f : c → Bool → Bool), true = if h : c then f h a else b ===>
-- ∀ (a b c : Bool) (f : true = c → Bool → Bool),
--   (false = c → true = b) ∧ (∀ (h : true = c),  true = f h a)
-- NOTE: Test case to validate dite propagation on equality true
#testOptimize [ "DIteOverFun_8" ]
  ∀ (a b c : Bool) (f : c → Bool → Bool), true = if h : c then f h a else b ===>
  ∀ (a b c : Bool) (f : true = c → Bool → Bool),
    (false = c → true = b) ∧ (∀ (h : true = c),  true = f h a)

-- ∀ (a b c : Bool) (f : c → Bool → Bool), false = if h : c then f h a else b ===>
-- ∀ (a b c : Bool) (f : true = c → Bool → Bool),
--   (false = c → false = b) ∧ (∀ (h : true = c), false = f h a)
-- NOTE: Test case to validate dite propagation on equality false
#testOptimize [ "DIteOverFun_9" ]
  ∀ (a b c : Bool) (f : c → Bool → Bool), false = if h : c then f h a else b ===>
  ∀ (a b c : Bool) (f : true = c → Bool → Bool),
    (false = c → false = b) ∧ (∀ (h : true = c), false = f h a)


-- ∀ (c : Prop) (x y z : Int) (f : c → Int → Int), [Decidable c] →
--   (if h : c then λ n => some ((f h x) + n) else λ n => some (x - n)) z = some y ===>
-- ∀ (c : Prop) (x y z : Int) (f : c → Int → Int),
--   (∀ (h : c), some y = some (Int.add z (f h x))) ∧
--   (¬ c → some y = some (Int.add x (Int.neg z)))
-- NOTE: Test cases to ensure that ite returning function are properly handled
-- NOTE: Can be reduced to
--   (∀ (h : c), y = Int.add z (f h x)) ∧
--   (¬ c → y = Int.add x (Int.neg z))
-- with additional simplification rules
#testOptimize [ "DIteOverFun_10" ]
  ∀ (c : Prop) (x y z : Int) (f : c → Int → Int), [Decidable c] →
    (if h : c then λ n => some ((f h x) + n) else λ n => some (x - n)) z = some y ===>
  ∀ (c : Prop) (x y z : Int) (f : c → Int → Int),
    (∀ (h : c), some y = some (Int.add z (f h x))) ∧
    (¬ c → some y = some (Int.add x (Int.neg z)))

-- ∀ (c : Prop) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] → true = (dite c t e) ===>
-- ∀ (c : Prop) (t : c → Bool) (e : ¬ c → Bool),
--  (∀ (h : c), true = t h) ∧
--  (∀ (h : ¬ c), true = e h)
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverFun_11" ]
  ∀ (c : Prop) (t : c → Bool) (e : ¬ c → Bool), [Decidable c] → true = (dite c t e) ===>
  ∀ (c : Prop) (t : c → Bool) (e : ¬ c → Bool),
    (∀ (h : c), true = t h) ∧
    (∀ (h : ¬ c), true = e h)

-- ∀ (c : Prop) (x : Int) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--  [Decidable c] → true = dite c t e x ===>
-- ∀ (c : Prop) (x : Int) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
--  (∀ (h : c), true = t h x) ∧
--  (∀ (h : ¬ c), true = e h x)
-- NOTE: Test cases to ensure that quantified functions passed to dite are properly handled.
#testOptimize [ "DIteOverFun_12" ]
  ∀ (c : Prop) (x : Int) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    [Decidable c] → true = dite c t e x ===>
  ∀ (c : Prop) (x : Int) (t : c → Int → Bool) (e : ¬ c → Int → Bool),
    (∀ (h : c), true = t h x) ∧
    (∀ (h : ¬ c), true = e h x)

-- ∀ (α : Type) (c : Prop) (w x y z : α) (lt : α → α → Bool) (f : c → α → α),
--   [Decidable c] → [BEq α] →
--   List.lex (if h : c then [w, f h x, y] else [y, z]) [w, y, z] lt ===>
-- ∀ (α : Type) (c : Prop) (w x y z : α) (lt : α → α → Bool) (f : c → α → α), [BEq α] →
--   (∀ (h : c), true = (lt w w || (lt (f h x) y || lt y z && (f h x) == y) && w == w)) ∧
--   (¬ c → true = (lt y w || (lt z y || z == y) && y == w))
-- NOTE: Test case to consider implicit parameters
#testOptimize [ "DIteOverFun_13" ]
  ∀ (α : Type) (c : Prop) (w x y z : α) (lt : α → α → Bool) (f : c → α → α),
    [Decidable c] → [BEq α] →
    List.lex (if h : c then [w, f h x, y] else [y, z]) [w, y, z] lt ===>
  ∀ (α : Type) (c : Prop) (w x y z : α) (lt : α → α → Bool) (f : c → α → α), [BEq α] →
    (∀ (h : c), true = (lt w w || (lt (f h x) y || lt y z && (f h x) == y) && w == w)) ∧
    (¬ c → true = (lt y w || (lt z y || z == y) && y == w))

-- ∀ (xs : Array Int) (i j : Nat) (z : Int),
--   some z = if h1 : i < xs.1.length
--            then if i = j
--                 then if h2 : j < xs.1.length then some xs[j] else none
--                 else some xs[i]
--            else some 2 ===>
-- ∀ (xs : Array Int) (i : Nat) (z : Int),
--   (¬ i < xs.1.length → some z = some 2) ∧
--   ∀ (h1 : i < xs.1.length), some z = some (List.get xs.1 ⟨i, h1⟩)
-- NOTE: Test case can be reduced to the following with additional simplification rules:
-- ∀ (xs : Array Int) (i : Nat) (z : Int),
--   (¬ i < xs.1.length → z = 2) ∧
--   ∀ (h1 : i < xs.1.length), z = List.get xs.1 ⟨i, h1⟩
#testOptimize [ "DIteOverFun_14" ] (norm-result: 1)
  ∀ (xs : Array Int) (i j : Nat) (z : Int),
    some z = if h1 : i < xs.1.length
             then if i = j
                  then if h2 : j < xs.1.length then some xs[j] else none
                  else some xs[i]
             else some 2 ===>
  ∀ (xs : Array Int) (i j : Nat) (z : Int),
    (¬i < xs.1.length → some z = some (Int.ofNat 2)) ∧
        ∀ (h1 : i < xs.1.length),
          (¬i = j → some z = some (xs.1.get ⟨i, h1⟩)) ∧
            (i = j → j < xs.1.length ∧ ∀ (h2 : j < xs.1.length), some z = some (xs.1.get ⟨j, h2⟩))

/-! Test cases to validate when dite over function propagation must NOT be applied. -/

-- ∀ (c : Prop) (x : Option Int) (y : Int) (f : c → Option Int → Option Int), [Decidable c] →
--    (if h : c then f h x else none) = some y ===>
-- ∀ (c : Prop) (x : Option Int) (y : Int) (f : c → Option Int → Option Int),
--   some y = Solver.dite' c (fun h : _ => f h x) (fun _ => none)
-- NOTE: Test cases to ensure that non constant dite cannot be propagated
#testOptimize [ "DIteOverFunUnchanged_1" ]
  ∀ (c : Prop) (x : Option Int) (y : Int) (f : c → Option Int → Option Int), [Decidable c] →
     (if h : c then f h x else none) = some y ===>
  ∀ (c : Prop) (x : Option Int) (y : Int) (f : c → Option Int → Option Int),
    some y = Solver.dite' c (fun h : _ => f h x) (fun _ => none)

-- ∀ (b c : Prop) (x : Option Int) (y z : Int)
--   (f : ¬ c → Int → Int) (g : b → Option Int → Option Int), [Decidable b] → [Decidable c] →
--   (if h1 : c then (if h2 : b then (g h2 x) else none) else some (f h1 y)) = some z ===>
-- ∀ (b c : Prop) (x : Option Int) (y z : Int)
--   (f : ¬ c → Int → Int) (g : b → Option Int → Option Int),
--   some z = Solver.dite' c
--            (fun _ => Solver.dite' b (fun h2 : _ => g h2 x) (fun _ => none))
--            (fun h1 : _ => some (f h1 y))
-- NOTE: Test cases to ensure that non constant dite cannot be propagated
#testOptimize [ "DIteOverFunUnchanged_2" ]
  ∀ (b c : Prop) (x : Option Int) (y z : Int)
    (f : ¬ c → Int → Int) (g : b → Option Int → Option Int), [Decidable b] → [Decidable c] →
    (if h1 : c then (if h2 : b then (g h2 x) else none) else some (f h1 y)) = some z ===>
  ∀ (b c : Prop) (x : Option Int) (y z : Int)
    (f : ¬ c → Int → Int) (g : b → Option Int → Option Int),
    some z = Solver.dite' c
             (fun _ => Solver.dite' b (fun h2 : _ => g h2 x) (fun _ => none))
             (fun h1 : _ => some (f h1 y))

-- ∀ (b c : Prop) (x : Int) (y z : Option Int)
--   (f : c → Int → Int) (g : b → Option Int → Option Int), [Decidable b] → [Decidable c] →
--    (if h1 : c then some (f h1 x) else (if h2 : b then (g h2 y) else none)) = z ===>
-- ∀ (b c : Prop) (x : Int) (y z : Option Int)
--   (f : c → Int → Int) (g : b → Option Int → Option Int),
--    z = Solver.dite' c
--        (fun h1 : _ => some (f h1 x))
--        (fun _ => Solver.dite' b (fun h2 : _ => g h2 y) (fun _ => none))
-- NOTE: Test cases to ensure that non constant dite cannot be propagated
#testOptimize [ "DIteOverFunUnchanged_3" ]
  ∀ (b c : Prop) (x : Int) (y z : Option Int)
    (f : c → Int → Int) (g : b → Option Int → Option Int), [Decidable b] → [Decidable c] →
     (if h1 : c then some (f h1 x) else (if h2 : b then (g h2 y) else none)) = z ===>
  ∀ (b c : Prop) (x : Int) (y z : Option Int)
    (f : c → Int → Int) (g : b → Option Int → Option Int),
     z = Solver.dite' c
         (fun h1 : _ => some (f h1 x))
         (fun _ => Solver.dite' b (fun h2 : _ => g h2 y) (fun _ => none))

-- ∀ (b c d : Prop) (x y : Int) (z : Option Int)
--   (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
--   [Decidable b] → [Decidable c] → [Decidable d] →
--   let op1 :=
--     if h1 : c
--     then if h2 : d then some (g h2 x) else some (f h1 y)
--     else if h3 : b then some (t h3 x) else none;
--   op1 = z ===>
-- ∀ (b c d : Prop) (x y : Int) (z : Option Int)
--   (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
--    z = Solver.dite' c
--        (fun h1 : _ => Solver.dite' d (fun h2 : _ => some (g h2 x)) (fun _ => some (f h1 y)))
--        (fun _ => Solver.dite' b (fun h3 : _ => some (t h3 x)) (fun _ => none))
-- NOTE: Test cases to ensure that dite cannot be propagated when at
-- least one function's argument is not a constant.
#testOptimize [ "DIteOverFunUnchanged_4" ]
∀ (b c d : Prop) (x y : Int) (z : Option Int)
  (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
  [Decidable b] → [Decidable c] → [Decidable d] →
  let op1 :=
    if h1 : c
    then if h2 : d then some (g h2 x) else some (f h1 y)
    else if h3 : b then some (t h3 x) else none;
  op1 = z ===>
∀ (b c d : Prop) (x y : Int) (z : Option Int)
  (f : c → Int → Int) (g : d → Int → Int) (t : b → Int → Int),
   z = Solver.dite' c
       (fun h1 : _ => Solver.dite' d (fun h2 : _ => some (g h2 x)) (fun _ => some (f h1 y)))
       (fun _ => Solver.dite' b (fun h3 : _ => some (t h3 x)) (fun _ => none))

-- ∀ (c : Prop) (xs : List Int) (w x : Int) (f : c → Int → Int), [Decidable c] →
--   List.length (if h : c then [w, (f h x)] else xs) > 0 ===>
-- ∀ (c : Prop) (xs : List Int) (w x : Int) (f : c → Int → Int),
--   0 < List.length (Solver.dite' c (fun h : _ => [w, (f h x)]) (fun _ => xs))
#testOptimize [ "DIteOverFunUnchanged_5" ] (norm-result: 1)
  ∀ (c : Prop) (xs : List Int) (w x : Int) (f : c → Int → Int), [Decidable c] →
    List.length (if h : c then [w, (f h x)] else xs) > 0 ===>
  ∀ (c : Prop) (xs : List Int) (w x : Int) (f : c → Int → Int),
    0 < List.length (Solver.dite' c (fun h : _ => [w, (f h x)]) (fun _ => xs))

-- ∀ (c : Prop) (a b x : Bool) (f : c → Bool → Bool),
--   [Decidable c] → x = if h : c then f h a else b ===>
-- ∀ (c : Prop) (a b x : Bool) (f : c → Bool → Bool),
--   x = Solver.dite' c (fun h : _ => f h a) (fun _ => b)
#testOptimize [ "DIteOverFunUnchanged_6" ]
  ∀ (c : Prop) (a b x : Bool) (f : c → Bool → Bool),
    [Decidable c] → x = if h : c then f h a else b ===>
  ∀ (c : Prop) (a b x : Bool) (f : c → Bool → Bool),
    x = Solver.dite' c (fun h : _ => f h a) (fun _ => b)

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

def beqColor : Color → Color → Bool
| .red x, .red y
| .blue x, .blue y => beqColor x y
| .transparent, .transparent
| .black, .black => true
| _, _ => false

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) (.red x) ===>
-- ∀ (n : Option Nat) (x : Color),
--  toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
--  (fun (_ : Unit) => False)
--  (fun (_ : Unit) => False)
--  (fun (_ : Unit) => true = beqColor .transparent x)
--  (fun (_ : Unit) => False)
--  (fun (_ : Nat) => False)
#testOptimize [ "MatchOverFun_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) (.red x) ===>
  ∀ (n : Option Nat) (x : Color),
     toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
     (fun (_ : Unit) => False)
     (fun (_ : Unit) => False)
     (fun (_ : Unit) => true = beqColor .transparent x)
     (fun (_ : Unit) => False)
     (fun (_ : Nat) => False)

def toColorTwo (x : Option α) : Color :=
 match x with
 | none => .black
 | some _ => .blue .transparent

-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (.blue x) ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
--   toColorTwo.match_1 (fun (_ : Option α) => Prop) n
--   (fun (_ : Unit) => False)
--   (fun (_ : α) => true = beqColor Color.transparent x)
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverFun_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) (.blue x) ===>
  ∀ (α : Type) (n : Option α) (x : Color),
    toColorTwo.match_1 (fun (_ : Option α) => Prop) n
    (fun (_ : Unit) => False)
    (fun (_ : α) => true = beqColor Color.transparent x)


def toColorThree (x : Option Nat) : Color :=
 match x with
 | none => .black
 | some Nat.zero => .transparent
 | some 1 => .red .transparent
 | some 2 => .blue .black
 | some n => if n < 10 then .blue .transparent
             else if n < 100 then .red .black
             else .red .transparent

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorThree n) (.red x) ===>
-- ∀ (n : Option Nat) (x : Color),
--   toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
--    (fun (_ : Unit) => False)
--    (fun (_ : Unit) => False)
--    (fun (_ : Unit) => true = beqColor .transparent x)
--    (fun (_ : Unit) => False)
--    (fun (a : Nat) =>
--      ¬ a < 10 ∧
--      ((¬ a < 100 → true = beqColor .transparent x) ∧
--      (a < 100 → true = beqColor .black x)))
-- NOTE: Lean4 already applied structural equivalence between toColorFour.match_1 and toColorOne.match_1
-- NOTE: Test cases to ensure that simplification rule can transitively detect
-- that all path reduce to constant values
#testOptimize [ "MatchOverFun_3" ] (norm-result: 1)
  ∀ (n : Option Nat) (x : Color), beqColor (toColorThree n) (.red x) ===>
  ∀ (n : Option Nat) (x : Color),
    toColorOne.match_1 (fun (_ : Option Nat) => Prop) n
     (fun (_ : Unit) => False)
     (fun (_ : Unit) => False)
     (fun (_ : Unit) => true = beqColor .transparent x)
     (fun (_ : Unit) => False)
     (fun (a : Nat) =>
       ¬ a < 10 ∧
       ((¬ a < 100 → true = beqColor .transparent x) ∧
        (a < 100 → true = beqColor .black x)))

def beqColorDegree : Color → Color → (Nat → Bool)
| .red x, .red y
| .blue x, .blue y => λ n => if n == 0 then true else beqColor x y
| .transparent, .transparent
| .black, .black => λ _n => true
| _, _ => λ _n => false

-- ∀ (y : Nat) (x z : Color), beqColorDegree z (Color.blue x) y ===>
-- ∀ (y : Nat) (x z : Color),
--  beqColor.match_1 (fun (_ : Color) (_ : Color) => Prop) z (.blue x)
--   (fun (n : Color) (m : Color) => ¬ 0 = y → true = beqColor n m)
--   (fun (n : Color) (m : Color) => ¬ 0 = y → true = beqColor n m)
--   (fun (_ : Unit) => True)
--   (fun (_ : Unit) => True)
--   (fun (_ : Color) (_ : Color) => False)
-- NOTE: Test cases to ensure that match returning function are properly handled
#testOptimize [ "MatchOverFun_4" ] (norm-result: 1)
  ∀ (y : Nat) (x z : Color), beqColorDegree z (Color.blue x) y ===>
  ∀ (y : Nat) (x z : Color),
    beqColor.match_1 (fun (_ : Color) (_ : Color) => Prop) z (.blue x)
     (fun (n : Color) (m : Color) => ¬ 0 = y → true = beqColor n m)
     (fun (n : Color) (m : Color) => ¬ 0 = y → true = beqColor n m)
     (fun (_ : Unit) => True)
     (fun (_ : Unit) => True)
     (fun (_ : Color) (_ : Color) => False)


def colorToList (c : Color) (w x y z : α) : List α :=
 match c with
 | .red _ => [w, x]
 | .transparent => [y, z]
 | .blue _ => [w, x, y]
 | .black => [w, z, y]

-- ∀ (α : Type) (c : Color) (w x y z : α) (lt : α → α → Bool), [BEq α] →
--   List.lex (colorToList c w x y z) [w, y, z] lt ===>
-- ∀ (α : Type) (c : Color) (w x y z : α) (lt : α → α → Bool), [BEq α] →
--   colorToList.match_1 (fun (_ : Color) => Prop) c
--   (fun (_ : Color) => true = (lt w w || (lt x y || x == y) && w == w))
--   (fun (_ : Unit) => true = (lt y w || (lt z y || z == y) && y == w))
--   (fun (_ : Color) => true = (lt w w || (lt x y || lt y z && x == y) && w == w))
--   (fun (_ : Unit) => true = (lt w w || (lt z y || lt y z && z == y) && w == w))
-- NOTE: Test case to consider implicit parameters
#testOptimize [ "MatchOverFun_5" ]
  ∀ (α : Type) (c : Color) (w x y z : α) (lt : α → α → Bool), [BEq α] →
    List.lex (colorToList c w x y z) [w, y, z] lt ===>
  ∀ (α : Type) (c : Color) (w x y z : α) (lt : α → α → Bool), [BEq α] →
    colorToList.match_1 (fun (_ : Color) => Prop) c
    (fun (_ : Color) => true = (lt w w || (lt x y || x == y) && w == w))
    (fun (_ : Unit) => true = (lt y w || (lt z y || z == y) && y == w))
    (fun (_ : Color) => true = (lt w w || (lt x y || lt y z && x == y) && w == w))
    (fun (_ : Unit) => true = (lt w w || (lt z y || lt y z && z == y) && w == w))

/-! Test cases to validate when match over constructor constant propagation must NOT be applied. -/

-- ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
-- ∀ (n : Option Nat) (x : Color),
--    true = beqColor (toColorOne.match_1 (fun (_ : Option Nat) => Color) n
--                    (fun (_ : Unit) => .black)
--                    (fun (_ : Unit) => .transparent)
--                    (fun (_ : Unit) =>.red .transparent)
--                    (fun (_ : Unit) => .blue .black)
--                    (fun (_ : Nat) => .blue .transparent)) x
#testOptimize [ "MatchOverFunUnchanged_1" ]
  ∀ (n : Option Nat) (x : Color), beqColor (toColorOne n) x ===>
  ∀ (n : Option Nat) (x : Color),
      true = beqColor (toColorOne.match_1 (fun (_ : Option Nat) => Color) n
                       (fun (_ : Unit) => .black)
                       (fun (_ : Unit) => .transparent)
                       (fun (_ : Unit) =>.red .transparent)
                       (fun (_ : Unit) => .blue .black)
                       (fun (_ : Nat) => .blue .transparent)) x

-- ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
-- ∀ (α : Type) (n : Option α) (x : Color),
--   true = beqColor
--          ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
--            (fun (_ : Unit) => .black)
--            (fun (_ : α) => .blue .transparent) ) x
-- NOTE: Test case to ensure that generic type are also properly handled
#testOptimize [ "MatchOverFunUnchanged_2" ]
  ∀ (α : Type) (n : Option α) (x : Color), beqColor (toColorTwo n) x ===>
  ∀ (α : Type) (n : Option α) (x : Color),
    true = beqColor
           ( toColorTwo.match_1 (fun (_ : Option α) => Color) n
             (fun (_ : Unit) => .black)
             (fun (_ : α) => .blue .transparent) ) x

end Tests.ConstFunProp
