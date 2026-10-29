import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListAppend

/-! ## Test objectives to validate normalization and simplification rules on ``List.append
    (see `optimizeListAppend`).

    NOTE: `xs ++ ys` is a notation for `HAppend.hAppend xs ys`, which is an alias to `List.append xs ys`
    once instances are resolved. All expected results are therefore written in terms of ``List.append.
-/

variable (α : Type) (a b c d : α) (xs ys : List α) (x y : Nat)

/-! Test cases for rules `List.append [] x ===> x` and `List.append x [] ===> x`. -/

-- [] ++ xs ===> xs
#testOptimize [ "ListAppendNil_1" ] ([] : List α) ++ xs ===> xs

-- xs ++ [] ===> xs
#testOptimize [ "ListAppendNil_2" ] xs ++ ([] : List α) ===> xs

-- [] ++ [] ===> []
#testOptimize [ "ListAppendNil_3" ] ([] : List α) ++ ([] : List α) ===> ([] : List α)

-- [] ++ [a, b] ===> [a, b]
#testOptimize [ "ListAppendNil_4" ] ([] : List α) ++ [a, b] ===> [a, b]

-- [a, b] ++ [] ===> [a, b]
#testOptimize [ "ListAppendNil_5" ] [a, b] ++ ([] : List α) ===> [a, b]

-- (xs ++ []) ++ [a] ===> List.append xs [a]
-- NOTE: the inner append is reduced before considering the outer one
#testOptimize [ "ListAppendNil_6" ] (xs ++ ([] : List α)) ++ [a] ===> List.append xs [a]

-- List.take 0 xs ++ ys ===> ys
-- NOTE: the list arguments are optimized before applying the rule
#testOptimize [ "ListAppendNil_7" ] List.take 0 xs ++ ys ===> ys

-- xs ++ [] = xs ===> True
#testOptimize [ "ListAppendNil_8" ] xs ++ ([] : List α) = xs ===> True


/-! Test cases for rule `List.append [e₁, e₂, ..., eₙ] x ===> (e₁ :: ... :: eₙ :: x)` with a constructor list
    as second argument. -/

-- [a, b] ++ [c] ===> [a, b, c]
#testOptimize [ "ListAppendCst_1" ] [a, b] ++ [c] ===> [a, b, c]

-- List.append [a, b] [c, d] ===> [a, b, c, d]
#testOptimize [ "ListAppendCst_2" ] List.append [a, b] [c, d] ===> [a, b, c, d]

-- [a] ++ [b] ++ [c] ===> [a, b, c]
#testOptimize [ "ListAppendCst_3" ] [a] ++ [b] ++ [c] ===> [a, b, c]

-- [x + 0] ++ [y] ===> [x, y]
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListAppendCst_4" ] [x + 0] ++ [y] ===> [x, y]

-- List.reverse [a, b] ++ [c] ===> [b, a, c]
-- NOTE: the list arguments are optimized before applying the rule
#testOptimize [ "ListAppendCst_5" ] List.reverse [a, b] ++ [c] ===> [b, a, c]

-- [a] ++ List.replicate 2 b ===> [a, b, b]
-- NOTE: the list arguments are optimized before applying the rule
#testOptimize [ "ListAppendCst_6" ] [a] ++ List.replicate 2 b ===> [a, b, b]


/-! Test cases for rule `List.append [e₁, e₂, ..., eₙ] x ===> (e₁ :: ... :: eₙ :: x)` with a non constructor
    list as second argument. -/

-- [a] ++ xs ===> a :: xs
#testOptimize [ "ListAppendCons_1" ] [a] ++ xs ===> a :: xs

-- [a, b] ++ xs ===> a :: b :: xs
#testOptimize [ "ListAppendCons_2" ] [a, b] ++ xs ===> a :: b :: xs

-- [a] ++ [b] ++ xs ===> a :: b :: xs
-- NOTE: `++` is left associative, the inner append is reduced first
#testOptimize [ "ListAppendCons_3" ] [a] ++ [b] ++ xs ===> a :: b :: xs

-- [a] ++ ([b] ++ xs) ===> a :: b :: xs
#testOptimize [ "ListAppendCons_4" ] [a] ++ ([b] ++ xs) ===> a :: b :: xs

-- [x + 0] ++ xs ===> x :: xs
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListAppendCons_5" ] ∀ (xs : List Nat), [x + 0] ++ xs = x :: xs ===> True

-- [a] ++ (xs ++ [b]) ===> a :: List.append xs [b]
#testOptimize [ "ListAppendCons_6" ] [a] ++ (xs ++ [b]) ===> a :: List.append xs [b]


/-! Test cases for rule `List.append (e₁ :: e₂ :: ... :: eₙ :: l1) l2 ===> (e₁ :: ... :: eₙ :: List.append l1 l2)`. -/

-- (a :: xs) ++ [b] ===> a :: List.append xs [b]
#testOptimize [ "ListAppendConsTail_1" ] (a :: xs) ++ [b] ===> a :: List.append xs [b]

-- (a :: b :: xs) ++ ys ===> a :: b :: List.append xs ys
#testOptimize [ "ListAppendConsTail_2" ] (a :: b :: xs) ++ ys ===> a :: b :: List.append xs ys

-- (a :: xs) ++ [] ===> a :: xs
-- NOTE: reduced by rule `List.append x [] ===> x` before considering the first argument
#testOptimize [ "ListAppendConsTail_3" ] (a :: xs) ++ ([] : List α) ===> a :: xs

-- ([a] ++ xs) ++ [b] ===> a :: List.append xs [b]
-- NOTE: the inner append is reduced to `a :: xs` before applying the rule on the outer one
#testOptimize [ "ListAppendConsTail_4" ] ([a] ++ xs) ++ [b] ===> a :: List.append xs [b]

-- (a :: xs) ++ (b :: ys) ===> a :: List.append xs (b :: ys)
#testOptimize [ "ListAppendConsTail_5" ] (a :: xs) ++ (b :: ys) ===> a :: List.append xs (b :: ys)


/-! Test cases to ensure that no rule is applied when the first list argument is not a constructor. -/

-- xs ++ [a] ===> List.append xs [a]
#testOptimize [ "ListAppendUnchanged_1" ] xs ++ [a] ===> List.append xs [a]

-- xs ++ ys ===> List.append xs ys
#testOptimize [ "ListAppendUnchanged_2" ] xs ++ ys ===> List.append xs ys

-- (xs ++ [a]) ++ [b] ===> List.append (List.append xs [a]) [b]
-- NOTE: Can be reduced to `List.append xs [a, b]` with an additional simplification rule (associativity).
#testOptimize [ "ListAppendUnchanged_3" ] (xs ++ [a]) ++ [b] ===> List.append (List.append xs [a]) [b]

-- xs ++ (ys ++ [a]) ===> List.append xs (List.append ys [a])
#testOptimize [ "ListAppendUnchanged_4" ] xs ++ (ys ++ [a]) ===> List.append xs (List.append ys [a])

-- List.reverse xs ++ [a] ===> List.append (List.reverseAux xs []) [a]
#testOptimize [ "ListAppendUnchanged_5" ] List.reverse xs ++ [a] ===> List.append (List.reverseAux xs []) [a]


/-! Test cases to validate that `List.append` as HOF is eta-expanded before applying the rules. -/

-- List.append [a, b] ===> fun ys => a :: b :: ys
#testOptimize [ "ListAppendHOF_1" ] List.append [a, b] ===> fun (ys : List α) => a :: b :: ys

-- List.append xs ===> fun ys => List.append xs ys
#testOptimize [ "ListAppendHOF_2" ] List.append xs ===> fun (ys : List α) => List.append xs ys

-- List.append ([] : List α) ===> fun ys => ys
#testOptimize [ "ListAppendHOF_3" ] List.append ([] : List α) ===> fun (ys : List α) => ys


/-! Test cases to ensure that other rules are applied once `List.append` is reduced. -/

-- [a] ++ xs = a :: xs ===> True
#testOptimize [ "ListAppendReduce_1" ] [a] ++ xs = a :: xs ===> True

-- List.length ([a] ++ xs) ===> 1 + List.length xs
#testOptimize [ "ListAppendReduce_2" ] (norm-result: 1) List.length ([a] ++ xs) ===> Nat.add 1 (List.length xs)

-- ([a, b] ++ xs)[1]? ===> some b
#testOptimize [ "ListAppendReduce_3" ] ([a, b] ++ xs)[1]? ===> some b

-- ([a, b] ++ xs)[2]? ===> List.get?Internal xs 0
#testOptimize [ "ListAppendReduce_4" ] (norm-result: 1) ([a, b] ++ xs)[2]? ===> List.get?Internal xs 0

-- List.reverse ([a] ++ xs) ===> List.reverseAux xs [a]
#testOptimize [ "ListAppendReduce_5" ] List.reverse ([a] ++ xs) ===> List.reverseAux xs [a]

-- List.take 1 ([a] ++ xs) ===> [a]
#testOptimize [ "ListAppendReduce_6" ] List.take 1 ([a] ++ xs) ===> [a]

-- List.drop 1 ([a] ++ xs) ===> xs
#testOptimize [ "ListAppendReduce_7" ] List.drop 1 ([a] ++ xs) ===> xs

-- List.take 1 [a, b, c] ++ List.drop 1 [a, b, c] = [a, b, c] ===> True
#testOptimize [ "ListAppendReduce_8" ] List.take 1 [a, b, c] ++ List.drop 1 [a, b, c] = [a, b, c] ===> True

end Test.ListAppend
