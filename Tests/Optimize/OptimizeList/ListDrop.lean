import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListDrop

/-! ## Test objectives to validate normalization and simplification rules on ``List.drop
    (see `optimizeListDrop`). -/

variable (α : Type) (a b c : α) (xs : List α) (n : Nat) (x y : Nat)

/-! Test cases for rule `List.drop i [] ===> []`. -/

-- List.drop n [] ===> []
#testOptimize [ "ListDropNil_1" ] List.drop n ([] : List α) ===> ([] : List α)

-- List.drop 2 [] ===> []
#testOptimize [ "ListDropNil_2" ] List.drop 2 ([] : List α) ===> ([] : List α)


/-! Test cases for rule `List.drop 0 x ===> x`. -/

-- List.drop 0 xs ===> xs
#testOptimize [ "ListDropZero_1" ] List.drop 0 xs ===> xs

-- List.drop (1 - 1) xs ===> xs
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListDropZero_2" ] List.drop (1 - 1) xs ===> xs

-- List.drop (n - n) xs ===> xs
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListDropZero_3" ] List.drop (n - n) xs ===> xs

-- List.drop 0 (xs ++ [a]) ===> List.append xs [a]
#testOptimize [ "ListDropZero_4" ] List.drop 0 (xs ++ [a]) ===> List.append xs [a]

-- List.drop 0 [a, b] ===> [a, b]
-- NOTE: reduced by rule `List.drop 0 x ===> x` before considering the list argument
#testOptimize [ "ListDropZero_5" ] List.drop 0 [a, b] ===> [a, b]

-- List.drop 0 (a :: xs) ===> a :: xs
-- NOTE: reduced by rule `List.drop 0 x ===> x` before considering the list argument
#testOptimize [ "ListDropZero_6" ] List.drop 0 (a :: xs) ===> a :: xs

-- List.drop 0 xs = xs ===> True
#testOptimize [ "ListDropZero_7" ] List.drop 0 xs = xs ===> True


/-! Test cases for rules (`cstListDrop?`):
     - List.drop n [e₁, e₂, ..., eₖ] ===> [eₙ₊₁, .. eₖ] (if n := N ∧ N ≤ k)
     - List.drop n [e₁, e₂, ..., eₖ] ===> [] (if n := N ∧ N > k)
-/

-- List.drop 1 [a, b, c] ===> [b, c]
#testOptimize [ "ListDropCst_1" ] List.drop 1 [a, b, c] ===> [b, c]

-- List.drop 2 [a, b, c] ===> [c]
#testOptimize [ "ListDropCst_2" ] List.drop 2 [a, b, c] ===> [c]

-- List.drop 3 [a, b, c] ===> []
#testOptimize [ "ListDropCst_3" ] List.drop 3 [a, b, c] ===> ([] : List α)

-- List.drop 10 [a, b, c] ===> []
#testOptimize [ "ListDropCst_4" ] List.drop 10 [a, b, c] ===> ([] : List α)

-- List.drop (1 + 1) [a, b, c] ===> [c]
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListDropCst_5" ] List.drop (1 + 1) [a, b, c] ===> [c]

-- List.drop 1 [x + 0, y] ===> [y]
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListDropCst_6" ] List.drop 1 [x + 0, y] ===> [y]

-- List.drop 1 (List.reverse [a, b, c]) ===> [b, a]
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListDropCst_7" ] List.drop 1 (List.reverse [a, b, c]) ===> [b, a]


/-! Test cases for rules (`cstListDrop?`):
     - List.drop n (e₁ :: e₂ :: ... :: eₖ :: x) ===> eₙ₊₁ :: ... :: eₖ :: x (if n := N ∧ N ≤ k)
     - List.drop n (e₁ :: e₂ :: ... :: eₖ :: x) ===> List.drop (n - k) x (if n := N ∧ N > k)
-/

-- List.drop 1 (a :: b :: xs) ===> b :: xs
#testOptimize [ "ListDropCons_1" ] List.drop 1 (a :: b :: xs) ===> b :: xs

-- List.drop 2 (a :: b :: xs) ===> xs
-- NOTE: the tail `List.drop 0 xs` is not generated when the index reaches 0 on the non constructor tail
#testOptimize [ "ListDropCons_2" ] List.drop 2 (a :: b :: xs) ===> xs

-- List.drop 1 (a :: xs) ===> xs
#testOptimize [ "ListDropCons_3" ] List.drop 1 (a :: xs) ===> xs

-- List.drop 3 (a :: b :: xs) ===> List.drop 1 xs
#testOptimize [ "ListDropCons_4" ] (norm-result: 1) List.drop 3 (a :: b :: xs) ===> List.drop 1 xs

-- List.drop 5 (a :: b :: xs) ===> List.drop 3 xs
#testOptimize [ "ListDropCons_5" ] (norm-result: 1) List.drop 5 (a :: b :: xs) ===> List.drop 3 xs

-- List.drop (1 + 1) (a :: b :: c :: xs) ===> c :: xs
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListDropCons_6" ] List.drop (1 + 1) (a :: b :: c :: xs) ===> c :: xs

-- List.drop 1 ((x + 0) :: xs) ===> xs
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListDropCons_7" ] ∀ (xs : List Nat), List.drop 1 ((x + 0) :: xs) = xs ===> True

-- List.drop 2 (a :: List.reverse [b, c]) ===> [b]
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListDropCons_8" ] List.drop 2 (a :: List.reverse [b, c]) ===> [b]


/-! Test cases to ensure that no rule is applied when the index is not a literal or the list is not a constructor. -/

-- List.drop n [a, b] ===> List.drop n [a, b]
#testOptimize [ "ListDropUnchanged_1" ] List.drop n [a, b] ===> List.drop n [a, b]

-- List.drop n (a :: xs) ===> List.drop n (a :: xs)
#testOptimize [ "ListDropUnchanged_2" ] List.drop n (a :: xs) ===> List.drop n (a :: xs)

-- List.drop n xs ===> List.drop n xs
#testOptimize [ "ListDropUnchanged_3" ] List.drop n xs ===> List.drop n xs

-- List.drop 2 xs ===> List.drop 2 xs
#testOptimize [ "ListDropUnchanged_4" ] (norm-result: 1) List.drop 2 xs ===> List.drop 2 xs

-- List.drop 2 (xs ++ [a]) ===> List.drop 2 (List.append xs [a])
#testOptimize [ "ListDropUnchanged_5" ] (norm-result: 1) List.drop 2 (xs ++ [a]) ===> List.drop 2 (List.append xs [a])


/-! Test cases to validate that `List.drop` as HOF is not reduced. -/

-- List.drop n ===> fun xs => List.drop n xs
#testOptimize [ "ListDropHOF_1" ] List.drop (α := α) n ===> fun (xs : List α) => List.drop n xs

-- List.drop 2 ===> fun xs => List.drop 2 xs
#testOptimize [ "ListDropHOF_2" ] (norm-result: 1) List.drop (α := α) 2 ===> fun (xs : List α) => List.drop 2 xs


/-! Test cases to ensure that other rules are applied once `List.drop` is reduced. -/

-- List.length (List.drop 1 (a :: b :: xs)) ===> 1 + List.length xs
#testOptimize [ "ListDropReduce_1" ] (norm-result: 1) List.length (List.drop 1 (a :: b :: xs)) ===>
  Nat.add 1 (List.length xs)

-- List.drop 1 [a, b, c] = [b, c] ===> True
#testOptimize [ "ListDropReduce_2" ] List.drop 1 [a, b, c] = [b, c] ===> True

-- List.drop 2 (a :: b :: xs) = xs ===> True
#testOptimize [ "ListDropReduce_3" ] List.drop 2 (a :: b :: xs) = xs ===> True

-- List.take 1 [a, b, c] ++ List.drop 1 [a, b, c] = [a, b, c] ===> True
#testOptimize [ "ListDropReduce_4" ] List.take 1 [a, b, c] ++ List.drop 1 [a, b, c] = [a, b, c] ===> True

-- List.drop 1 (List.drop 1 (a :: b :: xs)) ===> xs
#testOptimize [ "ListDropReduce_5" ] List.drop 1 (List.drop 1 (a :: b :: xs)) ===> xs

-- (List.drop 1 (a :: b :: xs))[0]? ===> some b
#testOptimize [ "ListDropReduce_6" ] (List.drop 1 (a :: b :: xs))[0]? ===> some b

end Test.ListDrop
