import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListTake

/-! ## Test objectives to validate normalization and simplification rules on ``List.take
    (see `optimizeListTake`). -/

variable (α : Type) (a b c : α) (xs : List α) (n : Nat) (x y : Nat)

/-! Test cases for rule `List.take i [] ===> []`. -/

-- List.take n [] ===> []
#testOptimize [ "ListTakeNil_1" ] List.take n ([] : List α) ===> ([] : List α)

-- List.take 2 [] ===> []
#testOptimize [ "ListTakeNil_2" ] List.take 2 ([] : List α) ===> ([] : List α)


/-! Test cases for rule `List.take 0 x ===> []`. -/

-- List.take 0 xs ===> []
#testOptimize [ "ListTakeZero_1" ] List.take 0 xs ===> ([] : List α)

-- List.take (1 - 1) xs ===> []
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListTakeZero_2" ] List.take (1 - 1) xs ===> ([] : List α)

-- List.take (n - n) xs ===> []
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListTakeZero_3" ] List.take (n - n) xs ===> ([] : List α)

-- List.take 0 (xs ++ [a]) ===> []
#testOptimize [ "ListTakeZero_4" ] List.take 0 (xs ++ [a]) ===> ([] : List α)

-- ∀ (k : Nat), List.take 0 xs = List.take k [] ===> True
#testOptimize [ "ListTakeZero_5" ] ∀ (k : Nat), List.take 0 xs = List.take k ([] : List α) ===> True


/-! Test cases for rules (`cstListTake?`):
     - List.take n [e₁, e₂, ..., eₖ] ===> [e₁, e₂, ..., eₙ] (if n := N ∧ N ≤ k)
     - List.take n [e₁, e₂, ..., eₖ] ===> [e₁, e₁, ..., eₖ] (if n := N ∧ N > k)
-/

-- List.take 0 [a, b] ===> []
-- NOTE: reduced by rule `List.take 0 x ===> []` before considering the list argument
#testOptimize [ "ListTakeCst_1" ] List.take 0 [a, b] ===> ([] : List α)

-- List.take 2 [a, b, c] ===> [a, b]
#testOptimize [ "ListTakeCst_2" ] List.take 2 [a, b, c] ===> [a, b]

-- List.take 3 [a, b, c] ===> [a, b, c]
#testOptimize [ "ListTakeCst_3" ] List.take 3 [a, b, c] ===> [a, b, c]

-- List.take 5 [a, b, c] ===> [a, b, c]
#testOptimize [ "ListTakeCst_4" ] List.take 5 [a, b, c] ===> [a, b, c]

-- List.take (1 + 1) [a, b, c] ===> [a, b]
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListTakeCst_5" ] List.take (1 + 1) [a, b, c] ===> [a, b]

-- List.take 1 [x + 0, y] ===> [x]
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListTakeCst_6" ] List.take 1 [x + 0, y] ===> [x]

-- List.take 2 [x + 0, y] ===> [x, y]
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListTakeCst_7" ] List.take 2 [x + 0, y] ===> [x, y]


/-! Test cases for rules (`cstListTake?`):
     - List.take n (e₁ :: e₂ :: ... :: eₖ :: x) ===> [e₁, e₂, ..., eₙ] (if n := N ∧ N ≤ k)
     - List.take n (e₁ :: e₂ :: ... :: eₖ :: x) ===> e₁ :: e₂ :: ... :: eₖ :: (List.take "N - k" x) (if n := N ∧ N > k)
-/

-- List.take 0 (a :: xs) ===> []
-- NOTE: reduced by rule `List.take 0 x ===> []` before considering the list argument
#testOptimize [ "ListTakeCons_1" ] List.take 0 (a :: xs) ===> ([] : List α)

-- List.take 1 (a :: b :: xs) ===> [a]
#testOptimize [ "ListTakeCons_2" ] List.take 1 (a :: b :: xs) ===> [a]

-- List.take 2 (a :: b :: xs) ===> [a, b]
-- NOTE: the tail `List.take 0 xs` is not generated when the index reaches 0 on the non constructor tail
#testOptimize [ "ListTakeCons_3" ] List.take 2 (a :: b :: xs) ===> [a, b]

-- List.take 4 (a :: b :: xs) ===> a :: b :: List.take 2 xs
#testOptimize [ "ListTakeCons_4" ] (norm-result: 1) List.take 4 (a :: b :: xs) ===> a :: b :: List.take 2 xs

-- List.take 3 (a :: b :: xs) ===> a :: b :: List.take 1 xs
#testOptimize [ "ListTakeCons_5" ] (norm-result: 1) List.take 3 (a :: b :: xs) ===> a :: b :: List.take 1 xs


/-! Test cases to ensure that no rule is applied when the index is not a literal or the list is not a constructor. -/

-- List.take n [a, b] ===> List.take n [a, b]
#testOptimize [ "ListTakeUnchanged_1" ] List.take n [a, b] ===> List.take n [a, b]

-- List.take n (a :: xs) ===> List.take n (a :: xs)
#testOptimize [ "ListTakeUnchanged_2" ] List.take n (a :: xs) ===> List.take n (a :: xs)

-- List.take n xs ===> List.take n xs
#testOptimize [ "ListTakeUnchanged_3" ] List.take n xs ===> List.take n xs

-- List.take 2 xs ===> List.take 2 xs
#testOptimize [ "ListTakeUnchanged_4" ] (norm-result: 1) List.take 2 xs ===> List.take 2 xs

-- List.take 2 (xs ++ [a]) ===> List.take 2 (List.append xs [a])
#testOptimize [ "ListTakeUnchanged_5" ] (norm-result: 1) List.take 2 (xs ++ [a]) ===> List.take 2 (List.append xs [a])


/-! Test cases to validate that `List.take` as HOF is not reduced. -/

-- List.take n ===> fun xs => List.take n xs
#testOptimize [ "ListTakeHOF_1" ] List.take (α := α) n ===> fun (xs : List α) => List.take n xs

-- List.take 2 ===> fun xs => List.take 2 xs
#testOptimize [ "ListTakeHOF_2" ] (norm-result: 1) List.take (α := α) 2 ===> fun (xs : List α) => List.take 2 xs


/-! Test cases to ensure that the rules are applied once the arguments are reduced by other rules. -/

-- List.take 2 (List.reverse [a, b, c]) ===> [c, b]
#testOptimize [ "ListTakeReduce_1" ] List.take 2 (List.reverse [a, b, c]) ===> [c, b]

-- List.take 2 [a, b, c] = [a, b] ===> True
#testOptimize [ "ListTakeReduce_2" ] List.take 2 [a, b, c] = [a, b] ===> True

end Test.ListTake
