import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListLength

/-! ## Test objectives to validate normalization and simplification rules on ``List.length
    (see `optimizeListLength`). -/

variable (α : Type) (a b c : α) (xs : List α) (x : Nat)

/-! Test cases for rule `List.length [] ===> 0`. -/

-- List.length [] ===> 0
#testOptimize [ "ListLengthNil_1" ] (norm-result: 1) List.length ([] : List α) ===> 0

-- List.length (List.take 2 []) ===> 0
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListLengthNil_2" ] (norm-result: 1) List.length (List.take 2 ([] : List α)) ===> 0


/-! Test cases for rule `List.length [e₁, e₂, ..., eₙ] ===> n`. -/

-- [a, b, c].length ===> 3
#testOptimize [ "ListLengthCst_1" ] (norm-result: 1) [a, b, c].length ===> 3

-- [a].length ===> 1
#testOptimize [ "ListLengthCst_2" ] (norm-result: 1) [a].length ===> 1

-- [x + 0].length ===> 1
#testOptimize [ "ListLengthCst_3" ] (norm-result: 1) [x + 0].length ===> 1

-- List.length (List.replicate 3 a) ===> 3
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListLengthCst_4" ] (norm-result: 1) List.length (List.replicate 3 a) ===> 3

-- List.length ([a] ++ [b, c]) ===> 3
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListLengthCst_5" ] (norm-result: 1) List.length ([a] ++ [b, c]) ===> 3


/-! Test cases for rule `List.length (e₁ :: e₂ :: ... :: eₙ :: x) ===> n + List.length x`. -/

-- (a :: b :: xs).length ===> 2 + List.length xs
#testOptimize [ "ListLengthCons_1" ] (norm-result: 1) (a :: b :: xs).length ===> Nat.add 2 (List.length xs)

-- (a :: xs).length ===> 1 + List.length xs
#testOptimize [ "ListLengthCons_2" ] (norm-result: 1) (a :: xs).length ===> Nat.add 1 (List.length xs)

-- List.length (a :: xs) = List.length xs + 1 ===> True
#testOptimize [ "ListLengthCons_3" ] List.length (a :: xs) = List.length xs + 1 ===> True


/-! Test cases to ensure that no rule is applied when the list is not a constructor. -/

-- xs.length ===> List.length xs
#testOptimize [ "ListLengthUnchanged_1" ] xs.length ===> List.length xs

-- List.length (xs ++ [a]) ===> List.length (List.append xs [a])
#testOptimize [ "ListLengthUnchanged_2" ] List.length (xs ++ [a]) ===> List.length (List.append xs [a])


/-! Test cases to validate that `List.length` as HOF is not reduced. -/

-- List.length ===> List.length
#testOptimize [ "ListLengthHOF_1" ] List.length (α := α) ===> List.length (α := α)

end Test.ListLength
