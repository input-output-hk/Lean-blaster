import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListReverse

/-! ## Test objectives to validate normalization and simplification rules on ``List.reverseAux
    (see `optimizeListReverseAux`).

    NOTE: `List.reverse as` is an alias to `List.reverseAux as []`. All expected results are therefore
    written in terms of ``List.reverseAux.
-/

variable (α : Type) (a b c : α) (xs ys : List α) (x y : Nat)

/-! Test cases for rule `List.reverseAux [] l ===> l`. -/

-- List.reverse [] ===> []
#testOptimize [ "ListReverseNil_1" ] List.reverse ([] : List α) ===> ([] : List α)

-- List.reverseAux [] ys ===> ys
#testOptimize [ "ListReverseNil_2" ] List.reverseAux ([] : List α) ys ===> ys

-- List.reverseAux [] [a, b] ===> [a, b]
#testOptimize [ "ListReverseNil_3" ] List.reverseAux ([] : List α) [a, b] ===> [a, b]


/-! Test cases for rule `List.reverseAux [e₀, e₁, ..., eₖ] l ==> eₖ :: ... :: e₁ :: e₀ :: l`. -/

-- List.reverse [a, b, c] ===> [c, b, a]
#testOptimize [ "ListReverseCst_1" ] List.reverse [a, b, c] ===> [c, b, a]

-- List.reverse [a] ===> [a]
#testOptimize [ "ListReverseCst_2" ] List.reverse [a] ===> [a]

-- List.reverseAux [a, b] [c] ===> [b, a, c]
#testOptimize [ "ListReverseCst_3" ] List.reverseAux [a, b] [c] ===> [b, a, c]

-- List.reverseAux [a, b] ys ===> b :: a :: ys
#testOptimize [ "ListReverseCst_4" ] List.reverseAux [a, b] ys ===> b :: a :: ys

-- List.reverse [x + 0, y] ===> [y, x]
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListReverseCst_5" ] List.reverse [x + 0, y] ===> [y, x]

-- List.reverse (List.reverse [a, b]) ===> [a, b]
#testOptimize [ "ListReverseCst_6" ] List.reverse (List.reverse [a, b]) ===> [a, b]

-- List.reverse ([a] ++ [b]) ===> [b, a]
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListReverseCst_7" ] List.reverse ([a] ++ [b]) ===> [b, a]


/-! Test cases for rule `List.reverseAux (e₀ :: e₁ :: ... :: eₖ :: x) l ==> List.reverseAux x (eₖ :: ... :: e₁ :: e₀ :: l)`. -/

-- List.reverse (a :: b :: xs) ===> List.reverseAux xs [b, a]
#testOptimize [ "ListReverseCons_1" ] List.reverse (a :: b :: xs) ===> List.reverseAux xs [b, a]

-- List.reverse (a :: xs) ===> List.reverseAux xs [a]
#testOptimize [ "ListReverseCons_2" ] List.reverse (a :: xs) ===> List.reverseAux xs [a]

-- List.reverseAux (a :: xs) ys ===> List.reverseAux xs (a :: ys)
#testOptimize [ "ListReverseCons_3" ] List.reverseAux (a :: xs) ys ===> List.reverseAux xs (a :: ys)

-- List.reverseAux (a :: b :: xs) [c] ===> List.reverseAux xs [b, a, c]
#testOptimize [ "ListReverseCons_4" ] List.reverseAux (a :: b :: xs) [c] ===> List.reverseAux xs [b, a, c]


/-! Test cases to ensure that no rule is applied when the first list argument is not a constructor. -/

-- List.reverse xs ===> List.reverseAux xs []
#testOptimize [ "ListReverseUnchanged_1" ] List.reverse xs ===> List.reverseAux xs []

-- List.reverseAux xs ys ===> List.reverseAux xs ys
#testOptimize [ "ListReverseUnchanged_2" ] List.reverseAux xs ys ===> List.reverseAux xs ys

-- List.reverseAux xs [a] ===> List.reverseAux xs [a]
#testOptimize [ "ListReverseUnchanged_3" ] List.reverseAux xs [a] ===> List.reverseAux xs [a]

-- List.reverse (List.reverse xs) ===> List.reverseAux (List.reverseAux xs []) []
-- NOTE: Can be reduced to `xs` with an additional simplification rule.
#testOptimize [ "ListReverseUnchanged_4" ] List.reverse (List.reverse xs) ===>
  List.reverseAux (List.reverseAux xs []) []


/-! Test cases to validate that `List.reverseAux`/`List.reverse` as HOF are not reduced. -/

-- List.reverseAux xs ===> fun ys => List.reverseAux xs ys
#testOptimize [ "ListReverseHOF_1" ] List.reverseAux xs ===> fun (ys : List α) => List.reverseAux xs ys

-- List.reverse ===> fun as => List.reverseAux as []
#testOptimize [ "ListReverseHOF_2" ] List.reverse (α := α) ===> fun (as : List α) => List.reverseAux as []

-- List.reverseAux [a, b] ===> fun ys => b :: a :: ys
#testOptimize [ "ListReverseHOF_3" ] List.reverseAux [a, b] ===> fun (ys : List α) => b :: a :: ys

end Test.ListReverse
