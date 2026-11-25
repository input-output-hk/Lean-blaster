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



/-! Test cases for rule `List.reverseAux (List.reverseAux l []) [] ===> l` (`idListReverse?`). -/

-- List.reverse (List.reverse xs) ===> xs
#testOptimize [ "ListReverseInv_1" ] List.reverse (List.reverse xs) ===> xs

-- List.reverseAux (List.reverseAux xs []) [] ===> xs
#testOptimize [ "ListReverseInv_2" ] List.reverseAux (List.reverseAux xs []) [] ===> xs

-- List.reverse (List.reverse (List.reverse xs)) ===> List.reverseAux xs []
-- NOTE: the inner pair is reduced first, the remaining reversal is kept
#testOptimize [ "ListReverseInv_3" ] List.reverse (List.reverse (List.reverse xs)) ===> List.reverseAux xs []

-- List.reverse (List.reverse (List.reverse (List.reverse xs))) ===> xs
#testOptimize [ "ListReverseInv_4" ] List.reverse (List.reverse (List.reverse (List.reverse xs))) ===> xs

-- List.reverse (List.reverse (xs ++ [])) ===> xs
-- NOTE: the list argument is optimized before applying the rule
#testOptimize [ "ListReverseInv_5" ] List.reverse (List.reverse (xs ++ [])) ===> xs

-- (List.reverse (List.reverse xs)) ++ ys ===> List.append xs ys
#testOptimize [ "ListReverseInv_6" ] List.reverse (List.reverse xs) ++ ys ===> List.append xs ys

-- ∀ xs, List.reverse (List.reverse xs) = xs ===> True
#testOptimize [ "ListReverseInv_7" ] ∀ (xs : List α), List.reverse (List.reverse xs) = xs ===> True

-- ∀ xs ys, List.reverse (List.reverse xs) = ys ===> ∀ xs ys, xs = ys
#testOptimize [ "ListReverseInv_8" ] ∀ (xs ys : List α), List.reverse (List.reverse xs) = ys ===>
  ∀ (xs ys : List α), xs = ys

-- List.reverse (List.reverse (a :: b :: xs)) ===> List.reverseAux (List.reverseAux xs [b, a]) []
-- NOTE: the inner reversal is normalized first (`List.reverseAux xs [b, a]`): its accumulator is no
-- longer `[]`, the rule does not apply (the constant prefix is reversed by the `cstListReverse?` rule
-- on the outer application only once `xs` is a constructor)
#testOptimize [ "ListReverseInv_9" ] List.reverse (List.reverse (a :: b :: xs)) ===>
  List.reverseAux (List.reverseAux xs [b, a]) []


/-! Test cases to ensure that rule `List.reverseAux (List.reverseAux l []) [] ===> l` is not applied
    when one of the accumulators is not `[]` or when the inner list is not a `List.reverseAux`. -/

-- List.reverseAux (List.reverseAux xs []) ys ===> List.reverseAux (List.reverseAux xs []) ys
#testOptimize [ "ListReverseInvUnchanged_1" ] List.reverseAux (List.reverseAux xs []) ys ===>
  List.reverseAux (List.reverseAux xs []) ys

-- List.reverseAux (List.reverseAux xs []) [a] ===> List.reverseAux (List.reverseAux xs []) [a]
#testOptimize [ "ListReverseInvUnchanged_2" ] List.reverseAux (List.reverseAux xs []) [a] ===>
  List.reverseAux (List.reverseAux xs []) [a]

-- List.reverseAux (List.reverseAux xs ys) [] ===> List.reverseAux (List.reverseAux xs ys) []
#testOptimize [ "ListReverseInvUnchanged_3" ] List.reverseAux (List.reverseAux xs ys) [] ===>
  List.reverseAux (List.reverseAux xs ys) []

-- List.reverseAux (List.reverseAux xs [a]) [] ===> List.reverseAux (List.reverseAux xs [a]) []
#testOptimize [ "ListReverseInvUnchanged_4" ] List.reverseAux (List.reverseAux xs [a]) [] ===>
  List.reverseAux (List.reverseAux xs [a]) []

-- List.reverseAux (List.reverseAux xs ys) zs ===> List.reverseAux (List.reverseAux xs ys) zs
#testOptimize [ "ListReverseInvUnchanged_5" ] ∀ (zs : List α), List.reverseAux (List.reverseAux xs ys) zs = zs ===>
  ∀ (zs : List α), zs = List.reverseAux (List.reverseAux xs ys) zs

-- List.reverse (xs ++ ys) ===> List.reverseAux (List.append xs ys) []
-- NOTE: the inner list is not a `List.reverseAux` application
#testOptimize [ "ListReverseInvUnchanged_6" ] List.reverse (xs ++ ys) ===> List.reverseAux (List.append xs ys) []

-- List.reverse (List.reverse xs ++ ys) ===> List.reverseAux (List.append (List.reverseAux xs []) ys) []
-- NOTE: the inner `List.reverseAux` is below an append, the rule does not apply
#testOptimize [ "ListReverseInvUnchanged_7" ] List.reverse (List.reverse xs ++ ys) ===>
  List.reverseAux (List.append (List.reverseAux xs []) ys) []

-- List.reverseAux (List.reverseAux xs []) ===> fun ys => List.reverseAux (List.reverseAux xs []) ys
-- NOTE: as HOF the outer accumulator is a bound variable, the rule does not apply
#testOptimize [ "ListReverseInvUnchanged_8" ] List.reverseAux (List.reverseAux xs []) ===>
  fun (ys : List α) => List.reverseAux (List.reverseAux xs []) ys

-- ∀ xs ys, List.reverse (List.reverse xs) = List.reverse ys ===> ∀ xs ys, xs = List.reverseAux ys []
-- NOTE: only the double reversal is reduced
#testOptimize [ "ListReverseInvUnchanged_9" ] ∀ (xs ys : List α), List.reverse (List.reverse xs) = List.reverse ys ===>
  ∀ (xs ys : List α), xs = List.reverseAux ys []


/-! Test cases to validate that `List.reverseAux`/`List.reverse` as HOF are not reduced. -/

-- List.reverseAux xs ===> fun ys => List.reverseAux xs ys
#testOptimize [ "ListReverseHOF_1" ] List.reverseAux xs ===> fun (ys : List α) => List.reverseAux xs ys

-- List.reverse ===> fun as => List.reverseAux as []
#testOptimize [ "ListReverseHOF_2" ] List.reverse (α := α) ===> fun (as : List α) => List.reverseAux as []

-- List.reverseAux [a, b] ===> fun ys => b :: a :: ys
#testOptimize [ "ListReverseHOF_3" ] List.reverseAux [a, b] ===> fun (ys : List α) => b :: a :: ys

end Test.ListReverse
