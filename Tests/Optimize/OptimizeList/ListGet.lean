import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListGet

/-! ## Test objectives to validate normalization and simplification rules on ``List.get?Internal
    (see `optimizeListGet`).

    NOTE: `xs[n]?` is a notation for `getElem? xs n`, which is an alias to `List.get?Internal xs n`
    once instances are resolved. All expected results are therefore written in terms of ``List.get?Internal.
-/

variable (α : Type) (a b c : α) (xs : List α) (i n : Nat) (x y : Nat)

/-! Test cases for rule `List.get?Internal [] i ===> none`. -/

-- ([] : List α)[n]? ===> none
#testOptimize [ "ListGetNil_1" ] ([] : List α)[n]? ===> (none : Option α)

-- ([] : List α)[2]? ===> none
#testOptimize [ "ListGetNil_2" ] ([] : List α)[2]? ===> (none : Option α)


/-! Test cases for rules (`isListNCtor?`):
     - List.get?Internal [e₀, e₁, ..., eₖ] n ===> some eₙ (if n := N ∧ N ≤ k)
     - List.get?Internal [e₀, e₁, ..., eₖ] n ===> none (if n := N ∧ N > k)
-/

-- [a, b, c][0]? ===> some a
#testOptimize [ "ListGetCst_1" ] [a, b, c][0]? ===> some a

-- [a, b, c][2]? ===> some c
#testOptimize [ "ListGetCst_2" ] [a, b, c][2]? ===> some c

-- [a, b, c][3]? ===> none
#testOptimize [ "ListGetCst_3" ] [a, b, c][3]? ===> (none : Option α)

-- [a, b, c][1 + 1]? ===> some c
-- NOTE: the index is optimized to a literal before applying the rule
#testOptimize [ "ListGetCst_4" ] [a, b, c][1 + 1]? ===> some c

-- [x + 0, y][1]? ===> some y
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListGetCst_5" ] [x + 0, y][1]? ===> some y

-- [a][0]? ===> some a
#testOptimize [ "ListGetCst_6" ] [a][0]? ===> some a


/-! Test cases for rules (`isListNCtor?`):
     - List.get?Internal (e₀ :: e₁ :: ... :: eₖ :: x) n ===> some eₙ (if n := N ∧ N ≤ k)
     - List.get?Internal (e₀ :: e₁ :: ... :: eₖ :: x) n ===> List.get?Internal x (N "-" k) (if n := N ∧ N > k)
-/

-- (a :: b :: xs)[0]? ===> some a
#testOptimize [ "ListGetCons_1" ] (a :: b :: xs)[0]? ===> some a

-- (a :: b :: xs)[1]? ===> some b
#testOptimize [ "ListGetCons_2" ] (a :: b :: xs)[1]? ===> some b

-- (a :: b :: xs)[2]? ===> List.get?Internal xs 0
#testOptimize [ "ListGetCons_3" ] (norm-result: 1) (a :: b :: xs)[2]? ===> List.get?Internal xs 0

-- (a :: b :: xs)[5]? ===> List.get?Internal xs 3
#testOptimize [ "ListGetCons_4" ] (norm-result: 1) (a :: b :: xs)[5]? ===> List.get?Internal xs 3

-- (a :: xs)[1 + 1]? ===> List.get?Internal xs 1
#testOptimize [ "ListGetCons_5" ] (norm-result: 1) (a :: xs)[1 + 1]? ===> List.get?Internal xs 1


/-! Test cases for rules (`isUnfoldListIdx?`), i.e., when the index is not a literal:
     - List.get?Internal [e₀, e₁, ..., eₙ] i ===>
          sif 0 = i then some e₀ else sif 1 = i then some e₁ ... else none
     - List.get?Internal (e₀ :: e₁ :: ... :: eₙ :: x) i ===>
          sif 0 = i then some e₀ else sif 1 = i then some e₁ ... else List.get?Internal x (i - (n + 1))

    NOTE: the index must be shifted by the number of unfolded elements when reaching a non-constructor tail,
    i.e., `(e₀ :: e₁ :: x)[i]? = sif 0 = i then some e₀ else sif 1 = i then some e₁ else x[i - 2]?`.
    Using `x[i]?` instead is unsound (counterexample: `(0 :: 0 :: [7])[2]? = some 7` whereas `[7][2]? = none`).
-/

-- [a][i]? ===> sif 0 = i then some a else none
#testOptimize [ "ListGetUnfold_1" ] (norm-result: 1) [a][i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a) (fun _ => (none : Option α))

-- [a, b][i]? ===> sif 0 = i then some a else sif 1 = i then some b else none
#testOptimize [ "ListGetUnfold_2" ] (norm-result: 1) [a, b][i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = i) (fun _ => some b) (fun _ => (none : Option α)))

-- [a, b, c][i]? ===> sif 0 = i then some a else sif 1 = i then some b else sif 2 = i then some c else none
#testOptimize [ "ListGetUnfold_3" ] (norm-result: 1) [a, b, c][i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = i) (fun _ => some b)
      (fun _ => Blaster.dite' (2 = i) (fun _ => some c) (fun _ => (none : Option α))))

-- (a :: xs)[i]? ===> sif 0 = i then some a else List.get?Internal xs (i - 1)
#testOptimize [ "ListGetUnfold_4" ] (norm-result: 1) (a :: xs)[i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a) (fun _ => List.get?Internal xs (Nat.sub i 1))

-- (a :: b :: xs)[i]? ===> sif 0 = i then some a else sif 1 = i then some b else List.get?Internal xs (i - 2)
#testOptimize [ "ListGetUnfold_5" ] (norm-result: 1) (a :: b :: xs)[i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = i) (fun _ => some b) (fun _ => List.get?Internal xs (Nat.sub i 2)))

-- [x + 0][i]? ===> sif 0 = i then some x else none
-- NOTE: the list elements are optimized before applying the rule
#testOptimize [ "ListGetUnfold_6" ] (norm-result: 1) [x + 0][i]? ===>
  Blaster.dite' (0 = i) (fun _ => some x) (fun _ => (none : Option Nat))

-- [a, b][n + 1]? ===> sif 0 = 1 + n then some a else sif 1 = 1 + n then some b else none
-- NOTE: the index is normalized (but not a literal) before applying the rule.
-- NOTE: no restart is set when the list ends with `[]`, hence the result is not re-optimized. It could be reduced to
-- `sif 0 = n then some b else none` (`0 = Nat.add 1 n ===> False` and `1 = Nat.add 1 n ===> 0 = n`) by setting the
-- restart flag as done when the tail is not a constructor.
#testOptimize [ "ListGetUnfold_7" ] (norm-result: 1) [a, b][n + 1]? ===>
  Blaster.dite' (0 = Nat.add 1 n) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = Nat.add 1 n) (fun _ => some b) (fun _ => (none : Option α)))

-- (a :: xs)[n + 1]? ===> List.get?Internal xs n
-- NOTE: the result is re-optimized (restart) when the tail is not a constructor: the shifted index
-- `Nat.sub (Nat.add 1 n) 1` reduces to `n` and the condition `0 = Nat.add 1 n` reduces to `False`.
#testOptimize [ "ListGetUnfold_8" ] (a :: xs)[n + 1]? ===> List.get?Internal xs n

-- (a :: b :: c :: xs)[i]? ===>
--   sif 0 = i then some a else sif 1 = i then some b else sif 2 = i then some c else List.get?Internal xs (i - 3)
#testOptimize [ "ListGetUnfold_9" ] (norm-result: 1) (a :: b :: c :: xs)[i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = i) (fun _ => some b)
      (fun _ => Blaster.dite' (2 = i) (fun _ => some c) (fun _ => List.get?Internal xs (Nat.sub i 3))))

-- (a :: b :: xs)[n + 2]? ===> List.get?Internal xs n
-- NOTE: the result is re-optimized (restart): both conditions `0 = Nat.add 2 n` and `1 = Nat.add 2 n` reduce
-- to `False` and the shifted index `Nat.sub (Nat.add 2 n) 2` reduces to `n`.
#testOptimize [ "ListGetUnfold_10" ] (a :: b :: xs)[n + 2]? ===> List.get?Internal xs n

-- (a :: b :: xs)[i]? = (if 0 = i then some a else if 1 = i then some b else xs[i - 2]?) ===> True
#testOptimize [ "ListGetUnfold_11" ]
  ((a :: b :: xs)[i]? = (if 0 = i then some a else if 1 = i then some b else xs[i - 2]?)) ===> True

-- ∀ (xs : List Nat) (i : Nat), (x :: xs)[i]? = (if 0 = i then some x else xs[i - 1]?) ===> True
#testOptimize [ "ListGetUnfold_12" ]
  (∀ (xs : List Nat) (i : Nat), (x :: xs)[i]? = (if 0 = i then some x else xs[i - 1]?)) ===> True

-- (a :: b :: xs)[n + 1]? ===> sif 0 = n then some b else List.get?Internal xs ((1 + n) - 2)
-- NOTE: the result is re-optimized (restart): `0 = Nat.add 1 n` reduces to `False` and `1 = Nat.add 1 n`
-- reduces to `0 = n`.
-- NOTE: Can be reduced to `sif 0 = n then some b else List.get?Internal xs (Nat.sub n 1)` with additional
-- simplification rules (`Nat.sub (Nat.add 1 n) 2 ===> Nat.sub n 1`).
#testOptimize [ "ListGetUnfold_13" ] (norm-result: 1) (a :: b :: xs)[n + 1]? ===>
  Blaster.dite' (0 = n) (fun _ => some b) (fun _ => List.get?Internal xs (Nat.sub (Nat.add 1 n) 2))

-- (a :: b :: c :: xs)[n + 2]? ===> sif 0 = n then some c else List.get?Internal xs ((2 + n) - 3)
-- NOTE: Can be reduced to `sif 0 = n then some c else List.get?Internal xs (Nat.sub n 1)` with additional
-- simplification rules (`Nat.sub (Nat.add 2 n) 3 ===> Nat.sub n 1`).
#testOptimize [ "ListGetUnfold_14" ] (norm-result: 1) (a :: b :: c :: xs)[n + 2]? ===>
  Blaster.dite' (0 = n) (fun _ => some c) (fun _ => List.get?Internal xs (Nat.sub (Nat.add 2 n) 3))

-- (a :: b :: xs)[n + 3]? ===> List.get?Internal xs (1 + n)
-- NOTE: the shifted index `Nat.sub (Nat.add 3 n) 2` reduces to `Nat.add 1 n`.
#testOptimize [ "ListGetUnfold_15" ] (norm-result: 1) (a :: b :: xs)[n + 3]? ===> List.get?Internal xs (Nat.add 1 n)

-- (a :: xs)[i - 1]? ===> sif 0 = i - 1 then some a else List.get?Internal xs (i - 2)
-- NOTE: the shifted index `Nat.sub (Nat.sub i 1) 1` reduces to `Nat.sub i 2`.
#testOptimize [ "ListGetUnfold_16" ] (norm-result: 1) (a :: xs)[i - 1]? ===>
  Blaster.dite' (0 = Nat.sub i 1) (fun _ => some a) (fun _ => List.get?Internal xs (Nat.sub i 2))

-- (a :: xs)[2 * n]? ===> sif 0 = 2 * n then some a else List.get?Internal xs (2 * n - 1)
-- NOTE: no further simplification is applicable on the shifted index `Nat.sub (Nat.mul 2 n) 1`.
#testOptimize [ "ListGetUnfold_17" ] (norm-result: 1) (a :: xs)[2 * n]? ===>
  Blaster.dite' (0 = Nat.mul 2 n) (fun _ => some a) (fun _ => List.get?Internal xs (Nat.sub (Nat.mul 2 n) 1))

-- (a :: (xs ++ [b]))[n + 1]? ===> List.get?Internal (List.append xs [b]) n
-- NOTE: the tail `xs ++ [b]` is not a constructor, hence the index is shifted and the result re-optimized.
#testOptimize [ "ListGetUnfold_18" ] (a :: (xs ++ [b]))[n + 1]? ===> List.get?Internal (List.append xs [b]) n

-- (a :: b :: xs)[n + 2]? = xs[n]? ===> True
#testOptimize [ "ListGetUnfold_19" ] ((a :: b :: xs)[n + 2]? = xs[n]?) ===> True

-- ∀ (xs : List Nat) (n : Nat), (x :: xs)[n + 1]? = xs[n]? ===> True
#testOptimize [ "ListGetUnfold_20" ] (∀ (xs : List Nat) (n : Nat), (x :: xs)[n + 1]? = xs[n]?) ===> True

-- ∀ (xs : List Nat) (n : Nat), (x :: xs)[n + 1]? = (if 0 = n + 1 then some x else xs[n]?) ===> True
-- NOTE: the rhs is also simplified to `List.get?Internal xs n` (`0 = Nat.add 1 n ===> False`).
#testOptimize [ "ListGetUnfold_21" ]
  (∀ (xs : List Nat) (n : Nat), (x :: xs)[n + 1]? = (if 0 = n + 1 then some x else xs[n]?)) ===> True


/-! Test cases to ensure that no rule is applied when the list is not a constructor. -/

-- xs[i]? ===> List.get?Internal xs i
#testOptimize [ "ListGetUnchanged_1" ] xs[i]? ===> List.get?Internal xs i

-- xs[2]? ===> List.get?Internal xs 2
#testOptimize [ "ListGetUnchanged_2" ] (norm-result: 1) xs[2]? ===> List.get?Internal xs 2

-- (xs ++ [a, b])[0]? ===> List.get?Internal (List.append xs [a, b]) 0
#testOptimize [ "ListGetUnchanged_3" ] (norm-result: 1) (xs ++ [a, b])[0]? ===>
  List.get?Internal (List.append xs [a, b]) 0

-- (xs ++ [a])[i]? ===> List.get?Internal (List.append xs [a]) i
#testOptimize [ "ListGetUnchanged_4" ] (xs ++ [a])[i]? ===> List.get?Internal (List.append xs [a]) i


/-! Test cases to validate that `List.get?Internal` as HOF is eta-expanded before applying the rules. -/

-- List.get?Internal [a] ===> fun i => sif 0 = i then some a else none
#testOptimize [ "ListGetHOF_1" ] (norm-result: 1) List.get?Internal (α := α) [a] ===>
  fun (i : Nat) => Blaster.dite' (0 = i) (fun _ => some a) (fun _ => (none : Option α))

-- List.get?Internal xs ===> fun i => List.get?Internal xs i
#testOptimize [ "ListGetHOF_2" ] List.get?Internal (α := α) xs ===> fun (i : Nat) => List.get?Internal xs i


-- List.get?Internal (a :: xs) ===> fun i => sif 0 = i then some a else List.get?Internal xs (i - 1)
-- NOTE: the partial application is eta-expanded and the rule applies with the shifted index on the tail.
#testOptimize [ "ListGetHOF_3" ] (norm-result: 1) List.get?Internal (α := α) (a :: xs) ===>
  fun (i : Nat) => Blaster.dite' (0 = i) (fun _ => some a) (fun _ => List.get?Internal xs (Nat.sub i 1))

-- List.get?Internal (a :: b :: xs) ===>
--   fun i => sif 0 = i then some a else sif 1 = i then some b else List.get?Internal xs (i - 2)
#testOptimize [ "ListGetHOF_4" ] (norm-result: 1) List.get?Internal (α := α) (a :: b :: xs) ===>
  fun (i : Nat) => Blaster.dite' (0 = i) (fun _ => some a)
    (fun _ => Blaster.dite' (1 = i) (fun _ => some b) (fun _ => List.get?Internal xs (Nat.sub i 2)))

/-! Test cases to ensure that the rules are applied once the list argument is reduced by other rules. -/

-- (List.reverse [a, b] ++ [c])[0]? ===> some b
#testOptimize [ "ListGetReduce_1" ] (List.reverse [a, b] ++ [c])[0]? ===> some b

-- (List.replicate 2 a)[1]? ===> some a
#testOptimize [ "ListGetReduce_2" ] (List.replicate 2 a)[1]? ===> some a

-- [a, b][1]? = some b ===> True
#testOptimize [ "ListGetReduce_3" ] [a, b][1]? = some b ===> True

end Test.ListGet
