import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ListReplicate

/-! ## Test objectives to validate normalization and simplification rules on ``List.replicate
    (see `optimizeListReplicate`). -/

variable (α : Type) (a : α) (xs : List α) (n m i : Nat) (x : Nat)

/-! Test cases for rule `List.replicate N e ===> [e, ..., e]` (N copies). -/

-- List.replicate 0 a ===> []
#testOptimize [ "ListReplicateCst_1" ] List.replicate 0 a ===> ([] : List α)

-- List.replicate 1 a ===> [a]
#testOptimize [ "ListReplicateCst_2" ] List.replicate 1 a ===> [a]

-- List.replicate 3 a ===> [a, a, a]
#testOptimize [ "ListReplicateCst_3" ] List.replicate 3 a ===> [a, a, a]

-- List.replicate (1 + 2) a ===> [a, a, a]
-- NOTE: the number of copies is optimized to a literal before applying the rule
#testOptimize [ "ListReplicateCst_4" ] List.replicate (1 + 2) a ===> [a, a, a]

-- List.replicate 2 (x + 0) ===> [x, x]
-- NOTE: the element is optimized before applying the rule
#testOptimize [ "ListReplicateCst_5" ] List.replicate 2 (x + 0) ===> [x, x]

-- List.replicate 2 (List.replicate 1 a) ===> [[a], [a]]
-- NOTE: the element is optimized before applying the rule
#testOptimize [ "ListReplicateCst_6" ] List.replicate 2 (List.replicate 1 a) ===> [[a], [a]]


/-! Test cases for rule `List.replicate (N + e) a ===> a :: ... :: a :: List.replicate e a` (N copies),
    i.e., when the number of copies is a literal added to a non-literal expression. -/

-- List.replicate (n + 1) a ===> a :: List.replicate n a
#testOptimize [ "ListReplicateCons_1" ] List.replicate (n + 1) a ===> a :: List.replicate n a

-- List.replicate (1 + n) a ===> a :: List.replicate n a
-- NOTE: `Nat.add` is normalized with the literal as first operand before applying the rule
#testOptimize [ "ListReplicateCons_2" ] List.replicate (1 + n) a ===> a :: List.replicate n a

-- List.replicate (n + 3) a ===> a :: a :: a :: List.replicate n a
#testOptimize [ "ListReplicateCons_3" ] List.replicate (n + 3) a ===> a :: a :: a :: List.replicate n a

-- List.replicate (n + 1 + 1) a ===> a :: a :: List.replicate n a
-- NOTE: the number of copies is normalized to `Nat.add 2 n` before applying the rule
#testOptimize [ "ListReplicateCons_4" ] List.replicate (n + 1 + 1) a ===> a :: a :: List.replicate n a

-- List.replicate (n + m + 1) a ===> a :: List.replicate (n + m) a
#testOptimize [ "ListReplicateCons_5" ] (norm-result: 1) List.replicate (n + m + 1) a ===>
  a :: List.replicate (Nat.add n m) a

-- List.replicate (2 * n + 1) a ===> a :: List.replicate (2 * n) a
#testOptimize [ "ListReplicateCons_6" ] (norm-result: 1) List.replicate (2 * n + 1) a ===>
  a :: List.replicate (Nat.mul 2 n) a

-- List.replicate (n - 1 + 1) a ===> a :: List.replicate (n - 1) a
-- NOTE: `n - 1 + 1` is not simplified to `n` (not valid on natural numbers when `n = 0`)
#testOptimize [ "ListReplicateCons_7" ] (norm-result: 1) List.replicate (n - 1 + 1) a ===>
  a :: List.replicate (Nat.sub n 1) a

-- List.replicate (n + 1) (x + 0) ===> x :: List.replicate n x
-- NOTE: the element is optimized before applying the rule
#testOptimize [ "ListReplicateCons_8" ] List.replicate (n + 1) (x + 0) ===> x :: List.replicate n x

-- List.replicate (n + 1) (List.replicate 1 a) ===> [a] :: List.replicate n [a]
-- NOTE: the element is optimized before applying the rule
#testOptimize [ "ListReplicateCons_9" ] List.replicate (n + 1) (List.replicate 1 a) ===>
  [a] :: List.replicate n [a]

-- ∀ (n : Nat) (a : Nat), List.replicate (n + 1) a = a :: List.replicate n a ===> True
#testOptimize [ "ListReplicateCons_10" ]
  (∀ (n : Nat) (a : Nat), List.replicate (n + 1) a = a :: List.replicate n a) ===> True

-- ∀ (n : Nat) (a : Nat), List.replicate (n + 2) a = a :: List.replicate (n + 1) a ===> True
-- NOTE: both sides are reduced to `a :: a :: List.replicate n a`
#testOptimize [ "ListReplicateCons_11" ]
  (∀ (n : Nat) (a : Nat), List.replicate (n + 2) a = a :: List.replicate (n + 1) a) ===> True


/-! Test cases to ensure that no rule is applied when the number of copies is neither a literal
    nor a literal added to an expression. -/

-- List.replicate n a ===> List.replicate n a
#testOptimize [ "ListReplicateUnchanged_1" ] List.replicate n a ===> List.replicate n a

-- List.replicate (n + 0) a ===> List.replicate n a
-- NOTE: the number of copies is optimized to `n` before applying the rule
#testOptimize [ "ListReplicateUnchanged_2" ] List.replicate (n + 0) a ===> List.replicate n a

-- List.replicate (n + m) a ===> List.replicate (n + m) a
#testOptimize [ "ListReplicateUnchanged_3" ] List.replicate (n + m) a ===> List.replicate (Nat.add n m) a

-- List.replicate (2 * n) a ===> List.replicate (2 * n) a
#testOptimize [ "ListReplicateUnchanged_4" ] (norm-result: 1) List.replicate (2 * n) a ===>
  List.replicate (Nat.mul 2 n) a


/-! Test cases to validate that `List.replicate` as HOF is eta-expanded before applying the rule. -/

-- List.replicate 2 ===> fun a => [a, a]
#testOptimize [ "ListReplicateHOF_1" ] List.replicate (α := α) 2 ===> fun (a : α) => [a, a]

-- List.replicate n ===> fun a => List.replicate n a
#testOptimize [ "ListReplicateHOF_2" ] List.replicate (α := α) n ===> fun (a : α) => List.replicate n a

-- List.replicate (n + 1) ===> fun a => a :: List.replicate n a
#testOptimize [ "ListReplicateHOF_3" ] List.replicate (α := α) (n + 1) ===>
  fun (a : α) => a :: List.replicate n a


/-! Test cases to ensure that other rules are applied once `List.replicate` is reduced. -/

-- List.length (List.replicate 3 a) ===> 3
#testOptimize [ "ListReplicateReduce_1" ] (norm-result: 1) List.length (List.replicate 3 a) ===> 3

-- (List.replicate 2 a)[1]? ===> some a
#testOptimize [ "ListReplicateReduce_2" ] (List.replicate 2 a)[1]? ===> some a

-- List.reverse (List.replicate 2 a) ===> [a, a]
#testOptimize [ "ListReplicateReduce_3" ] List.reverse (List.replicate 2 a) ===> [a, a]

-- List.length (List.replicate (n + 2) a) ===> 2 + List.length (List.replicate n a)
#testOptimize [ "ListReplicateReduce_4" ] (norm-result: 1) List.length (List.replicate (n + 2) a) ===>
  Nat.add 2 (List.length (List.replicate n a))

-- (List.replicate (n + 2) a)[1]? ===> some a
#testOptimize [ "ListReplicateReduce_5" ] (List.replicate (n + 2) a)[1]? ===> some a

-- (List.replicate (n + 2) a)[3]? ===> List.get?Internal (List.replicate n a) 1
#testOptimize [ "ListReplicateReduce_6" ] (norm-result: 1) (List.replicate (n + 2) a)[3]? ===>
  List.get?Internal (List.replicate n a) 1

-- (List.replicate (n + 1) a)[i]? ===> sif 0 = i then some a else List.get?Internal (List.replicate n a) (i - 1)
#testOptimize [ "ListReplicateReduce_7" ] (norm-result: 1) (List.replicate (n + 1) a)[i]? ===>
  Blaster.dite' (0 = i) (fun _ => some a) (fun _ => List.get?Internal (List.replicate n a) (Nat.sub i 1))

-- List.take 1 (List.replicate (n + 2) a) ===> [a]
#testOptimize [ "ListReplicateReduce_8" ] List.take 1 (List.replicate (n + 2) a) ===> [a]

-- List.take 3 (List.replicate (n + 2) a) ===> a :: a :: List.take 1 (List.replicate n a)
#testOptimize [ "ListReplicateReduce_9" ] (norm-result: 1) List.take 3 (List.replicate (n + 2) a) ===>
  a :: a :: List.take 1 (List.replicate n a)

-- List.drop 2 (List.replicate (n + 2) a) ===> List.replicate n a
#testOptimize [ "ListReplicateReduce_10" ] List.drop 2 (List.replicate (n + 2) a) ===> List.replicate n a

-- List.drop 3 (List.replicate (n + 2) a) ===> List.drop 1 (List.replicate n a)
#testOptimize [ "ListReplicateReduce_11" ] (norm-result: 1) List.drop 3 (List.replicate (n + 2) a) ===>
  List.drop 1 (List.replicate n a)

-- List.reverse (List.replicate (n + 1) a) ===> List.reverseAux (List.replicate n a) [a]
#testOptimize [ "ListReplicateReduce_12" ] List.reverse (List.replicate (n + 1) a) ===>
  List.reverseAux (List.replicate n a) [a]

-- List.replicate (n + 1) a ++ xs ===> a :: List.append (List.replicate n a) xs
#testOptimize [ "ListReplicateReduce_13" ] List.replicate (n + 1) a ++ xs ===>
  a :: List.append (List.replicate n a) xs

end Test.ListReplicate
