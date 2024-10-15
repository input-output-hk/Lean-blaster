import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.BEqList
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance on generic `List -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- List.nil : List α == List.nil ===> True
#testOptimize [ "BEqListCst_1" ] ∀ (α : Type), [BEq α] → (List.nil : List α) == List.nil ===> True

-- List.nil == [x, y, z] ===> False (with Type(x) = α)
#testOptimize [ "BEqListCst_2" ] ∀ (α : Type) (x y z : α), [BEq α] → List.nil == [x, y, z] ===> False

-- [x, y] == [x, y, z] ===> False
-- NOTE: Reduce to False via `reduceApp` rule, which is also applicable on recursive functions
#testOptimize [ "BEqListCst_3" ] ∀ (α : Type) (x y z : α), [BEq α] → [x, y] == [x, y, z] ===> False


/-! Test cases to ensure that the following simplification rules must not be applied on
    generic ``List instances that have not been reduced via `reduceApp` rule.`
     - `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`
     - `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`
-/

-- [x] == [x] ===> x == x
-- NOTE: Reduction via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqListUnchanged_1" ] ∀ (α : Type) (x : α), [BEq α] → [x] == [x] ===>
                                       ∀ (α : Type) (x : α), [BEq α] → true = (x == x)

-- [x] == [y] ===> x == y
-- NOTE: Reduction via `reduceApp` rule, which is also applicable on recursive functions.
#testOptimize [ "BEqListUnchanged_2" ] ∀ (α : Type) (x y : α), [BEq α] → [x] == [y] ===>
                                       ∀ (α : Type) (x y : α), [BEq α] → true = (x == y)

-- ∀ (α : Type) (x y z : α), [BEq α] → [x, y, z] == [x, y, z] ===>
-- ∀ (α : Type) (x y z : α), [BEq α] → true = ((!(x == x) || ((!(y == y) || (z == z)) && (y == y))) && (x == x))
-- NOTE: Reduction via `reduceApp` rule, which is also applicable on recursive functions
-- NOTE: can be reduced to (x == x) && (y == y) && (z == z) with additional boolean simplification rules
#testOptimize [ "BEqListUnchanged_3" ] ∀ (α : Type) (x y z : α), [BEq α] → [x, y, z] == [x, y, z] ===>
                                       ∀ (α : Type) (x y z : α), [BEq α] →
                                         true = ((!(x == x) || ((!(y == y) || (z == z)) && (y == y))) && (x == x))


-- ∀ (α : Type) (x y z : α), [BEq α] → [y, z, x] == [x, y, z] ===>
-- ∀ (α : Type) (x y z : α), [BEq α] → true = ((!(y == x) || ((!(z == y) || (x == z)) && (z == y))) && (y == x))
-- NOTE: Reduction via `reduceApp` rule, which is also applicable on recursive functions
-- NOTE: can be reduced to (y == x) && (z == y) && (x == z) with additional boolean simplification rules
#testOptimize [ "BEqListUnchanged_4" ] ∀ (α : Type) (x y z : α), [BEq α] → [y, z, x] == [x, y, z] ===>
                                       ∀ (α : Type) (x y z : α), [BEq α] →
                                         true = ((!(y == x) || ((!(z == y) || (x == z)) && (z == y))) && (y == x))

-- ∀ (α : Type) (x : List α), [BEq α] → List.nil == x ===>
-- ∀ (α : Type) (x : List α), [BEq α] → true = (List.beq List.nil x)
#testOptimize [ "BEqListUnchanged_5" ] ∀ (α : Type) (x : List α), [BEq α] → List.nil == x ===>
                                       ∀ (α : Type) (x : List α), [BEq α] → true = (List.beq List.nil x)

-- ∀ (α : Type) (x : α) (xs ys : List α), [BEq α] → (x :: xs) == ys ===>
-- ∀ (α : Type) (x : α) (xs ys : List α), [BEq α] → true = (List.beq (x :: xs) ys)
#testOptimize [ "BEqListUnchanged_6" ] ∀ (α : Type) (x : α) (xs ys : List α), [BEq α] → (x :: xs) == ys ===>
                                       ∀ (α : Type) (x : α) (xs ys : List α), [BEq α] → true = (List.beq (x :: xs) ys)


/-! Test cases to ensure that `reduceApp` is properly called
    when `BEq.beq` operands are reduced to constant values via optimization. -/

variable (α : Type) [BEq α]
variable (x : α)
variable (y : α)
variable (z : α)

-- List.append [x] [y] == [x, y, z] ===> false
#testOptimize [ "BEqListReduce_1" ] List.append [x] [y] == [x, y, z] ===> false

-- List.append [x] [y] == [z, x, y] ===> false
#testOptimize [ "BEqListReduce_2" ] List.append [x] [y] == [z, x, y] ===> false

-- List.append [x] [y, z, x] == [y, z, x] ===> false
#testOptimize [ "BEqListReduce_3" ] List.append [x] [y, z, x] == [y, z, x] ===> false

-- List.drop 2 [y, z, x] == [y, z, x] ===> false
#testOptimize [ "BEqListReduce_4" ] List.drop 2 [y, z, x] == [y, z, x] ===> false

-- List.take 2 [y, z, x] == [y, z, x] ===> false
#testOptimize [ "BEqListReduce_5" ] List.take 2 [y, z, x] == [y, z, x] ===> false


-- TODO: add other test cases when normalization and simplification rules are introduced for List.

end Test.BEqList
