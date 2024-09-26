import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.BEqList
/-! ## Test objectives to validate normalization and simplification rules on ``BEq.beq instance on generic `List -/

/-! Test cases for `reduceApp` rule on ``BEq.beq. -/

-- List.nil : List α == List.nil ===> True
#testOptimize [ "BEqListCst_1" ] ∀ (α : Type), [BEq α] → (List.nil : List α) == List.nil ===> True

-- List.nil == [x, y, z] ===> False (with Type(x) = α)
#testOptimize [ "BEqListCst_2" ] ∀ (α : Type) (x y z : α), [BEq α] → List.nil == [x, y, z] ===>
                                 ∀ (α : Type) (_x _y _z : α), [BEq α] → False


/-! Test cases to ensure that the following simplification rules must not be applied on
    generic ``List instances that have not been reduced via `reduceApp` rule.`
     - `e1 == e2 ==> true (if e1 =ₚₜᵣ e2)`
     - `e1 == e2 ==> e2 == e1 (if e2 <ₒ e1)`
-/

-- [x] == [x] ===> true = List.beq [x] [x]
#testOptimize [ "BEqListUnchanged_1" ] ∀ (α : Type) (x : α), [BEq α] → [x] == [x] ===>
                                       ∀ (α : Type) (x : α), [BEq α] → true = (List.beq [x] [x])

-- [x] == [y] ===> true = List.beq [x] [y]
#testOptimize [ "BEqListUnchanged_2" ] ∀ (α : Type) (x y : α), [BEq α] → [x] == [y] ===>
                                       ∀ (α : Type) (x y : α), [BEq α] → true = (List.beq [x] [y])

-- [x, y] == [x, y, z] ===> true = List.beq [x, y] [x, y, z] (with Type(x) = α)
-- NOTE: Can result to false with unfolding of recursive function
#testOptimize [ "BEqListUnchanged_3" ] ∀ (α : Type) (x y z : α), [BEq α] → [x, y] == [x, y, z] ===>
                                       ∀ (α : Type) (x y z : α), [BEq α] → true = (List.beq [x, y] [x, y, z])

-- [x, y, z] == [x, y, z] ===> true = List.beq [x, y, z] [x, y, z] (with Type(x) = α)
#testOptimize [ "BEqListUnchanged_4" ] ∀ (α : Type) (x y z : α), [BEq α] → [x, y, z] == [x, y, z] ===>
                                       ∀ (α : Type) (x y z : α), [BEq α] → true = (List.beq [x, y, z] [x, y, z])


-- [y, z, x] == [x, y, z] ===> true = List.beq [y, z, x] [x, y, z] (with Type(x) = α)
#testOptimize [ "BEqListUnchanged_5" ] ∀ (α : Type) (x y z : α), [BEq α] → [y, z, x] == [x, y, z] ===>
                                       ∀ (α : Type) (x y z : α), [BEq α] → true = (List.beq [y, z, x] [x, y, z])


/-! Test cases to ensure that `reduceApp` is properly called
    when `BEq.beq` operands are reduced to constant values via optimization. -/

-- TODO: add test cases when normalization and simplification rules are introduced for List.

end Test.BEqList
