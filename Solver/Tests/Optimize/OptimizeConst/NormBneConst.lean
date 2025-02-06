import Lean
import Solver.Tests.Utils

open Lean Elab Command Term

namespace Test.NormBneConst

/-! ## Test objectives to validate normalization rules on `BEq.beq` const
       obtained after unfolding `bne definition.
-/

/-! Test cases for normalization rule:
      - app (const ``not l1) (app (const ``BEq.beq l2) e1 e2) ===> app (const ``not l1) (app (const ``BEq.beq us) e1 e2) (if n = ``bne)
-/

-- ∀ (a b : Bool), a != b ===> ∀ (a b : Bool), ¬ (a = b)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBne_1" ] ∀ (a b : Bool), a != b ===> ∀ (a b : Bool), ¬ (a = b)

-- ∀ (x y : Int), x != y ===> ∀ (x y : Int), ¬ (x = y)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBne_2" ] ∀ (x y : Int), x != y ===> ∀ (x y : Int), ¬ (x = y)

-- ∀ (x y : Nat), x != y ===> ∀ (x y : Nat), !(x == y) (i.e., false = (x == y))
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBne_3" ] ∀ (x y : Nat), x != y ===> ∀ (x y : Nat), ¬ (x = y)

-- ∀ (s t : String), s != t ===> ∀ (s t : String), ¬ (s = t)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBne_4" ] ∀ (s t : String), s != t ===> ∀ (s t : String), ¬ (s = t)

-- ∀ (α : Type) (x y : α), [BEq α] → x != y ===>
-- ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)
#testOptimize [ "ConstBne_5" ] ∀ (α : Type) (x y : α), [BEq α] → x != y ===>
                               ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)


-- ∀ (a b : Bool), (a != b) = !(a == b) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "ConstBne_6" ] ∀ (a b : Bool), (a != b) = !(a == b) ===> True

-- ∀ (x y : Int), (x != y) = !(x == y) ===> True
#testOptimize [ "ConstBne_7" ] ∀ (x y : Int), (x != y) = !(x == y) ===> True

-- ∀ (x y : Nat), (x != y) = !(x == y)
#testOptimize [ "ConstBne_8" ] ∀ (x y : Nat), (x != y) = !(x == y) ===> True

-- ∀ (s t : String), (s != t) = !(s == t) ===> True
#testOptimize [ "ConstBne_9" ] ∀ (s t : String), (s != t) = !(s == t) ===> True

-- ∀ (α : Type) (x y : α), [BEq α] → x != y = !(x == y) ===> True
#testOptimize [ "ConstBne_10" ] ∀ (α : Type) (x y : α), [BEq α] → (x != y) = !(x == y) ===> True


/-! Test cases to ensure that normalization is not wrongly applied on nominal `BEq.beq` expressions. -/

-- ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), a = b
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "ConstBeq_1" ] ∀ (a b : Bool), a == b ===> ∀ (a b : Bool), a = b

-- ∀ (a b : Bool), !(a == b) ===> ∀ (a b : Bool), ¬ (a = b)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBeq_2" ] ∀ (a b : Bool), !(a == b) ===> ∀ (a b : Bool), ¬ (a = b)

-- ∀ (x y : Int), x == y ===> ∀ (x y : Int), x = y
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "ConstBeq_3" ] ∀ (x y : Int), x == y ===> ∀ (x y : Int), x = y

-- ∀ (x y : Int), !(x == y) ===> ∀ (x y : Int), ¬ (x = y)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBeq_4" ] ∀ (x y : Int), !(x == y) ===> ∀ (x y : Int), ¬ (x = y)

-- ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), x = y
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "ConstBeq_5" ] ∀ (x y : Nat), x == y ===> ∀ (x y : Nat), x = y

-- ∀ (x y : Nat), !(x == y) ===> ∀ (x y : Nat), ¬ (x = y)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBeq_6" ] ∀ (x y : Nat), !(x == y) ===> ∀ (x y : Nat), ¬ (x = y)

-- ∀ (s t : String), s == t ===> ∀ (s t : String), (s = t)
-- NOTE: `true = (a == b)` is reduced to `a = b`
#testOptimize [ "ConstBeq_7" ] ∀ (s t : String), s == t ===> ∀ (s t : String), s = t

-- ∀ (s t : String), !(s == t) ===> ∀ (s t : String), ¬ (s = t)
-- NOTE: `false = (a == b)` is reduced to `¬ (a = b)`
#testOptimize [ "ConstBeq_8" ] ∀ (s t : String), !(s == t) ===> ∀ (s t : String), ¬ (s = t)

-- ∀ (α : Type) (x y : α), [BEq α] → x == y ===>
-- ∀ (α : Type) (x y : α), [BEq α] → true = (x == y)
#testOptimize [ "ConstBeq_9" ] ∀ (α : Type) (x y : α), [BEq α] → x == y ===>
                               ∀ (α : Type) (x y : α), [BEq α] → true = (x == y)

-- ∀ (α : Type) (x y : α), [BEq α] → !(x == y) ===>
-- ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)
#testOptimize [ "ConstBeq_10" ] ∀ (α : Type) (x y : α), [BEq α] → !(x == y) ===>
                                ∀ (α : Type) (x y : α), [BEq α] → false = (x == y)

end Test.NormBneConst
