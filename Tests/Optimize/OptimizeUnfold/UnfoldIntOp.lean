import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldNatOp

/-! ## Test objectives to validate unfolding `Int` operators -/


/-! Test cases to validate unfolding of `Int` operators only when reduced to a constant value or via rewriting. -/

-- TODO: add test cases when simplification on Int operators are introduced


/-! Test cases to validate when `Int` operators must not be unfolded -/

-- ∀ (x y z : Int), x + y > z ===> ∀ (x y z : Int), z < Int.add x y
#testOptimize [ "IntOpNotUnfolded_1", proof ] ∀ (x y z : Int), x + y > z ===> ∀ (x y z : Int), z < Int.add x y

-- ∀ (x y z : Int), x - y < z ===> ∀ (x y : Int), Int.add x (Int.neg y) < z
#testOptimize [ "IntOpNotUnfolded_2", proof ] ∀ (x y z : Int), x - y < z ===> ∀ (x y z : Int), Int.add x (Int.neg y) < z

-- ∀ (x y z : Int), y + (x - z) < z ===> ∀ (x y z : Int), Int.add y (Int.add x (Int.neg z)) < z
#testOptimize [ "IntOpNotUnfolded_3", proof ] ∀ (x y z : Int), y + (x - z) < z ===>
                                     ∀ (x y z : Int), Int.add y (Int.add x (Int.neg z)) < z

-- ∀ (x y : Int), -x < y ===> ∀ (x y : Int), Int.neg x < y
#testOptimize [ "IntOpNotUnfolded_4", proof ] ∀ (x y : Int), -x < y ===> ∀ (x y : Int), Int.neg x < y

-- ∀ (x y z : Int), x * y > z ===> ∀ (x y z : Int), z < Int.mul x y
#testOptimize [ "IntOpNotUnfolded_5", proof ] ∀ (x y z : Int), x * y > z ===> ∀ (x y z : Int), z < Int.mul x y

-- ∀ (x y z : Int), x / y < z ===> ∀ (x y z : Int), Int.ediv x y < z
#testOptimize [ "IntOpNotUnfolded_6", proof ] ∀ (x y z : Int), x / y < z ===> ∀ (x y z : Int), Int.ediv x y < z

-- ∀ (x y z : Int), x % y < z ===> ∀ (x y z : Int), Int.emod x y < z
#testOptimize [ "IntOpNotUnfolded_7", proof ] ∀ (x y z : Int), x % y < z ===> ∀ (x y z : Int), Int.emod x y < z

-- ∀ (x y z : Int), Int.tdiv x y < z ===> ∀ (x y z : Int), Int.tdiv x y < z
#testOptimize [ "IntOpNotUnfolded_8", proof ] ∀ (x y z : Int), Int.tdiv x y < z ===> ∀ (x y z : Int), Int.tdiv x y < z

-- ∀ (x y z : Int), Int.tmod x y < z ===> ∀ (x y z : Int), Int.tmod x y < z
#testOptimize [ "IntOpNotUnfolded_9", proof ] ∀ (x y z : Int), Int.tmod x y < z ===> ∀ (x y z : Int), Int.tmod x y < z

-- ∀ (x y z : Int), Int.fdiv x y < z ===> ∀ (x y z : Int), Int.fdiv x y < z
#testOptimize [ "IntOpNotUnfolded_10", proof ] ∀ (x y z : Int), Int.fdiv x y < z ===> ∀ (x y z : Int), Int.fdiv x y < z

-- ∀ (x y z : Int), Int.fmod x y < z ===> ∀ (x y z : Int), Int.fmod x y < z
#testOptimize [ "IntOpNotUnfolded_11", proof ] ∀ (x y z : Int), Int.fmod x y < z ===> ∀ (x y z : Int), Int.fmod x y < z

-- ∀ (x y : Int) (n : Nat), x ^ n > y ===> ∀ (x y : Int) (n : Nat), y < Int.pow x n
#testOptimize [ "IntOpNotUnfolded_12", proof ] ∀ (x y : Int) (n : Nat), x ^ n > y ===> ∀ (x y : Int) (n : Nat), y < Int.pow x n

-- ∀ (x : Int) (n : Nat), Int.toNat x = n ===> ∀ (x : Int) (n : Nat), n = Int.toNat x
#testOptimize [ "IntOpNotUnfolded_13", proof ] ∀ (x : Int) (n : Nat), Int.toNat x = n ===> ∀ (x : Int) (n : Nat), n = Int.toNat x


end Tests.UnfoldNatOp
