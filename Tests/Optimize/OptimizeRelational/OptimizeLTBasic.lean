import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLTBasic

/-! ## Test objectives to validate the basic simplification rules on `LT.lt` (see `optimizeLT`):
      - e1 < e2 ==> False (if e1 =ₚₜᵣ e2)
      - e < 0 ==> False (if Type(e) = Nat)
      - N1 < N2 ==> N1 "<" N2
      - e < 1 ==> 0 = e (if Type(e) = Nat)

    The rules are applied only when `isOpaqueRelational` is satisfied, i.e., the type of the operands
    is `Nat`, `Int`, `Bool` or `String`.
-/

/-! Test cases for simplification rule `e1 < e2 ==> False (if e1 =ₚₜᵣ e2)`. -/

-- ∀ (x : Nat), x < x ===> False
#testOptimize [ "LTSame_1" ] ∀ (x : Nat), x < x ===> False

-- ∀ (x : Int), x < x ===> False
#testOptimize [ "LTSame_2" ] ∀ (x : Int), x < x ===> False

-- ∀ (s : String), s < s ===> False
#testOptimize [ "LTSame_3" ] ∀ (s : String), s < s ===> False

-- ∀ (b : Bool), b < b ===> False
#testOptimize [ "LTSame_4" ] ∀ (b : Bool), b < b ===> False

-- ∀ (x y : Nat), x + y < y + x ===> False
-- both operands are normalized to the same expression
#testOptimize [ "LTSame_5" ] ∀ (x y : Nat), x + y < y + x ===> False

-- ∀ (x y : Int), x + y < y + x ===> False
#testOptimize [ "LTSame_6" ] ∀ (x y : Int), x + y < y + x ===> False

-- ∀ (x : Int), x < x + 0 ===> False
-- `x + 0` is simplified to `x` beforehand
#testOptimize [ "LTSame_7" ] ∀ (x : Int), x < x + 0 ===> False


/-! Test cases for simplification rule `e < 0 ==> False (if Type(e) = Nat)`. -/

-- ∀ (x : Nat), x < 0 ===> False
#testOptimize [ "LTNatZero_1" ] ∀ (x : Nat), x < 0 ===> False

-- ∀ (x y : Nat), x + y < 0 ===> False
#testOptimize [ "LTNatZero_2" ] ∀ (x y : Nat), x + y < 0 ===> False

-- ∀ (x y : Nat), x - y < 0 ===> False
#testOptimize [ "LTNatZero_3" ] ∀ (x y : Nat), x - y < 0 ===> False

-- ∀ (x : Nat), x * 5 < 0 ===> False
#testOptimize [ "LTNatZero_4" ] ∀ (x : Nat), x * 5 < 0 ===> False


/-! Test cases for simplification rule `N1 < N2 ==> N1 "<" N2`. -/

-- (3 : Nat) < 5 ===> True
#testOptimize [ "LTCst_1" ] (3 : Nat) < 5 ===> True

-- (7 : Nat) < 5 ===> False
#testOptimize [ "LTCst_2" ] (7 : Nat) < 5 ===> False

-- (5 : Nat) < 5 ===> False
#testOptimize [ "LTCst_3" ] (5 : Nat) < 5 ===> False

-- (-3 : Int) < 5 ===> True
#testOptimize [ "LTCst_4" ] (-3 : Int) < 5 ===> True

-- (-3 : Int) < -5 ===> False
#testOptimize [ "LTCst_5" ] (-3 : Int) < -5 ===> False

-- (5 : Int) < 5 ===> False
#testOptimize [ "LTCst_6" ] (5 : Int) < 5 ===> False

-- (0 : Int) < -5 ===> False
-- `-5` is folded to the literal `Int.negSucc 4` beforehand
#testOptimize [ "LTCst_7" ] (0 : Int) < -5 ===> False

-- "abc" < "abd" ===> True
#testOptimize [ "LTCst_8" ] "abc" < "abd" ===> True

-- "abd" < "abc" ===> False
#testOptimize [ "LTCst_9" ] "abd" < "abc" ===> False

-- "abc" < "abc" ===> False
#testOptimize [ "LTCst_10" ] "abc" < "abc" ===> False

-- (123 : Nat) + 2 < 100 + 30 ===> True
-- both operands are folded to literals beforehand
#testOptimize [ "LTCst_11" ] (123 : Nat) + 2 < 100 + 30 ===> True


/-! Test cases for simplification rule `e < 1 ==> 0 = e (if Type(e) = Nat)`. -/

-- ∀ (x : Nat), x < 1 ===> ∀ (x : Nat), 0 = x
#testOptimize [ "LTNatOne_1" ] (norm-result: 1) ∀ (x : Nat), x < 1 ===> ∀ (x : Nat), 0 = x

-- ∀ (x y : Nat), x - y < 1 ===> ∀ (x y : Nat), 0 = x - y
#testOptimize [ "LTNatOne_2" ] (norm-result: 1) ∀ (x y : Nat), x - y < 1 ===> ∀ (x y : Nat), 0 = Nat.sub x y

-- ∀ (x : Nat), x < 1 → 0 < x ===> ∀ (x : Nat), 0 < x
-- the hypothesis `0 = x` substitutes `x` in the conclusion, i.e., `0 < 0 ==> False` and `0 = x → False ==> 0 < x`
#testOptimize [ "LTNatOne_3" ] (norm-result: 1) ∀ (x : Nat), x < 1 → 0 < x ===> ∀ (x : Nat), 0 < x


/-! Test cases to ensure that the basic simplification rules are not wrongly applied. -/

-- ∀ (x y : Nat), x < y ===> ∀ (x y : Nat), x < y
#testOptimize [ "LTNoNorm_1" ] ∀ (x y : Nat), x < y ===> ∀ (x y : Nat), x < y

-- ∀ (x : Int), x < 0 ===> ∀ (x : Int), x < 0
-- rule `e < 0 ==> False` is only applicable on `Nat`
#testOptimize [ "LTNoNorm_2" ] (norm-result: 1) ∀ (x : Int), x < 0 ===> ∀ (x : Int), x < Int.ofNat 0

-- ∀ (x : Int), x < 1 ===> ∀ (x : Int), x < 1
-- rule `e < 1 ==> 0 = e` is only applicable on `Nat`
#testOptimize [ "LTNoNorm_3" ] (norm-result: 1) ∀ (x : Int), x < 1 ===> ∀ (x : Int), x < Int.ofNat 1

-- false < true ===> false < true
-- rule `N1 < N2 ==> N1 "<" N2` is not applicable on `Bool` literals
#testOptimize [ "LTNoNorm_4" ] false < true ===> false < true

-- ∀ (α : Type) (x : α), [LT α] → x < x ===> ∀ (α : Type) (x : α), [LT α] → x < x
-- `α` is not an opaque relational type
#testOptimize [ "LTNoNorm_5" ] ∀ (α : Type) (x : α), [LT α] → x < x ===> ∀ (α : Type) (x : α), [LT α] → x < x

-- ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y
#testOptimize [ "LTNoNorm_6" ] ∀ (α : Type) (x y : α), [LT α] → x < y ===> ∀ (α : Type) (x y : α), [LT α] → x < y

-- ∀ (x : List Nat), x < x ===> ∀ (x : List Nat), List.Lex (λ a b => a < b) x x
-- `LT.lt` on `List Nat` is not opaque: the instance is unfolded instead
#testOptimize [ "LTNoNorm_7" ]
  ∀ (x : List Nat), x < x ===> ∀ (x : List Nat), List.Lex (λ (a b : Nat) => a < b) x x

end Test.OptimizeLTBasic
