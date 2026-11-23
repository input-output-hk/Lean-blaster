import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeLE

/-! ## Test objectives to validate the normalization rule on `LE.le` (see `optimizeLE`):
      - e1 ≤ e2 ==> ¬ (e2 < e1)

    The rule is applied only when `isOpaqueRelational` is satisfied, i.e., the type of the operands
    is `Nat`, `Int`, `Bool` or `String`. A restart is triggered so that the resulting `LT.lt`
    expression is normalized in turn.
-/

/-! Test cases for normalization rule `e1 ≤ e2 ==> ¬ (e2 < e1)` (fully applied `LE.le`). -/

-- ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), ¬ (y < x)
#testOptimize [ "LENorm_1" ] ∀ (x y : Nat), x ≤ y ===> ∀ (x y : Nat), ¬ (y < x)

-- ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ (y < x)
#testOptimize [ "LENorm_2" ] ∀ (x y : Int), x ≤ y ===> ∀ (x y : Int), ¬ (y < x)

-- ∀ (x y : String), x ≤ y ===> ∀ (x y : String), ¬ (y < x)
#testOptimize [ "LENorm_3" ] ∀ (x y : String), x ≤ y ===> ∀ (x y : String), ¬ (y < x)

-- ∀ (x y : Bool), x ≤ y ===> ∀ (x y : Bool), ¬ (y < x)
#testOptimize [ "LENorm_4" ] ∀ (x y : Bool), x ≤ y ===> ∀ (x y : Bool), ¬ (y < x)

-- ∀ (x y : Nat), (x ≤ y) = ¬ (y < x) ===> True
-- Test case to validate expression caching after rewriting
#testOptimize [ "LENorm_5" ] ∀ (x y : Nat), (x ≤ y) = ¬ (y < x) ===> True

-- ∀ (x y : Int), (x < 1 + y) = (x ≤ y) ===> True
-- Both sides normalize to `¬ (y < x)` (see rule `a < 1 + b ==> ¬ (b < a)` on `LT.lt`)
#testOptimize [ "LENorm_6" ] ∀ (x y : Int), (x < 1 + y) = (x ≤ y) ===> True


/-! Test cases for normalization rule `LE.le ==> λ x y => ¬ (y < x)` (partially applied `LE.le`). -/

-- ∀ (r : Nat → Nat → Prop), r = LE.le ===> ∀ (r : Nat → Nat → Prop), r = fun x y => ¬ (y < x)
#testOptimize [ "LEPartial_1" ]
  ∀ (r : Nat → Nat → Prop), r = @LE.le Nat instLENat ===>
  ∀ (r : Nat → Nat → Prop), r = fun (x y : Nat) => ¬ (y < x)

-- ∀ (r : Int → Int → Prop), r = LE.le ===> ∀ (r : Int → Int → Prop), r = fun x y => ¬ (y < x)
#testOptimize [ "LEPartial_2" ]
  ∀ (r : Int → Int → Prop), r = @LE.le Int Int.instLEInt ===>
  ∀ (r : Int → Int → Prop), r = fun (x y : Int) => ¬ (y < x)


/-! Test cases to validate that the restart triggered by the rule leads to the normalization
    of the resulting `LT.lt` expression.
-/

-- ∀ (x : Nat), x ≤ x ===> True
-- `¬ (x < x)` is simplified to `¬ False`
#testOptimize [ "LERestart_1" ] ∀ (x : Nat), x ≤ x ===> True

-- ∀ (x : Nat), 0 ≤ x ===> True
-- `¬ (x < 0)` is simplified to `¬ False`
#testOptimize [ "LERestart_2" ] ∀ (x : Nat), 0 ≤ x ===> True

-- ∀ (x : Nat), x ≤ 0 ===> ∀ (x : Nat), 0 = x
-- `¬ (0 < x)` is normalized to `0 = x`
#testOptimize [ "LERestart_3" ] (norm-result: 1) ∀ (x : Nat), x ≤ 0 ===> ∀ (x : Nat), 0 = x

-- ∀ (x : Nat), x ≤ x + 1 ===> True
-- `¬ (1 + x < x)` is simplified to `¬ False`
#testOptimize [ "LERestart_4" ] ∀ (x : Nat), x ≤ x + 1 ===> True

-- ∀ (x : Int), x ≤ 1 + x ===> True
-- `¬ (1 + x < x)` is simplified to `¬ False`
#testOptimize [ "LERestart_5" ] ∀ (x : Int), x ≤ 1 + x ===> True

-- ∀ (x : Int), 1 + x ≤ x ===> False
-- `¬ (x < 1 + x)` is simplified to `¬ True`
#testOptimize [ "LERestart_6" ] ∀ (x : Int), 1 + x ≤ x ===> False

-- ∀ (s : String), s ≤ s ===> True
#testOptimize [ "LERestart_7" ] ∀ (s : String), s ≤ s ===> True

-- ∀ (b : Bool), b ≤ b ===> True
#testOptimize [ "LERestart_8" ] ∀ (b : Bool), b ≤ b ===> True

-- (3 : Nat) ≤ 5 ===> True
#testOptimize [ "LERestart_9" ] (3 : Nat) ≤ 5 ===> True

-- (-3 : Int) ≤ -5 ===> False
#testOptimize [ "LERestart_10" ] (-3 : Int) ≤ -5 ===> False


/-! Test cases to ensure that the normalization rule is not applied when the operand type
    is not an opaque relational type.
-/

-- ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y
-- LE remains unchanged
#testOptimize [ "LENoNorm_1" ] ∀ (α : Type) (x y : α), [LE α] → x ≤ y ===> ∀ (α : Type) (x y : α), [LE α] → x ≤ y

-- ∀ (α : Type) [LE α] (r : α → α → Prop), r = LE.le ===> ∀ (α : Type) [LE α] (r : α → α → Prop), r = LE.le
-- partially applied LE remains unchanged
#testOptimize [ "LENoNorm_2" ]
  ∀ (α : Type) [LE α] (r : α → α → Prop), r = @LE.le α _ ===>
  ∀ (α : Type) [LE α] (r : α → α → Prop), r = @LE.le α _

-- ∀ (x y : List Nat), x ≤ y ===> ∀ (x y : List Nat), ¬ List.Lex (λ a b => a < b) y x
-- `LE.le` on `List Nat` is not opaque: the instance is unfolded instead
#testOptimize [ "LENoNorm_3" ]
  ∀ (x y : List Nat), x ≤ y ===> ∀ (x y : List Nat), ¬ List.Lex (λ (a b : Nat) => a < b) y x

end Test.OptimizeLE
