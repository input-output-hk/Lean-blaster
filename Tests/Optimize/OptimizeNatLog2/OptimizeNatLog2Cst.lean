import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeNatLog2Cst

/-! ## Test objectives to validate the constant folding rule on `Nat.log2` (see `cstNatLog2?`
    in `optimizeNatLog2`):
      - Nat.log2 N ==> "Nat.log2 N"
-/

/-! Test cases for simplification rule `Nat.log2 N ==> "Nat.log2 N"`. -/

-- Nat.log2 8 ===> 3
def log2Cst_1 : Expr := Lean.Expr.lit (Lean.Literal.natVal 3)
elab "log2Cst_1" : term => return log2Cst_1

#testOptimize [ "Log2Cst_1" ] Nat.log2 8 ===> log2Cst_1

-- Nat.log2 0 ===> 0
def log2Cst_2 : Expr := Lean.Expr.lit (Lean.Literal.natVal 0)
elab "log2Cst_2" : term => return log2Cst_2

#testOptimize [ "Log2Cst_2" ] Nat.log2 0 ===> log2Cst_2

-- Nat.log2 1 ===> 0
#testOptimize [ "Log2Cst_3" ] Nat.log2 1 ===> log2Cst_2

-- Nat.log2 2 ===> 1
def log2Cst_4 : Expr := Lean.Expr.lit (Lean.Literal.natVal 1)
elab "log2Cst_4" : term => return log2Cst_4

#testOptimize [ "Log2Cst_4" ] Nat.log2 2 ===> log2Cst_4

-- Nat.log2 299 ===> 8
def log2Cst_5 : Expr := Lean.Expr.lit (Lean.Literal.natVal 8)
elab "log2Cst_5" : term => return log2Cst_5

#testOptimize [ "Log2Cst_5" ] Nat.log2 299 ===> log2Cst_5

-- Nat.log2 1023 ===> 9
def log2Cst_6 : Expr := Lean.Expr.lit (Lean.Literal.natVal 9)
elab "log2Cst_6" : term => return log2Cst_6

#testOptimize [ "Log2Cst_6" ] Nat.log2 1023 ===> log2Cst_6

-- ∀ (x : Nat), x = Nat.log2 1024 ===> ∀ (x : Nat), 10 = x
#testOptimize [ "Log2Cst_7" ] (norm-result: 1) ∀ (x : Nat), x = Nat.log2 1024 ===> ∀ (x : Nat), 10 = x

-- ∀ (x y : Nat), x + Nat.log2 16 < y ===> ∀ (x y : Nat), 4 + x < y
#testOptimize [ "Log2Cst_8" ] (norm-result: 1) ∀ (x y : Nat), x + Nat.log2 16 < y ===> ∀ (x y : Nat), Nat.add 4 x < y

-- ∀ (x : Nat), Nat.log2 8 < x ===> ∀ (x : Nat), 3 < x
#testOptimize [ "Log2Cst_9" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 8 < x ===> ∀ (x : Nat), 3 < x


/-! Test cases where the operand is folded to a literal beforehand (the constant folding rule
    then applies on the normalized operand). -/

-- ∀ (x : Nat), Nat.log2 (2 ^ 5) = x ===> ∀ (x : Nat), 5 = x
#testOptimize [ "Log2CstOperand_1" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 (2 ^ 5) = x ===> ∀ (x : Nat), 5 = x

-- ∀ (x : Nat), Nat.log2 (2 * 3) = x ===> ∀ (x : Nat), 2 = x
#testOptimize [ "Log2CstOperand_2" ] (norm-result: 1) ∀ (x : Nat), Nat.log2 (2 * 3) = x ===> ∀ (x : Nat), 2 = x

-- ∀ (x : Nat), x = 0 → Nat.log2 (2 * x) = 0 ===> True
-- `x` is substituted by `0` from the hypothesis, then `Nat.log2 0 ==> 0`
#testOptimize [ "Log2CstOperand_3" ] ∀ (x : Nat), x = 0 → Nat.log2 (2 * x) = 0 ===> True


/-! Test cases to ensure that the constant folding rule is not applied on non-literal operands. -/

-- ∀ (x y : Nat), Nat.log2 x = y ===> ∀ (x y : Nat), y = Nat.log2 x
#testOptimize [ "Log2CstNoNorm_1" ] ∀ (x y : Nat), Nat.log2 x = y ===> ∀ (x y : Nat), y = Nat.log2 x

-- ∀ (x y : Nat), Nat.log2 (x + 1) = y ===> ∀ (x y : Nat), y = Nat.log2 (1 + x)
#testOptimize [ "Log2CstNoNorm_2" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (x + 1) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.add 1 x)

-- ∀ (x y : Nat), Nat.log2 (Nat.log2 x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.log2 x)
#testOptimize [ "Log2CstNoNorm_3" ] ∀ (x y : Nat), Nat.log2 (Nat.log2 x) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.log2 x)

-- ∀ (x y : Nat), Nat.log2 (x / 2) = y ===> ∀ (x y : Nat), y = Nat.log2 (x / 2)
#testOptimize [ "Log2CstNoNorm_4" ] (norm-result: 1)
  ∀ (x y : Nat), Nat.log2 (x / 2) = y ===> ∀ (x y : Nat), y = Nat.log2 (Nat.div x 2)

end Test.OptimizeNatLog2Cst
