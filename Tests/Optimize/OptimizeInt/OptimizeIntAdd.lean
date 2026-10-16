import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.OptimizeIntAdd

/-! ## Test objectives to validate normalization and simplification rules on ``Int.add -/

/-! Test cases for `reduceApp` rule on ``Int.add -/

-- 0 + 1 ===> 1
def intAddCst_1 : Expr := Lean.Expr.app
  (Lean.Expr.const `Int.ofNat [])
  (Lean.Expr.lit (Lean.Literal.natVal 1))

elab "intAddCst_1" : term => return intAddCst_1

#testOptimize [ "IntAddCst_1", proof] (0 : Int) + 1 ===> intAddCst_1

/-! Test cases for the constant fold `N1 + N2 ==> N1 "+" N2` -/

-- the fold feeds `Int.zero_add`, so its step must be in the stack
#testOptimize ["IntAddCst_2", proof] ∀ (n : Int), -2 + 2 + n = n ===> True

#testOptimize ["IntAddCst_3", proof] ∀ (n : Int), 1 + 1 + n = 2 + n ===> True

-- `2 - 2` unfolds to `2 + -2` first, then folds
#testOptimize ["IntAddCst_4", proof] ∀ (n : Int), 2 - 2 + n = n ===> True

/-! Test cases for the `Int.sub` unfolding `m - n ==> m + -n` -/

#testOptimize ["IntSubUnfold_1", proof] ∀ (x y : Int), x - y = x + -y ===> True

-- unfolding then `Int.add_right_neg` and `Int.zero_add`
#testOptimize ["IntSubUnfold_2", proof] ∀ (x n : Int), x - x + n = n ===> True

-- both sides carry the same `x - y`, one step rewrites both
#testOptimize ["IntSubUnfold_3", proof] ∀ (x y n : Int), x - y + n = n + (x - y) ===> True

/-! Test cases for simplification rule `0 + n ===> n` -/

#testOptimize ["IntAddZero_1", proof] ∀ (m n: Int), 0 + m = n ===> ∀ (m n: Int), m = n

#testOptimize ["IntAddZero_2", proof] ∀ (n : Int), 0 + n = n ===> True

/-! Test cases for simplification rule `N1 + (N2 + n) ==> (N1 "+" N2) + n` -/

#testOptimize ["IntAddAssoc_1", proof] ∀ (n : Int), 1 + (2 + n) = 3 + n ===> True

-- nested operand carries a core `Int.add`, exercising `toElabForm`'s Int branch
#testOptimize ["IntAddAssoc_2", proof] ∀ (a b : Int), 1 + (2 + (a + b)) = 3 + (a + b) ===> True

-- fold to `0` inside the associativity branch, then `Int.zero_add`
#testOptimize ["IntAddAssoc_3", proof] ∀ (n : Int), 2 + (-2 + n) = n ===> True

/-! Test cases for simplification rule `N1 + -(N2 + n) ==> (N1 "-" N2) + -n` -/

#testOptimize ["IntAddNegAdd_1", proof] ∀ (n : Int), 5 + -(2 + n) = 3 + -n ===> True

-- fold `1 - 1` inside the branch, then `Int.zero_add`
#testOptimize ["IntAddNegAdd_2", proof] ∀ (n : Int), 1 + -(1 + n) = -n ===> True

/-! Test cases for the commutative reorder `n1 + n2 ==> n2 + n1` -/

#testOptimize ["IntAddComm_1", proof] ∀ (n : Int), n + 3 = 3 + n ===> True

-- reorder `n + 0 ==> 0 + n`, closed with `Int.add_zero`
#testOptimize ["IntAddComm_2", proof] ∀ (n : Int), n + 0 = n ===> True


/-! Test cases for the simplification rule `n1 + (-n2) ==> 0 (if n1 =ₚₜᵣ n2)` -/

-- n + (-n) = 0 ==> True
#testOptimize ["IntAddNeg_1", proof] ∀ (n : Int), n + (-n) = 0 ===> True

/-! Test cases for the constant fold `Int.toNat N ==> "Int.toNat" N` under a composed goal. -/

#testOptimize ["IntToNatCst_1", proof]
  ∀ (x : Nat) (y : Int), ((Int.toNat 5 + x) = (x + 5)) ∧ y - y = 0 ===> True

/-! Test cases for simplification rule `Int.toNat (Int.ofNat e) ==> e` -/

-- ∀ (n : Nat), Int.toNat (Int.ofNat n) - n = 0 ===> True
#testOptimize ["IntToNatOfNat_1", proof] ∀ (n : Nat), Int.toNat (Int.ofNat n) - n = 0 ===> True

/-! Test cases for the simplification rule `Int.toNat (-(Int.ofNat e)) ==> 0` -/

-- ∀ (n : Nat), Int.toNat (-(Int.ofNat n)) = 0 ===> True
#testOptimize ["IntToNatNegOfNat_1", proof] ∀ (n : Nat), Int.toNat (-(Int.ofNat n)) = 0 ===> True

/-! Test cases for steps over `Int.ofNat`, written with a cast. -/

-- ∀ (n : Nat), Int.toNat (-(n : Int)) = 0 ===> True
#testOptimize ["IntToNatNegCast_1", proof] ∀ (n : Nat), Int.toNat (-(n : Int)) = 0 ===> True

-- ∀ (n : Nat), Int.toNat (n : Int) - n = 0 ===> True
#testOptimize ["IntToNatCast_1", proof] ∀ (n : Nat), Int.toNat (n : Int) - n = 0 ===> True

abbrev castA (n : Nat) : Int := (n : Int)

-- ∀ (n : Nat), castA n - (n : Int) = 0 ===> True
#testOptimize ["IntCastAbbrev_1", proof] ∀ (n : Nat), castA n - (n : Int) = 0 ===> True

-- ∀ (n : Nat), (fun (k : Nat) => (k : Int)) n - (n : Int) = 0 ===> True
#testOptimize ["IntCastBeta_1", proof]
  ∀ (n : Nat), (fun (k : Nat) => (k : Int)) n - (n : Int) = 0 ===> True

-- ∀ (n : Nat), Int.toNat (n : Int) + Nat.succ (Int.toNat (n : Int)) = Int.toNat (n : Int) + (1 + n) ===> True
#testOptimize ["IntCastSucc_1", proof]
  ∀ (n : Nat), Int.toNat (n : Int) + Nat.succ (Int.toNat (n : Int)) = Int.toNat (n : Int) + (1 + n) ===> True

-- ∀ (n : Nat), (n : Int) = (n : Int) ∧ Nat.succ (Int.toNat (n : Int)) = 1 + n ===> True
#testOptimize ["IntCastSucc_2", proof]
  ∀ (n : Nat), (n : Int) = (n : Int) ∧ Nat.succ (Int.toNat (n : Int)) = 1 + n ===> True

end Tests.OptimizeIntAdd
