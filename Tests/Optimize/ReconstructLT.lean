import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.ReconstructLT
/-! ## Proof reconstruction for the non-hypothesis `optimizeLT` reductions.
    Each case emits a proof step; the `proof` flag replays the stack and checks
    the reconstructed goal closes. -/

/-! Simplification rule `e < e ==> False`. -/

-- ∀ (a : Nat), a < a ===> False
#testOptimize [ "LtSelfNat", proof ] ∀ (a : Nat), a < a ===> False

-- ∀ (a : Int), a < a ===> False
#testOptimize [ "LtSelfInt", proof ] ∀ (a : Int), a < a ===> False

/-! Constant fold `N1 < N2 ==> N1 "<" N2`. -/

-- (2 < 5) = True ===> True
#testOptimize [ "LtCstNatTrue", proof ] (2 < 5) = True ===> True

-- (5 < 2) = False ===> True
#testOptimize [ "LtCstNatFalse", proof ] (5 < 2) = False ===> True

-- ((2 : Int) < 5) = True ===> True
#testOptimize [ "LtCstIntTrue", proof ] ((2 : Int) < 5) = True ===> True

-- ((5 : Int) < 2) = False ===> True
#testOptimize [ "LtCstIntFalse", proof ] ((5 : Int) < 2) = False ===> True

/-! Normalization rule `0 < -e ==> e < 0` (Int). -/

-- ∀ (a : Int), 0 < -a ===> ∀ (a : Int), a < 0
#testOptimize [ "ZeroLtNeg", proof ] (norm-result: 1) ∀ (a : Int), 0 < -a ===> ∀ (a : Int), a < 0

/-! Simplification rule `e < 1 ==> 0 = e` (Nat). -/

-- ∀ (a : Nat), a < 1 ===> ∀ (a : Nat), 0 = a
#testOptimize [ "LtOneNat", proof ] (norm-result: 1) ∀ (a : Nat), a < 1 ===> ∀ (a : Nat), 0 = a

/-! Simplification rule `N + e < e ==> False (N > 0) | True (N < 0)` (Int). -/

-- ∀ (a : Int), 3 + a < a ===> False
#testOptimize [ "AddPosLtSelf", proof ] ∀ (a : Int), 3 + a < a ===> False

-- ∀ (a : Int), (-3 + a < a) = True ===> True
#testOptimize [ "AddNegLtSelf", proof ] ∀ (a : Int), (-3 + a < a) = True ===> True

/-! Simplification rule `e < N + e ==> True (N > 0) | False (N < 0)` (Int). -/

-- ∀ (a : Int), (a < 3 + a) = True ===> True
#testOptimize [ "LtAddPosInt", proof ] ∀ (a : Int), (a < 3 + a) = True ===> True

-- ∀ (a : Int), a < -3 + a ===> False
#testOptimize [ "LtAddNegInt", proof ] ∀ (a : Int), a < -3 + a ===> False

/-! Simplification rule `a + b < a | b + a < a ==> False` (Nat). -/

-- ∀ (a b : Nat), a + b < a ===> False
#testOptimize [ "AddLtSelfLeft", proof ] ∀ (a b : Nat), a + b < a ===> False

-- ∀ (a b : Nat), b + a < a ===> False
#testOptimize [ "AddLtSelfRight", proof ] ∀ (a b : Nat), b + a < a ===> False

/-! Simplification rule `e < N + e ==> True (N > 0)` (Nat). -/

-- ∀ (a : Nat), (a < 3 + a) = True ===> True
#testOptimize [ "LtAddPosNat", proof ] ∀ (a : Nat), (a < 3 + a) = True ===> True

/-! Simplification rule `N1 + a < N2 ==> False (N2 ≤ N1) | a < N2 "-" N1` (Nat). -/

-- ∀ (a : Nat), 5 + a < 3 ===> False
#testOptimize [ "AddConstLtFalse", proof ] ∀ (a : Nat), 5 + a < 3 ===> False

-- ∀ (a : Nat), 3 + a < 5 ===> ∀ (a : Nat), a < 2
#testOptimize [ "AddConstLtSub", proof ] (norm-result: 1) ∀ (a : Nat), 3 + a < 5 ===> ∀ (a : Nat), a < 2

/-! Simplification rule `N1 < N2 + a ==> True (N1 < N2) | N1 "-" N2 < a` (Nat). -/

-- ∀ (a : Nat), (3 < 5 + a) = True ===> True
#testOptimize [ "ConstLtAddTrue", proof ] ∀ (a : Nat), (3 < 5 + a) = True ===> True

-- ∀ (a : Nat), 5 < 3 + a ===> ∀ (a : Nat), 2 < a
#testOptimize [ "ConstLtAddSub", proof ] (norm-result: 1) ∀ (a : Nat), 5 < 3 + a ===> ∀ (a : Nat), 2 < a

/-! Simplification rule `N1 + a < N2 ==> a < N2 "-" N1` (Int). -/

-- ∀ (a : Int), 3 + a < 5 ===> ∀ (a : Int), a < 2
#testOptimize [ "AddConstLtSubInt", proof ] (norm-result: 1) ∀ (a : Int), 3 + a < 5 ===> ∀ (a : Int), a < 2

/-! Simplification rule `N1 < N2 + a ==> N1 "-" N2 < a` (Int). -/

-- ∀ (a : Int), 5 < 3 + a ===> ∀ (a : Int), 2 < a
#testOptimize [ "ConstLtAddSubInt", proof ] (norm-result: 1) ∀ (a : Int), 5 < 3 + a ===> ∀ (a : Int), 2 < a

/-! Simplification rule
    `N1 + a < N2 + b ==> N1 "-" min(N1,N2) + a < N2 "-" min(N1,N2) + b`. -/

-- ∀ (a b : Nat), 3 + a < 5 + b ===> ∀ (a b : Nat), a < Nat.add 2 b
#testOptimize [ "AddBothNat", proof ] (norm-result: 1) ∀ (a b : Nat), 3 + a < 5 + b ===> ∀ (a b : Nat), a < Nat.add 2 b

-- ∀ (a b : Int), 3 + a < 5 + b ===> ∀ (a b : Int), a < Int.add 2 b
#testOptimize [ "AddBothInt", proof ] (norm-result: 1) ∀ (a b : Int), 3 + a < 5 + b ===> ∀ (a b : Int), a < Int.add 2 b

/-! Normalization rule `a < 1 + b ==> ¬ (b < a)`. -/

-- ∀ (a b : Nat), a < 1 + b ===> ∀ (a b : Nat), ¬ (b < a)
#testOptimize [ "LtOneAddNat", proof ] ∀ (a b : Nat), a < 1 + b ===> ∀ (a b : Nat), ¬ (b < a)

-- ∀ (a b : Int), a < 1 + b ===> ∀ (a b : Int), ¬ (b < a)
#testOptimize [ "LtOneAddInt", proof ] ∀ (a b : Int), a < 1 + b ===> ∀ (a b : Int), ¬ (b < a)

/-! ## Hypothesis-context reductions (Int).
    `a + b < a ==> False (if 0 ≤ b)` / `==> True (if b < 0)` (intRelLeftReduce?). -/

-- ∀ (a b : Int), 0 < b → ((a + b < a) = False) ===> True
#testOptimize [ "AddLtSelfNonNegInt", proof ] ∀ (a b : Int), 0 < b → ((a + b < a) = False) ===> True

-- ∀ (a b : Int), b < 0 → ((a + b < a) = True) ===> True
#testOptimize [ "AddLtSelfNegInt", proof ] ∀ (a b : Int), b < 0 → ((a + b < a) = True) ===> True

/-! `a < a + b ==> False (if b ≤ 0)` / `==> True (if 0 < b)` (Int, intRelRightReduce?). -/

-- ∀ (a b : Int), b < 0 → ((a < a + b) = False) ===> True
#testOptimize [ "LtAddSelfNonPosInt", proof ] ∀ (a b : Int), b < 0 → ((a < a + b) = False) ===> True

-- ∀ (a b : Int), 0 < b → ((a < a + b) = True) ===> True
#testOptimize [ "LtAddSelfPosInt", proof ] ∀ (a b : Int), 0 < b → ((a < a + b) = True) ===> True

/-! `a < a + b ==> False (if 0 = b)` / `==> True (if 0 < b)` (Nat, natRelRightReduce?). -/

-- ∀ (a b : Nat), 0 = b → ((a < a + b) = False) ===> True
#testOptimize [ "LtAddSelfZeroNat", proof ] ∀ (a b : Nat), 0 = b → ((a < a + b) = False) ===> True

-- ∀ (a b : Nat), 0 < b → ((a < a + b) = True) ===> True
#testOptimize [ "LtAddSelfPosNat", proof ] ∀ (a b : Nat), 0 < b → ((a < a + b) = True) ===> True

/-! `0 < x + y ==> True / False` from the signs of `x` and `y` (Int, intZeroLtSum?). -/

-- ∀ (x y : Int), 0 < x → 0 < y → ((0 < x + y) = True) ===> True
#testOptimize [ "ZeroLtSumPosInt", proof ] ∀ (x y : Int), 0 < x → 0 < y → ((0 < x + y) = True) ===> True

-- ∀ (x y : Int), x < 0 → y < 0 → ((0 < x + y) = False) ===> True
#testOptimize [ "ZeroLtSumNegInt", proof ] ∀ (x y : Int), x < 0 → y < 0 → ((0 < x + y) = False) ===> True

/-! `N < e ==> False (if ¬ (N - 1 < e))` (predCstLTInHyp). -/

-- ∀ (e : Nat), ¬ (4 < e) → ((5 < e) = False) ===> True
#testOptimize [ "PredCstLtNat", proof ] ∀ (e : Nat), ¬ (4 < e) → ((5 < e) = False) ===> True

-- ∀ (e : Int), ¬ (4 < e) → (((5 : Int) < e) = False) ===> True
#testOptimize [ "PredCstLtInt", proof ] ∀ (e : Int), ¬ ((4 : Int) < e) → (((5 : Int) < e) = False) ===> True

/-! `x + y < 0 ==> False / True` from the signs of `x` and `y` (Int, intZeroLtSum?). -/

-- ∀ (x y : Int), 0 < x → 0 < y → ((x + y < 0) = False) ===> True
#testOptimize [ "SumLtZeroPosInt", proof ] ∀ (x y : Int), 0 < x → 0 < y → ((x + y < 0) = False) ===> True

-- ∀ (x y : Int), x < 0 → y < 0 → ((x + y < 0) = True) ===> True
#testOptimize [ "SumLtZeroNegInt", proof ] ∀ (x y : Int), x < 0 → y < 0 → ((x + y < 0) = True) ===> True

end Test.ReconstructLT
