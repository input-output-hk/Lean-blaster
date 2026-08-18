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

end Test.ReconstructLT
