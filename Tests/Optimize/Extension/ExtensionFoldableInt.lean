import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionFoldableInt

/-! ## Class functions folded in normalize-only mode (`foldableFuns`): operators on `Int`
     See `ExtensionFoldableNat` for the description of the mechanism. -/

/-! `HAdd.hAdd` on `Int`. -/
axiom fia1 : Int → Int
@[blaster]
axiom fia1_lhs : ∀ (x : Int), fia1 (x + 1) = x

#testOptimize [ "ExtFoldIntAdd_1" ] ∀ (x : Int), fia1 (x + 1) = x ===> True
#testOptimize [ "ExtFoldIntAdd_2" ] ∀ (x : Int), fia1 (Int.add x 1) = x ===> True

axiom fia2 : Int → Int
@[blaster]
axiom fia2_rhs : ∀ (x : Int), fia2 x = x + 1

#testOptimize [ "ExtFoldIntAdd_3" ] ∀ (x : Int), fia2 x = x + 1 ===> True
#testOptimize [ "ExtFoldIntAdd_4" ] fia2 5 = 6 ===> True

axiom fia3 : Int → Int → Int
@[blaster]
axiom fia3_prem : ∀ (x y : Int), x + 1 < y → fia3 x y = x

#testOptimize [ "ExtFoldIntAdd_5" ] ∀ (x y : Int), x + 1 < y → fia3 x y = x ===> True

/-! `HSub.hSub` on `Int`: `Int.sub` is unfolded to `Int.add x (Int.neg y)` in the goal. -/
axiom fis1 : Int → Int
@[blaster]
axiom fis1_lhs : ∀ (x : Int), fis1 (x - 1) = x

#testOptimize [ "ExtFoldIntSub_1" ] ∀ (x : Int), fis1 (x - 1) = x ===> True

axiom fis2 : Int → Int
@[blaster]
axiom fis2_rhs : ∀ (x : Int), fis2 x = x - 1

#testOptimize [ "ExtFoldIntSub_2" ] ∀ (x : Int), fis2 x = x - 1 ===> True
#testOptimize [ "ExtFoldIntSub_3" ] fis2 5 = 4 ===> True

axiom fis3 : Int → Int → Int
@[blaster]
axiom fis3_prem : ∀ (x y : Int), x - 1 < y → fis3 x y = x

#testOptimize [ "ExtFoldIntSub_4" ] ∀ (x y : Int), x - 1 < y → fis3 x y = x ===> True

/-! `HMul.hMul` on `Int`. -/
axiom fim1 : Int → Int
@[blaster]
axiom fim1_lhs : ∀ (x : Int), fim1 (2 * x) = x

#testOptimize [ "ExtFoldIntMul_1" ] ∀ (x : Int), fim1 (2 * x) = x ===> True

axiom fim2 : Int → Int
@[blaster]
axiom fim2_rhs : ∀ (x : Int), fim2 x = 2 * x

#testOptimize [ "ExtFoldIntMul_2" ] ∀ (x : Int), fim2 x = 2 * x ===> True
#testOptimize [ "ExtFoldIntMul_3" ] fim2 5 = 10 ===> True

/-! `HDiv.hDiv` / `HMod.hMod` on `Int`. -/
axiom fid1 : Int → Int
@[blaster]
axiom fid1_lhs : ∀ (x : Int), fid1 (x / 2) = x

#testOptimize [ "ExtFoldIntDiv_1" ] ∀ (x : Int), fid1 (x / 2) = x ===> True

axiom fid2 : Int → Int
@[blaster]
axiom fid2_rhs : ∀ (x : Int), fid2 x = x / 2

#testOptimize [ "ExtFoldIntDiv_2" ] ∀ (x : Int), fid2 x = x / 2 ===> True
#testOptimize [ "ExtFoldIntDiv_3" ] fid2 9 = 4 ===> True

axiom fid3 : Int → Int → Int
@[blaster]
axiom fid3_prem : ∀ (x y : Int), x / 2 < y → fid3 x y = x

#testOptimize [ "ExtFoldIntDiv_4" ] ∀ (x y : Int), x / 2 < y → fid3 x y = x ===> True

axiom fio1 : Int → Int
@[blaster]
axiom fio1_lhs : ∀ (x : Int), fio1 (x % 2) = x

#testOptimize [ "ExtFoldIntMod_1" ] ∀ (x : Int), fio1 (x % 2) = x ===> True

axiom fio2 : Int → Int
@[blaster]
axiom fio2_rhs : ∀ (x : Int), fio2 x = x % 2

#testOptimize [ "ExtFoldIntMod_2" ] ∀ (x : Int), fio2 x = x % 2 ===> True
#testOptimize [ "ExtFoldIntMod_3" ] fio2 9 = 1 ===> True

axiom fio3 : Int → Int → Int
@[blaster]
axiom fio3_prem : ∀ (x y : Int), x % 2 < y → fio3 x y = x

#testOptimize [ "ExtFoldIntMod_4" ] ∀ (x y : Int), x % 2 < y → fio3 x y = x ===> True

/-! `HPow.hPow` on `Int` (`Int.pow`). -/
axiom fip1 : Int → Int
@[blaster]
axiom fip1_lhs : ∀ (x : Int), fip1 (x ^ 2) = x

#testOptimize [ "ExtFoldIntPow_1" ] ∀ (x : Int), fip1 (x ^ 2) = x ===> True

axiom fip2 : Int → Int
@[blaster]
axiom fip2_rhs : ∀ (x : Int), fip2 x = x ^ 2

#testOptimize [ "ExtFoldIntPow_2" ] ∀ (x : Int), fip2 x = x ^ 2 ===> True

/-! `Neg.neg` on `Int`. -/
axiom fin1 : Int → Int
@[blaster]
axiom fin1_lhs : ∀ (x : Int), fin1 (-x) = x

#testOptimize [ "ExtFoldIntNeg_1" ] ∀ (x : Int), fin1 (-x) = x ===> True
#testOptimize [ "ExtFoldIntNeg_2" ] ∀ (x : Int), fin1 (Int.neg x) = x ===> True

axiom fin2 : Int → Int
@[blaster]
axiom fin2_rhs : ∀ (x : Int), fin2 x = -x

#testOptimize [ "ExtFoldIntNeg_3" ] ∀ (x : Int), fin2 x = -x ===> True
#testOptimize [ "ExtFoldIntNeg_4" ] fin2 5 = -5 ===> True

axiom fin3 : Int → Int → Int
@[blaster]
axiom fin3_prem : ∀ (x y : Int), -x < y → fin3 x y = x

#testOptimize [ "ExtFoldIntNeg_5" ] ∀ (x y : Int), -x < y → fin3 x y = x ===> True

axiom fin4 : Int → Int
@[blaster]
axiom fin4_neg : ∀ (x : Int), fin4 (Neg.neg x) = x

#testOptimize [ "ExtFoldIntNeg_6" ] ∀ (x : Int), fin4 (-x) = x ===> True

end Test.ExtensionFoldableInt
