import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionFoldableNat

/-! ## Class functions folded in normalize-only mode (`foldableFuns`)
     Theorems are normalized in normalize-only mode, in which no function is unfolded except the class
     functions listed in `foldableFuns` (`Opaque.lean`): `Ne`, `OfNat.ofNat`, `HAdd.hAdd`, `HSub.hSub`,
     `HMul.hMul`, `HDiv.hDiv`, `HMod.hMod`, `HPow.hPow`, `Add.add`, `Sub.sub`, `Div.div`, `Mod.mod`,
     `Neg.neg`, `NatPow.pow`, `Append.append`, `HAppend.hAppend`, `GetElem?.getElem?`. An operator written
     with its class function in a rule (`n + 1`, `x / 2`, `-x`, `l ++ m`, `l[i]?`, `n ≠ 0`, ...) must reach the
     same normal form as in the goal (`Nat.add 1 n`, `Int.neg x`, `List.append l m`, `¬ (n = 0)`, ...), otherwise
     the lhs does not match and the rhs / premises are not comparable with the goal. Each operator is checked
     in the lhs, the rhs and a premise of a rule, through the heterogeneous class function (`HAdd.hAdd`, ...)
     and the homogeneous one (`Add.add`, ...). `OfNat.ofNat` is covered by the previous section.
     Rules are tried before the arguments of the application are optimized: an argument reused in the rhs
     may still be un-normalized (e.g., `OfNat.ofNat Nat 5 _`, `HAdd.hAdd … n 1`), hence rules whose rhs
     reuses an argument are declared with `restart := true` so that the rewritten term is optimized again
     (see the `ExtFoldRestart` cases). -/

/-! `HAdd.hAdd` / `Add.add` on `Nat`. -/
axiom foa1 : Nat → Nat
@[blaster]
axiom foa1_lhs : ∀ (n : Nat), foa1 (n + 1) = n

#testOptimize [ "ExtFoldNatAdd_1" ] ∀ (n : Nat), foa1 (n + 1) = n ===> True
#testOptimize [ "ExtFoldNatAdd_2" ] ∀ (n : Nat), foa1 (1 + n) = n ===> True
#testOptimize [ "ExtFoldNatAdd_3" ] ∀ (n : Nat), foa1 (Nat.add n 1) = n ===> True
-- no rewriting: the literal `5` does not match the pattern `Nat.add 1 n`
#testOptimize [ "ExtFoldNatAdd_4" ] (norm-result: 1) foa1 5 = 4 ===> 4 = foa1 5

axiom foa2 : Nat → Nat
@[blaster]
axiom foa2_rhs : ∀ (n : Nat), foa2 n = n + 1

#testOptimize [ "ExtFoldNatAdd_5" ] ∀ (n : Nat), foa2 n = n + 1 ===> True
#testOptimize [ "ExtFoldNatAdd_6" ] ∀ (n : Nat), foa2 n = Nat.add 1 n ===> True
#testOptimize [ "ExtFoldNatAdd_7" ] foa2 5 = 6 ===> True

axiom foa3 : Nat → Nat → Nat
@[blaster]
axiom foa3_prem : ∀ (n m : Nat), n + 1 < m → foa3 n m = n

#testOptimize [ "ExtFoldNatAdd_8" ] ∀ (n m : Nat), n + 1 < m → foa3 n m = n ===> True
#testOptimize [ "ExtFoldNatAdd_9" ] ∀ (n m : Nat), Nat.add 1 n < m → foa3 n m = n ===> True
-- premise not available: no rewriting
#testOptimize [ "ExtFoldNatAdd_10" ] (norm-result: 1) ∀ (n m : Nat), n < m → foa3 n m = n ===> ∀ (n m : Nat), n < m → n = foa3 n m

axiom foa4 : Nat → Nat
@[blaster]
axiom foa4_add : ∀ (n : Nat), foa4 (Add.add n 1) = n

#testOptimize [ "ExtFoldNatAdd_11" ] ∀ (n : Nat), foa4 (n + 1) = n ===> True

-- literals are folded on both sides: `n + 1 + 1` and `n + 2` have the same normal form
axiom foa5 : Nat → Nat
@[blaster]
axiom foa5_fold : ∀ (n : Nat), foa5 (n + 1 + 1) = n

#testOptimize [ "ExtFoldNatAdd_12" ] ∀ (n : Nat), foa5 (n + 2) = n ===> True

/-! `HSub.hSub` / `Sub.sub` on `Nat`. -/
axiom fos1 : Nat → Nat
@[blaster]
axiom fos1_lhs : ∀ (n : Nat), fos1 (n - 1) = n

#testOptimize [ "ExtFoldNatSub_1" ] ∀ (n : Nat), fos1 (n - 1) = n ===> True
#testOptimize [ "ExtFoldNatSub_2" ] ∀ (n : Nat), fos1 (Nat.sub n 1) = n ===> True

axiom fos2 : Nat → Nat
@[blaster]
axiom fos2_rhs : ∀ (n : Nat), fos2 n = n - 1

#testOptimize [ "ExtFoldNatSub_3" ] ∀ (n : Nat), fos2 n = n - 1 ===> True
#testOptimize [ "ExtFoldNatSub_4" ] fos2 5 = 4 ===> True

axiom fos3 : Nat → Nat → Nat
@[blaster]
axiom fos3_prem : ∀ (n m : Nat), n - 1 < m → fos3 n m = n

#testOptimize [ "ExtFoldNatSub_5" ] ∀ (n m : Nat), n - 1 < m → fos3 n m = n ===> True

axiom fos4 : Nat → Nat
@[blaster]
axiom fos4_sub : ∀ (n : Nat), fos4 (Sub.sub n 1) = n

#testOptimize [ "ExtFoldNatSub_6" ] ∀ (n : Nat), fos4 (n - 1) = n ===> True

/-! `HMul.hMul` / `Mul.mul` on `Nat`. -/
axiom fom1 : Nat → Nat
@[blaster]
axiom fom1_lhs : ∀ (n : Nat), fom1 (2 * n) = n

#testOptimize [ "ExtFoldNatMul_1" ] ∀ (n : Nat), fom1 (2 * n) = n ===> True
#testOptimize [ "ExtFoldNatMul_2" ] ∀ (n : Nat), fom1 (Nat.mul 2 n) = n ===> True

axiom fom2 : Nat → Nat
@[blaster]
axiom fom2_rhs : ∀ (n : Nat), fom2 n = 2 * n

#testOptimize [ "ExtFoldNatMul_3" ] ∀ (n : Nat), fom2 n = 2 * n ===> True
#testOptimize [ "ExtFoldNatMul_4" ] fom2 5 = 10 ===> True

axiom fom3 : Nat → Nat → Nat
@[blaster]
axiom fom3_prem : ∀ (n m : Nat), 2 * n < m → fom3 n m = n

#testOptimize [ "ExtFoldNatMul_5" ] ∀ (n m : Nat), 2 * n < m → fom3 n m = n ===> True

axiom fom4 : Nat → Nat
@[blaster]
axiom fom4_mul : ∀ (n : Nat), fom4 (Mul.mul 2 n) = n

#testOptimize [ "ExtFoldNatMul_6" ] ∀ (n : Nat), fom4 (2 * n) = n ===> True

/-! `HDiv.hDiv` / `Div.div` on `Nat`. -/
axiom fod1 : Nat → Nat
@[blaster]
axiom fod1_lhs : ∀ (n : Nat), fod1 (n / 2) = n

#testOptimize [ "ExtFoldNatDiv_1" ] ∀ (n : Nat), fod1 (n / 2) = n ===> True
#testOptimize [ "ExtFoldNatDiv_2" ] ∀ (n : Nat), fod1 (Nat.div n 2) = n ===> True

axiom fod2 : Nat → Nat
@[blaster]
axiom fod2_rhs : ∀ (n : Nat), fod2 n = n / 2

#testOptimize [ "ExtFoldNatDiv_3" ] ∀ (n : Nat), fod2 n = n / 2 ===> True
#testOptimize [ "ExtFoldNatDiv_4" ] fod2 9 = 4 ===> True

axiom fod3 : Nat → Nat → Nat
@[blaster]
axiom fod3_prem : ∀ (n m : Nat), n / 2 < m → fod3 n m = n

#testOptimize [ "ExtFoldNatDiv_5" ] ∀ (n m : Nat), n / 2 < m → fod3 n m = n ===> True

axiom fod4 : Nat → Nat
@[blaster]
axiom fod4_div : ∀ (n : Nat), fod4 (Div.div n 2) = n

#testOptimize [ "ExtFoldNatDiv_6" ] ∀ (n : Nat), fod4 (n / 2) = n ===> True

/-! `HMod.hMod` / `Mod.mod` on `Nat`. -/
axiom foo1 : Nat → Nat
@[blaster]
axiom foo1_lhs : ∀ (n : Nat), foo1 (n % 2) = n

#testOptimize [ "ExtFoldNatMod_1" ] ∀ (n : Nat), foo1 (n % 2) = n ===> True
#testOptimize [ "ExtFoldNatMod_2" ] ∀ (n : Nat), foo1 (Nat.mod n 2) = n ===> True

axiom foo2 : Nat → Nat
@[blaster]
axiom foo2_rhs : ∀ (n : Nat), foo2 n = n % 2

#testOptimize [ "ExtFoldNatMod_3" ] ∀ (n : Nat), foo2 n = n % 2 ===> True
#testOptimize [ "ExtFoldNatMod_4" ] foo2 9 = 1 ===> True

axiom foo3 : Nat → Nat → Nat
@[blaster]
axiom foo3_prem : ∀ (n m : Nat), 0 < n % 2 → foo3 n m = n

#testOptimize [ "ExtFoldNatMod_5" ] ∀ (n m : Nat), 0 < n % 2 → foo3 n m = n ===> True

axiom foo4 : Nat → Nat
@[blaster]
axiom foo4_mod : ∀ (n : Nat), foo4 (Mod.mod n 2) = n

#testOptimize [ "ExtFoldNatMod_6" ] ∀ (n : Nat), foo4 (n % 2) = n ===> True

/-! `HPow.hPow` / `Pow.pow` / `NatPow.pow` on `Nat` (`n ^ 2` unfolds through `instHPow`, `instPowNat` and
    `instNatPowNat`, i.e. `HPow.hPow` ↦ `Pow.pow` ↦ `NatPow.pow` ↦ `Nat.pow`). -/
axiom fop1 : Nat → Nat
@[blaster]
axiom fop1_lhs : ∀ (n : Nat), fop1 (n ^ 2) = n

#testOptimize [ "ExtFoldNatPow_1" ] ∀ (n : Nat), fop1 (n ^ 2) = n ===> True
#testOptimize [ "ExtFoldNatPow_2" ] ∀ (n : Nat), fop1 (Nat.pow n 2) = n ===> True

axiom fop2 : Nat → Nat
@[blaster]
axiom fop2_rhs : ∀ (n : Nat), fop2 n = n ^ 2

#testOptimize [ "ExtFoldNatPow_3" ] ∀ (n : Nat), fop2 n = n ^ 2 ===> True
#testOptimize [ "ExtFoldNatPow_4" ] fop2 3 = 9 ===> True

axiom fop3 : Nat → Nat
@[blaster]
axiom fop3_pow : ∀ (n : Nat), fop3 (Pow.pow n 2) = n

#testOptimize [ "ExtFoldNatPow_5" ] ∀ (n : Nat), fop3 (n ^ 2) = n ===> True

axiom fop4 : Nat → Nat
@[blaster]
axiom fop4_natpow : ∀ (n : Nat), fop4 (NatPow.pow n 2) = n

#testOptimize [ "ExtFoldNatPow_6" ] ∀ (n : Nat), fop4 (n ^ 2) = n ===> True

/-! Several operators in a single rule. -/
axiom fox1 : Nat → Nat → Nat
@[blaster]
axiom fox1_mixed : ∀ (n m : Nat), fox1 (n + m) (n - m) = (n + m) / 2 % 7

#testOptimize [ "ExtFoldNatMixed_1" ] ∀ (n m : Nat), fox1 (n + m) (n - m) = (n + m) / 2 % 7 ===> True
#testOptimize [ "ExtFoldNatMixed_2" ] ∀ (n m : Nat), fox1 (m + n) (n - m) = Nat.mod (Nat.div (Nat.add n m) 2) 7 ===> True

end Test.ExtensionFoldableNat
