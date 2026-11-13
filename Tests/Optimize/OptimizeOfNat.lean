import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Test.OptimizeOfNat

/-! ## Test objectives to validate normalization rules on `OfNat.ofNat` (`optimizeOfNat?`)
      - `OfNat.ofNat Nat n ==> n`
      - `OfNat.ofNat Int n ==> Int.ofNat n`
      - `OfNat.ofNat UInt8/16/32/64/USize n ==> UInt8/16/32/64/USize.ofNat n`
      - `OfNat.ofNat Int8/16/32/64/ISize n ==> Int8/16/32/64/ISize.ofNat n`
      - `OfNat.ofNat (Fin k) n ==> Fin.ofNat k n`
      - `OfNat.ofNat (BitVec w) n ==> BitVec.ofNat w n`
    `OfNat.ofNat` on any other type is unfolded (instance projection).
-/

/-! Test cases for `OfNat.ofNat Nat n ==> n`. -/

-- n = 5 ===> 5 = n
#testOptimize [ "OfNatNat_1" ] (norm-result: 1) ∀ (n : Nat), n = 5 ===> ∀ (n : Nat), 5 = n

-- 5 = 5 ===> True
#testOptimize [ "OfNatNat_2" ] (5 : Nat) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatNat_3" ] (5 : Nat) = 7 ===> False

-- n + 7 = m ===> m = Nat.add 7 n
-- NOTE: reordering applied on operands
#testOptimize [ "OfNatNat_4" ] (norm-result: 1) ∀ (n m : Nat), n + 7 = m ===> ∀ (n m : Nat), m = Nat.add 7 n

-- 0 = n ===> 0 = n
#testOptimize [ "OfNatNat_5" ] (norm-result: 1) ∀ (n : Nat), 0 = n ===> ∀ (n : Nat), 0 = n

-- n = 5 → n + 1 = 6 ===> True
#testOptimize [ "OfNatNat_6" ] ∀ (n : Nat), n = 5 → n + 1 = 6 ===> True

-- @OfNat.ofNat Nat 7 (instOfNatNat 7) = 7 ===> True
#testOptimize [ "OfNatNat_7" ] @OfNat.ofNat Nat 7 (instOfNatNat 7) = 7 ===> True

/-! The rule must not ignore the instance: with a non-standard instance `⟨99⟩ : OfNat Nat 7`,
    `@OfNat.ofNat Nat 7 ⟨99⟩` is definitionally `99`, not `7`. -/

-- n = @OfNat.ofNat Nat 7 ⟨99⟩ ===> 99 = n
#testOptimize [ "OfNatNat_8" ] (norm-result: 1) ∀ (n : Nat), n = @OfNat.ofNat Nat 7 ⟨99⟩ ===> ∀ (n : Nat), 99 = n

-- @OfNat.ofNat Nat 7 ⟨99⟩ = 99 ===> True
#testOptimize [ "OfNatNat_9" ] @OfNat.ofNat Nat 7 ⟨99⟩ = 99 ===> True

-- @OfNat.ofNat Nat 7 ⟨99⟩ = 7 ===> False
#testOptimize [ "OfNatNat_10" ] @OfNat.ofNat Nat 7 ⟨99⟩ = 7 ===> False

-- symbolic instance: n = @OfNat.ofNat Nat 7 ⟨i⟩ ===> n = i
#testOptimize [ "OfNatNat_SymInst_1" ] ∀ (n i : Nat), n = @OfNat.ofNat Nat 7 ⟨i⟩ ===> ∀ (n i : Nat), n = i

-- symbolic instance: @OfNat.ofNat Nat 7 ⟨i⟩ = 7 ===> 7 = i
#testOptimize [ "OfNatNat_SymInst_2" ] (norm-result: 1) ∀ (i : Nat), @OfNat.ofNat Nat 7 ⟨i⟩ = 7 ===> ∀ (i : Nat), 7 = i

-- symbolic instance: @OfNat.ofNat Nat 7 ⟨i + 1⟩ = 0 ===> False
#testOptimize [ "OfNatNat_SymInst_3" ] ∀ (i : Nat), @OfNat.ofNat Nat 7 ⟨i + 1⟩ = 0 ===> False

-- local instance: nothing is known about `inst`, the application must be left alone
-- NOTE: a literal `7` elaborated under `[inst : OfNat Nat 7]` resolves to `inst` itself, hence `nat_lit`
#testOptimize [ "OfNatNat_LocalInst_1" ] ∀ [inst : OfNat Nat (nat_lit 7)], @OfNat.ofNat Nat (nat_lit 7) inst = nat_lit 7 ===>
                                         ∀ [inst : OfNat Nat (nat_lit 7)], nat_lit 7 = @OfNat.ofNat Nat (nat_lit 7) inst

-- local instance: x = OfNat.ofNat Nat 7 inst ===> x = OfNat.ofNat Nat 7 inst
#testOptimize [ "OfNatNat_LocalInst_2" ] ∀ [inst : OfNat Nat (nat_lit 7)] (x : Nat), x = @OfNat.ofNat Nat (nat_lit 7) inst ===>
                                         ∀ [inst : OfNat Nat (nat_lit 7)] (x : Nat), x = @OfNat.ofNat Nat (nat_lit 7) inst

-- non-literal argument: @OfNat.ofNat Nat (2 + 3) _ = 5 ===> True
#testOptimize [ "OfNatNat_11" ] @OfNat.ofNat Nat (2 + 3) (instOfNatNat (2 + 3)) = 5 ===> True

-- partial application: the instance is a bound variable, so `OfNat.ofNat` is not reduced to a projection
-- NOTE: `norm-result` is not used, as it would unfold the expected `OfNat.ofNat` into `inst.1`
#testOptimize [ "OfNatNat_12" ]
  ∀ (f : OfNat Nat 7 → Nat), f = @OfNat.ofNat Nat 7 ===>
  ∀ (f : OfNat Nat (nat_lit 7) → Nat), f = fun (inst : OfNat Nat (nat_lit 7)) => @OfNat.ofNat Nat (nat_lit 7) inst

/-! Test cases for `OfNat.ofNat Int n ==> Int.ofNat n`. -/

-- x = 5 ===> Int.ofNat 5 = x
#testOptimize [ "OfNatInt_1" ] (norm-result: 1) ∀ (x : Int), x = 5 ===> ∀ (x : Int), Int.ofNat 5 = x

-- x = 0 ===> 0 = x
#testOptimize [ "OfNatInt_2" ] (norm-result: 1) ∀ (x : Int), x = 0 ===> ∀ (x : Int), Int.ofNat 0 = x

-- 5 = 5 ===> True
#testOptimize [ "OfNatInt_3" ] (5 : Int) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatInt_4" ] (5 : Int) = 7 ===> False

-- x = -5 ===> Int.negSucc 4 = x
#testOptimize [ "OfNatInt_5" ] (norm-result: 1) ∀ (x : Int), x = -5 ===> ∀ (x : Int), Int.negSucc 4 = x

-- x + 7 = y ===> y = Int.add (Int.ofNat 7) x
-- NOTE: reordering applied on operands
#testOptimize [ "OfNatInt_6" ] (norm-result: 1) ∀ (x y : Int), x + 7 = y ===> ∀ (x y : Int), y = Int.add (Int.ofNat 7) x

-- (5 : Int) = Int.ofNat 5 ===> True
#testOptimize [ "OfNatInt_7" ] (5 : Int) = Int.ofNat 5 ===> True

-- x = 5 → x + 1 = 6 ===> True
#testOptimize [ "OfNatInt_8" ] ∀ (x : Int), x = 5 → x + 1 = 6 ===> True

-- non-standard instance: x = @OfNat.ofNat Int 7 ⟨99⟩ ===> Int.ofNat 99 = x
#testOptimize [ "OfNatInt_9" ] (norm-result: 1) ∀ (x : Int), x = @OfNat.ofNat Int 7 ⟨99⟩ ===> ∀ (x : Int), Int.ofNat 99 = x

-- @OfNat.ofNat Int 7 ⟨99⟩ = 7 ===> False
#testOptimize [ "OfNatInt_10" ] @OfNat.ofNat Int 7 ⟨99⟩ = 7 ===> False

-- symbolic instance: x = @OfNat.ofNat Int 7 ⟨i⟩ ===> x = i
#testOptimize [ "OfNatInt_SymInst_1" ] ∀ (x i : Int), x = @OfNat.ofNat Int 7 ⟨i⟩ ===> ∀ (x i : Int), x = i

-- symbolic instance: @OfNat.ofNat Int 7 ⟨i⟩ = 7 ===> Int.ofNat 7 = i
#testOptimize [ "OfNatInt_SymInst_2" ] (norm-result: 1) ∀ (i : Int), @OfNat.ofNat Int 7 ⟨i⟩ = 7 ===> ∀ (i : Int), Int.ofNat 7 = i

-- symbolic instance with a `Nat` payload: x = @OfNat.ofNat Int 7 ⟨Int.ofNat i⟩ ===> x = Int.ofNat i
-- NOTE: reordering applied on operands
#testOptimize [ "OfNatInt_SymInst_3" ] ∀ (x : Int) (i : Nat), x = @OfNat.ofNat Int 7 ⟨Int.ofNat i⟩ ===>
                                       ∀ (x : Int) (i : Nat), Int.ofNat i = x

-- local instance: nothing is known about `inst`, the application must be left alone
#testOptimize [ "OfNatInt_LocalInst_1" ] ∀ [inst : OfNat Int (nat_lit 7)], @OfNat.ofNat Int (nat_lit 7) inst = Int.ofNat 7 ===>
                                         ∀ [inst : OfNat Int (nat_lit 7)], Int.ofNat (nat_lit 7) = @OfNat.ofNat Int (nat_lit 7) inst

/-! Test cases for `OfNat.ofNat` on fixed-width unsigned integers.
    NOTE: `UIntN.ofNat n` is currently unfolded further, down to `UIntN.ofBitVec (BitVec.ofFin N ⟨n, _⟩)`
    (the dedicated `ofNat` functions are not opacified yet). The width of `USize` is platform dependent,
    so literal comparisons on `USize` are not decided. -/

-- x = 5 ===> UInt8.ofBitVec (BitVec.ofFin 8 ⟨5, _⟩) = x
#testOptimize [ "OfNatUInt8_1" ] (norm-result: 1) ∀ (x : UInt8), x = 5 ===>
  ∀ (x : UInt8), UInt8.ofBitVec (@BitVec.ofFin 8 (@Fin.mk 256 5
    (@of_decide_eq_true (5 < 256) (Nat.decLt 5 256) (@rfl Bool (@decide (5 < 256) (Nat.decLt 5 256)))))) = x

-- 5 = 5 ===> True
#testOptimize [ "OfNatUInt8_2" ] (5 : UInt8) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatUInt8_3" ] (5 : UInt8) = 7 ===> False

-- 300 = 44 ===> True (wrap around)
#testOptimize [ "OfNatUInt8_4" ] (300 : UInt8) = 44 ===> True

-- (5 : UInt8) = UInt8.ofNat 5 ===> True
#testOptimize [ "OfNatUInt8_5" ] (5 : UInt8) = UInt8.ofNat 5 ===> True

-- x = 5 → x = UInt8.ofNat 5 ===> True
#testOptimize [ "OfNatUInt8_6" ] ∀ (x : UInt8), x = 5 → x = UInt8.ofNat 5 ===> True

-- non-standard instance: @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat 99⟩ = 99 ===> True
#testOptimize [ "OfNatUInt8_7" ] @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat 99⟩ = 99 ===> True

-- non-standard instance: @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat 99⟩ = 7 ===> False
#testOptimize [ "OfNatUInt8_8" ] @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat 99⟩ = 7 ===> False

-- symbolic instance: x = @OfNat.ofNat UInt8 7 ⟨i⟩ ===> x = i
#testOptimize [ "OfNatUInt8_SymInst_1" ] ∀ (x i : UInt8), x = @OfNat.ofNat UInt8 7 ⟨i⟩ ===> ∀ (x i : UInt8), x = i

-- symbolic instance: @OfNat.ofNat UInt8 7 ⟨i⟩ = i ===> True
#testOptimize [ "OfNatUInt8_SymInst_2" ] ∀ (i : UInt8), @OfNat.ofNat UInt8 7 ⟨i⟩ = i ===> True

-- symbolic instance with a `Nat` payload: @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat i⟩ = UInt8.ofNat i ===> True
#testOptimize [ "OfNatUInt8_SymInst_3" ] ∀ (i : Nat), @OfNat.ofNat UInt8 7 ⟨UInt8.ofNat i⟩ = UInt8.ofNat i ===> True

-- local instance: x = OfNat.ofNat UInt8 7 inst ===> x = OfNat.ofNat UInt8 7 inst
#testOptimize [ "OfNatUInt8_LocalInst_1" ]
  ∀ [inst : OfNat UInt8 (nat_lit 7)] (x : UInt8), x = @OfNat.ofNat UInt8 (nat_lit 7) inst ===>
  ∀ [inst : OfNat UInt8 (nat_lit 7)] (x : UInt8), x = @OfNat.ofNat UInt8 (nat_lit 7) inst

-- 5 = 5 ===> True
#testOptimize [ "OfNatUInt16_1" ] (5 : UInt16) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatUInt16_2" ] (5 : UInt16) = 7 ===> False

-- 70000 = 4464 ===> True (wrap around)
#testOptimize [ "OfNatUInt16_3" ] (70000 : UInt16) = 4464 ===> True

-- x = 5 → x = UInt16.ofNat 5 ===> True
#testOptimize [ "OfNatUInt16_4" ] ∀ (x : UInt16), x = 5 → x = UInt16.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatUInt32_1" ] (5 : UInt32) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatUInt32_2" ] (5 : UInt32) = 7 ===> False

-- 4294967301 = 5 ===> True (wrap around)
#testOptimize [ "OfNatUInt32_3" ] (4294967301 : UInt32) = 5 ===> True

-- x = 5 → x = UInt32.ofNat 5 ===> True
#testOptimize [ "OfNatUInt32_4" ] ∀ (x : UInt32), x = 5 → x = UInt32.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatUInt64_1" ] (5 : UInt64) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatUInt64_2" ] (5 : UInt64) = 7 ===> False

-- 18446744073709551621 = 5 ===> True (wrap around)
#testOptimize [ "OfNatUInt64_3" ] (18446744073709551621 : UInt64) = 5 ===> True

-- x = 5 → x = UInt64.ofNat 5 ===> True
#testOptimize [ "OfNatUInt64_4" ] ∀ (x : UInt64), x = 5 → x = UInt64.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatUSize_1" ] (5 : USize) = 5 ===> True

-- (5 : USize) = USize.ofNat 5 ===> True
#testOptimize [ "OfNatUSize_2" ] (5 : USize) = USize.ofNat 5 ===> True

-- x = 5 → x = USize.ofNat 5 ===> True
#testOptimize [ "OfNatUSize_3" ] ∀ (x : USize), x = 5 → x = USize.ofNat 5 ===> True

/-! Test cases for `OfNat.ofNat` on fixed-width signed integers
    (`IntN.ofNat n` is unfolded to `IntN.ofUIntN (UIntN.ofNat n)`, with `IntN.ofUIntN` private). -/

-- 5 = 5 ===> True
#testOptimize [ "OfNatInt8_1" ] (5 : Int8) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatInt8_2" ] (5 : Int8) = 7 ===> False

-- (5 : Int8) = Int8.ofNat 5 ===> True
#testOptimize [ "OfNatInt8_3" ] (5 : Int8) = Int8.ofNat 5 ===> True

-- x = 5 → x = Int8.ofNat 5 ===> True
#testOptimize [ "OfNatInt8_4" ] ∀ (x : Int8), x = 5 → x = Int8.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatInt16_1" ] (5 : Int16) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatInt16_2" ] (5 : Int16) = 7 ===> False

-- x = 5 → x = Int16.ofNat 5 ===> True
#testOptimize [ "OfNatInt16_3" ] ∀ (x : Int16), x = 5 → x = Int16.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatInt32_1" ] (5 : Int32) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatInt32_2" ] (5 : Int32) = 7 ===> False

-- x = 5 → x = Int32.ofNat 5 ===> True
#testOptimize [ "OfNatInt32_3" ] ∀ (x : Int32), x = 5 → x = Int32.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatInt64_1" ] (5 : Int64) = 5 ===> True

-- 5 = 7 ===> False
#testOptimize [ "OfNatInt64_2" ] (5 : Int64) = 7 ===> False

-- x = 5 → x = Int64.ofNat 5 ===> True
#testOptimize [ "OfNatInt64_3" ] ∀ (x : Int64), x = 5 → x = Int64.ofNat 5 ===> True

-- 5 = 5 ===> True
#testOptimize [ "OfNatISize_1" ] (5 : ISize) = 5 ===> True

-- (5 : ISize) = ISize.ofNat 5 ===> True
#testOptimize [ "OfNatISize_2" ] (5 : ISize) = ISize.ofNat 5 ===> True

-- x = 5 → x = ISize.ofNat 5 ===> True
#testOptimize [ "OfNatISize_3" ] ∀ (x : ISize), x = 5 → x = ISize.ofNat 5 ===> True

/-! Test cases for `OfNat.ofNat (Fin k) n ==> Fin.ofNat k n` (unfolded further to `Fin.mk (n % k) _`). -/

-- x = 3 ===> Fin.mk 3 _ = x
#testOptimize [ "OfNatFin_1" ] (norm-result: 1) ∀ (x : Fin 5), x = 3 ===>
  ∀ (x : Fin 5), (@Fin.mk 5 3
    (@of_decide_eq_true (3 < 5) (Nat.decLt 3 5) (@rfl Bool (@decide (3 < 5) (Nat.decLt 3 5))))) = x

-- 3 = 3 ===> True
#testOptimize [ "OfNatFin_2" ] (3 : Fin 5) = 3 ===> True

-- 3 = 4 ===> False
#testOptimize [ "OfNatFin_3" ] (3 : Fin 5) = 4 ===> False

-- 8 = 3 ===> True (modulo 5)
#testOptimize [ "OfNatFin_4" ] (8 : Fin 5) = 3 ===> True

-- (3 : Fin 5) = Fin.ofNat 5 3 ===> True
#testOptimize [ "OfNatFin_5" ] (3 : Fin 5) = Fin.ofNat 5 3 ===> True

-- (3 : Fin 5) = ⟨3, _⟩ ===> True
#testOptimize [ "OfNatFin_6" ] (3 : Fin 5) = ⟨3, by decide⟩ ===> True

-- x = 3 → x = Fin.ofNat 5 3 ===> True
#testOptimize [ "OfNatFin_7" ] ∀ (x : Fin 5), x = 3 → x = Fin.ofNat 5 3 ===> True

-- parametric bound: x = 3 → x = Fin.ofNat k 3 ===> True
#testOptimize [ "OfNatFin_8" ] ∀ (k : Nat) [NeZero k] (x : Fin k), x = 3 → x = Fin.ofNat k 3 ===> True

-- parametric bound: (3 : Fin k) = ⟨3 % k, _⟩ ===> True
#testOptimize [ "OfNatFin_9" ] ∀ (k : Nat) [NeZero k], (3 : Fin k) = ⟨3 % k, Nat.mod_lt 3 (Nat.pos_of_neZero k)⟩ ===> True

/-! Test cases for `OfNat.ofNat (BitVec w) n ==> BitVec.ofNat w n` (unfolded further to `BitVec.ofFin ⟨n % 2^w, _⟩`). -/

-- x = 3 ===> BitVec.ofFin 8 ⟨3, _⟩ = x
#testOptimize [ "OfNatBitVec_1" ] (norm-result: 1) ∀ (x : BitVec 8), x = 3 ===>
  ∀ (x : BitVec 8), @BitVec.ofFin 8 (@Fin.mk 256 3
    (@of_decide_eq_true (3 < 256) (Nat.decLt 3 256) (@rfl Bool (@decide (3 < 256) (Nat.decLt 3 256))))) = x

-- 3 = 3 ===> True
#testOptimize [ "OfNatBitVec_2" ] (3 : BitVec 8) = 3 ===> True

-- 3 = 4 ===> False
#testOptimize [ "OfNatBitVec_3" ] (3 : BitVec 8) = 4 ===> False

-- 259 = 3 ===> True (wrap around)
#testOptimize [ "OfNatBitVec_4" ] (259 : BitVec 8) = 3 ===> True

-- (3 : BitVec 8) = BitVec.ofNat 8 3 ===> True
#testOptimize [ "OfNatBitVec_5" ] (3 : BitVec 8) = BitVec.ofNat 8 3 ===> True

-- (3 : BitVec 8) = 3#8 ===> True
#testOptimize [ "OfNatBitVec_6" ] (3 : BitVec 8) = 3#8 ===> True

-- x = 3 → x = BitVec.ofNat 8 3 ===> True
#testOptimize [ "OfNatBitVec_7" ] ∀ (x : BitVec 8), x = 3 → x = BitVec.ofNat 8 3 ===> True

-- parametric width: x = 3 → x = BitVec.ofNat w 3 ===> True
#testOptimize [ "OfNatBitVec_8" ] ∀ (w : Nat) (x : BitVec w), x = 3 → x = BitVec.ofNat w 3 ===> True

-- parametric width: (3 : BitVec w) = 3#w ===> True
#testOptimize [ "OfNatBitVec_9" ] ∀ (w : Nat), (3 : BitVec w) = 3#w ===> True

/-! Constructor instances on `Fin` and `BitVec`: `OfNat.ofNat T n ⟨v⟩ ==> v`. -/

-- @OfNat.ofNat (Fin 5) 7 ⟨⟨3, _⟩⟩ = 3 ===> True
#testOptimize [ "OfNatFin_CtorInst_1" ] @OfNat.ofNat (Fin 5) 7 ⟨⟨3, by decide⟩⟩ = 3 ===> True

-- @OfNat.ofNat (Fin 5) 7 ⟨⟨3, _⟩⟩ = 2 ===> False
#testOptimize [ "OfNatFin_CtorInst_2" ] @OfNat.ofNat (Fin 5) 7 ⟨⟨3, by decide⟩⟩ = 2 ===> False

-- @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ = 99 ===> True
#testOptimize [ "OfNatBitVec_CtorInst_1" ] @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ = 99 ===> True

-- @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ = 7 ===> False
#testOptimize [ "OfNatBitVec_CtorInst_2" ] @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ = 7 ===> False

-- @OfNat.ofNat (BitVec 8) 7 ⟨99#8⟩ = 99 ===> True
#testOptimize [ "OfNatBitVec_CtorInst_3" ] @OfNat.ofNat (BitVec 8) 7 ⟨99#8⟩ = 99 ===> True

-- x = @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ → x = 99 ===> True
#testOptimize [ "OfNatBitVec_CtorInst_4" ] ∀ (x : BitVec 8), x = @OfNat.ofNat (BitVec 8) 7 ⟨99⟩ → x = 99 ===> True

/-! Test cases for `OfNat.ofNat` on types without a dedicated rule (the instance is unfolded). -/

structure Wrap where
  val : Nat

instance : OfNat Wrap n := ⟨⟨n⟩⟩

-- w = 5 ===> Wrap.mk 5 = w
#testOptimize [ "OfNatOther_1" ] (norm-result: 1) ∀ (w : Wrap), w = 5 ===> ∀ (w : Wrap), Wrap.mk 5 = w

-- (5 : Wrap).val = 5 ===> True
#testOptimize [ "OfNatOther_2" ] (5 : Wrap).val = 5 ===> True

-- (5 : Wrap) = ⟨5⟩ ===> True
#testOptimize [ "OfNatOther_3" ] (5 : Wrap) = ⟨5⟩ ===> True

-- (5 : Wrap) = ⟨7⟩ ===> False
#testOptimize [ "OfNatOther_4" ] (5 : Wrap) = ⟨7⟩ ===> False

-- instance with a non-identity value
structure Twice where
  val : Nat

instance : OfNat Twice n := ⟨⟨2 * n⟩⟩

-- (5 : Twice).val = 10 ===> True
#testOptimize [ "OfNatOther_5" ] (5 : Twice).val = 10 ===> True

-- t = 5 ===> Twice.mk 10 = t
#testOptimize [ "OfNatOther_6" ] (norm-result: 1) ∀ (t : Twice), t = 5 ===> ∀ (t : Twice), Twice.mk 10 = t

-- generic type with an `OfNat` instance in scope
#testOptimize [ "OfNatOther_7" ] ∀ (α : Type) [OfNat α (nat_lit 5)] (x : α), x = 5 ===>
                                 ∀ (α : Type) [OfNat α (nat_lit 5)] (x : α), x = 5

end Test.OptimizeOfNat
