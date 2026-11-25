import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionOfNat

/-! ## `OfNat.ofNat` with a non-standard instance in a rule
     The optimizer only reduces `OfNat.ofNat T n inst` natively when `inst` is the standard instance of `T`;
     any other instance has to be unfolded (its value is unrelated to `n`). Theorems are normalized in
     normalize-only mode, in which functions are not unfolded: the rules are declared with `restart := true`
     so that the rewritten term goes through optimization again. These cases check that a non-standard
     instance in the lhs, the rhs or a premise of a rule is handled consistently with the normal form of
     the goal. -/

/-! Standard instance (control). -/
axiom on0 : Nat → Nat

@[blaster (noRestart := true)]
axiom on0_rhs : ∀ (n : Nat), on0 n = 7

#testOptimize [ "ExtOfNatStd_1" ] ∀ (n : Nat), on0 n = 7 ===> True
#testOptimize [ "ExtOfNatStd_2" ] (norm-result: 1) ∀ (n m : Nat), on0 n = m ===> ∀ (m : Nat), 7 = m

/-! Non-standard instance in the rhs (`Nat`). -/
axiom on1 : Nat → Nat

@[blaster]
axiom on1_rhs : ∀ (n : Nat), on1 n = @OfNat.ofNat Nat 7 ⟨99⟩

#testOptimize [ "ExtOfNatRhs_1" ] ∀ (n : Nat), on1 n = 99 ===> True
#testOptimize [ "ExtOfNatRhs_2" ] ∀ (n : Nat), on1 n = 7 ===> False
#testOptimize [ "ExtOfNatRhs_3" ] (norm-result: 1) ∀ (n m : Nat), on1 n = m ===> ∀ (m : Nat), 99 = m

/-! Non-standard instance in the rhs (`Int`). -/
axiom on2 : Int → Int

@[blaster]
axiom on2_rhs : ∀ (x : Int), on2 x = @OfNat.ofNat Int 7 ⟨99⟩

#testOptimize [ "ExtOfNatRhsInt_1" ] ∀ (x : Int), on2 x = 99 ===> True
#testOptimize [ "ExtOfNatRhsInt_2" ] ∀ (x : Int), on2 x = 7 ===> False

/-! Symbolic instance in the rhs: the payload is a pattern variable. -/
axiom on3 : Nat → Nat

@[blaster]
axiom on3_rhs : ∀ (i : Nat), on3 i = @OfNat.ofNat Nat 7 ⟨i + 1⟩

#testOptimize [ "ExtOfNatRhsSym_1" ] ∀ (i : Nat), on3 i = i + 1 ===> True
#testOptimize [ "ExtOfNatRhsSym_2" ] on3 4 = 5 ===> True

/-! Non-standard instance in the lhs: the goal is unfolded before the rule is tried. -/
axiom on4 : Nat → Nat

@[blaster]
axiom on4_lhs : ∀ (i : Nat), on4 (@OfNat.ofNat Nat 7 ⟨i⟩) = i

#testOptimize [ "ExtOfNatLhs_1" ] ∀ (i : Nat), on4 (@OfNat.ofNat Nat 7 ⟨i⟩) = i ===> True
#testOptimize [ "ExtOfNatLhs_2" ] ∀ (i : Nat), on4 i = i ===> True
#testOptimize [ "ExtOfNatLhs_3" ] on4 5 = 5 ===> True

/-! Non-standard instance in a premise (a relational premise, as an equality premise `n = c`
    substitutes `n` in the conclusion and the rule is rejected). -/
axiom on5 : Nat → Nat

@[blaster]
axiom on5_prem : ∀ (n : Nat), @OfNat.ofNat Nat 7 ⟨99⟩ < n → on5 n = 0

#testOptimize [ "ExtOfNatPrem_1" ] ∀ (n : Nat), 99 < n → on5 n = 0 ===> True
#testOptimize [ "ExtOfNatPrem_2" ] on5 100 = 0 ===> True
-- premise not available: no rewriting
#testOptimize [ "ExtOfNatPrem_3" ] (norm-result: 1) ∀ (n : Nat), 7 < n → on5 n = 0 ===> ∀ (n : Nat), 7 < n → 0 = on5 n

/-! Local instance in a rule: the instance is a pattern variable, the application must stay symbolic. -/
axiom on6 : Nat → Nat → Nat

@[blaster]
axiom on6_inst : ∀ [inst : OfNat Nat (nat_lit 7)] (n : Nat), on6 (@OfNat.ofNat Nat (nat_lit 7) inst) n = n

#testOptimize [ "ExtOfNatLocalInst_1" ] ∀ [inst : OfNat Nat (nat_lit 7)] (n : Nat), on6 (@OfNat.ofNat Nat (nat_lit 7) inst) n = n ===> True
#testOptimize [ "ExtOfNatLocalInst_2" ] ∀ (n : Nat), on6 7 n = n ===> True
-- the goal's instance `⟨99⟩` is projected before the rule is tried: the pattern variable `inst`
-- cannot match a bare literal, no rewriting
#testOptimize [ "ExtOfNatLocalInst_3" ] (norm-result: 1) ∀ (n : Nat), on6 (@OfNat.ofNat Nat 7 ⟨99⟩) n = n ===> ∀ (n : Nat), n = on6 99 n
-- no rewriting
#testOptimize [ "ExtOfNatLocalInst_4" ] (norm-result: 1) ∀ (n : Nat), on6 8 n = n ===> ∀ (n : Nat), n = on6 8 n

/-! `BitVec` literals in rules. In normalize-only mode a literal stops at `BitVec.ofNat w n` (the dedicated
    `ofNat` functions are not opaque yet), whereas the goal unfolds it down to `BitVec.ofFin w ⟨n, _⟩`:
    a rhs is recovered through `restart := true`, but a literal in the lhs does not match the goal.
    TODO: the commented test cases `ExtOfNatBitVecLhs_1` and `ExtOfNatBitVecLhs_2` will be handled
    (and must be re-enabled) once `BitVec.ofNat` is opacified: both modes will then stop at
    `BitVec.ofNat w n` and the lhs literal will match the goal. -/
axiom onb1 : BitVec 8 → BitVec 8

@[blaster]
axiom onb1_rhs : ∀ (x : BitVec 8), onb1 x = 99

#testOptimize [ "ExtOfNatBitVecRhs_1" ] ∀ (x : BitVec 8), onb1 x = 99 ===> True

axiom onb2 : BitVec 8 → BitVec 8

@[blaster]
axiom onb2_rhs : ∀ (x : BitVec 8), onb2 x = @OfNat.ofNat (BitVec 8) 7 ⟨99⟩

#testOptimize [ "ExtOfNatBitVecRhs_2" ] ∀ (x : BitVec 8), onb2 x = 99 ===> True

axiom onb3 : BitVec 8 → BitVec 8 → BitVec 8

@[blaster]
axiom onb3_lhs : ∀ (x : BitVec 8), onb3 99 x = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtOfNatBitVecLhs_1" ] ∀ (x : BitVec 8), onb3 99 x = x ===> True

axiom onb4 : BitVec 8 → BitVec 8 → BitVec 8

@[blaster]
axiom onb4_lhs : ∀ (x : BitVec 8), onb4 (@OfNat.ofNat (BitVec 8) 7 ⟨99⟩) x = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtOfNatBitVecLhs_2" ] ∀ (x : BitVec 8), onb4 99 x = x ===> True

/-! `Int` literals in rules: a non-negative literal normalizes to `Int.ofNat n` in both modes, but a
    negative literal stops at `Int.neg (Int.ofNat n)` in normalize-only mode whereas the goal reduces it
    to `Int.negSucc (n - 1)`: a negative literal in the lhs does not match the goal.
    TODO: the commented test case `ExtOfNatIntLhs_3` will be handled (and must be re-enabled) together
    with the opacification of `BitVec.ofNat`, when the literal normal forms of both modes are aligned. -/
axiom oni1 : Int → Int → Int

@[blaster]
axiom oni1_lhs : ∀ (x : Int), oni1 99 x = x

#testOptimize [ "ExtOfNatIntLhs_1" ] ∀ (x : Int), oni1 99 x = x ===> True

axiom oni2 : Int → Int → Int

@[blaster]
axiom oni2_lhs : ∀ (x : Int), oni2 (@OfNat.ofNat Int 7 ⟨99⟩) x = x

#testOptimize [ "ExtOfNatIntLhs_2" ] ∀ (x : Int), oni2 99 x = x ===> True

axiom oni3 : Int → Int → Int

@[blaster]
axiom oni3_lhs : ∀ (x : Int), oni3 (-5) x = x

#testOptimize [ "ExtOfNatIntLhs_3" ] ∀ (x : Int), oni3 (-5) x = x ===> True

axiom oni4 : Int → Int

@[blaster]
axiom oni4_rhs : ∀ (x : Int), oni4 x = -5

#testOptimize [ "ExtOfNatIntRhs_1" ] ∀ (x : Int), oni4 x = -5 ===> True

end Test.ExtensionOfNat
