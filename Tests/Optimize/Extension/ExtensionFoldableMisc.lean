import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionFoldableMisc

/-! ## Class functions folded in normalize-only mode (`foldableFuns`): `HAppend.hAppend`, `GetElem?.getElem?`,
     `Ne`, rules whose rhs reuses an argument (`restart`), and `UInt8`.
     See `ExtensionFoldableNat` for the description of the mechanism. -/

/-! `HAppend.hAppend` / `Append.append` on `List` and `String`. -/
axiom fol1 : List Nat → Nat
@[blaster]
axiom fol1_lhs : ∀ (l : List Nat) (a : Nat), fol1 (l ++ [a]) = a

#testOptimize [ "ExtFoldListApp_1" ] ∀ (l : List Nat) (a : Nat), fol1 (l ++ [a]) = a ===> True
#testOptimize [ "ExtFoldListApp_2" ] ∀ (l : List Nat) (a : Nat), fol1 (List.append l [a]) = a ===> True

axiom fol2 : List Nat → List Nat
@[blaster]
axiom fol2_rhs : ∀ (l : List Nat), fol2 l = l ++ [0]

#testOptimize [ "ExtFoldListApp_3" ] ∀ (l : List Nat), fol2 l = l ++ [0] ===> True
#testOptimize [ "ExtFoldListApp_4" ] fol2 [1] = [1, 0] ===> True

axiom fol3 : List Nat → List Nat → Nat
@[blaster]
axiom fol3_prem : ∀ (l m : List Nat), l ++ m = [] → fol3 l m = 0

#testOptimize [ "ExtFoldListApp_5" ] ∀ (l m : List Nat), l ++ m = [] → fol3 l m = 0 ===> True

axiom fol4 : List Nat → Nat
@[blaster]
axiom fol4_app : ∀ (l : List Nat) (a : Nat), fol4 (Append.append l [a]) = a

#testOptimize [ "ExtFoldListApp_6" ] ∀ (l : List Nat) (a : Nat), fol4 (l ++ [a]) = a ===> True

axiom fost1 : String → Nat
@[blaster]
axiom fost1_lhs : ∀ (s : String), fost1 (s ++ "a") = 0

#testOptimize [ "ExtFoldStrApp_1" ] ∀ (s : String), fost1 (s ++ "a") = 0 ===> True

axiom fost2 : String → String
@[blaster]
axiom fost2_rhs : ∀ (s : String), fost2 s = s ++ "a"

#testOptimize [ "ExtFoldStrApp_2" ] ∀ (s : String), fost2 s = s ++ "a" ===> True
#testOptimize [ "ExtFoldStrApp_3" ] fost2 "b" = "ba" ===> True

/-! `GetElem?.getElem?` on `List`. -/
axiom fog1 : Option Nat → Nat
@[blaster]
axiom fog1_lhs : ∀ (l : List Nat) (i : Nat), fog1 l[i]? = i

#testOptimize [ "ExtFoldGetElem_1" ] ∀ (l : List Nat) (i : Nat), fog1 l[i]? = i ===> True

axiom fog2 : List Nat → Nat → Option Nat
@[blaster]
axiom fog2_rhs : ∀ (l : List Nat) (i : Nat), fog2 l i = l[i]?

#testOptimize [ "ExtFoldGetElem_2" ] ∀ (l : List Nat) (i : Nat), fog2 l i = l[i]? ===> True
#testOptimize [ "ExtFoldGetElem_3" ] ∀ (a : Nat) (l : List Nat), fog2 (a :: l) 0 = some a ===> True
#testOptimize [ "ExtFoldGetElem_4" ] ∀ (i : Nat), fog2 [] i = none ===> True

axiom fog3 : List Nat → Nat → Nat
@[blaster]
axiom fog3_prem : ∀ (l : List Nat) (i : Nat), l[i]? = none → fog3 l i = 0

#testOptimize [ "ExtFoldGetElem_5" ] ∀ (l : List Nat) (i : Nat), l[i]? = none → fog3 l i = 0 ===> True

/-! `Ne` as an argument and in an `Iff` rhs (premises and conclusions with `≠` are covered above). -/
axiom fone1 : Prop → Nat
@[blaster]
axiom fone1_lhs : ∀ (n : Nat), fone1 (n ≠ 0) = n

#testOptimize [ "ExtFoldNe_1" ] ∀ (n : Nat), fone1 (n ≠ 0) = n ===> True
#testOptimize [ "ExtFoldNe_2" ] ∀ (n : Nat), fone1 (¬ (n = 0)) = n ===> True
#testOptimize [ "ExtFoldNe_3" ] ∀ (n : Nat), fone1 (0 < n) = n ===> True

axiom fone2 : Nat → Prop
@[blaster]
axiom fone2_iff : ∀ (n : Nat), fone2 n ↔ n ≠ 0

#testOptimize [ "ExtFoldNe_4" ] ∀ (n : Nat), fone2 n ↔ 0 < n ===> True
#testOptimize [ "ExtFoldNe_5" ] ∀ (n : Nat), fone2 (n + 1) ===> True

axiom fone3 : Int → Prop
@[blaster]
axiom fone3_iff : ∀ (x : Int), fone3 x ↔ x ≠ 0

#testOptimize [ "ExtFoldNe_6" ] ∀ (x : Int), fone3 x ↔ ¬ (0 = x) ===> True

/-! Rules are tried before the arguments of the application are optimized and, without `restart`, the
    rewritten term is not optimized again: a literal argument reused in the rhs would stay un-normalized
    (`Nat.sub (OfNat.ofNat Nat 5 _) 1`, `0 < HAdd.hAdd … n 1`). With `restart := true` the rewritten term
    is normalized (`fonr1 5 = 4` and `fonr2 (n + 1)` reduce to `True`). -/
axiom fonr1 : Nat → Nat
@[blaster]
axiom fonr1_rhs : ∀ (n : Nat), fonr1 n = n - 1

#testOptimize [ "ExtFoldRestart_1" ] ∀ (n : Nat), fonr1 n = n - 1 ===> True
#testOptimize [ "ExtFoldRestart_2" ] fonr1 5 = 4 ===> True

axiom fonr2 : Nat → Prop
@[blaster]
axiom fonr2_iff : ∀ (n : Nat), fonr2 n ↔ n ≠ 0

#testOptimize [ "ExtFoldRestart_3" ] ∀ (n : Nat), fonr2 n ↔ 0 < n ===> True
#testOptimize [ "ExtFoldRestart_4" ] ∀ (n : Nat), fonr2 (n + 1) ===> True

/-! `HAdd.hAdd` on `UInt8`: the goal unfolds `UInt8.add` down to `UInt8.ofBitVec (BitVec.ofFin 8 ⟨_, _⟩)`
    whereas the rule stops at `UInt8.add x (UInt8.ofNat 1)` in normalize-only mode.
    TODO: to be handled (and re-enabled) together with the opacification of `BitVec.ofNat`. -/
axiom fou1 : UInt8 → UInt8
@[blaster]
axiom fou1_lhs : ∀ (x : UInt8), fou1 (x + 1) = x

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtFoldUInt8Add_1" ] ∀ (x : UInt8), fou1 (x + 1) = x ===> True

axiom fou2 : UInt8 → UInt8
@[blaster]
axiom fou2_rhs : ∀ (x : UInt8), fou2 x = x + 1

-- TODO: to be handled when `BitVec.ofNat` is opacified (currently no rewriting is performed)
-- #testOptimize [ "ExtFoldUInt8Add_2" ] ∀ (x : UInt8), fou2 x = x + 1 ===> True

end Test.ExtensionFoldableMisc
