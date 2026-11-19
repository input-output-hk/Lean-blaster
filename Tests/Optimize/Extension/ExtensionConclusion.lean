import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionConclusion

/-! ## Conclusions of generated optimization functions: predicates, `≠` and `↔` -/

axiom g : Nat → Nat

/-! Predicates: `p x` handled as `p x = True`, `¬ q x` handled as `q x = False`. -/

axiom p : Nat → Prop
axiom q : Nat → Prop

@[blaster (noRestart := true)]
axiom p_g : ∀ (n : Nat), p (g n)

@[blaster]
axiom not_q_g : ∀ (n : Nat), ¬ q (g n)

#testOptimize [ "ExtPredTrue_1" ] ∀ (n : Nat), p (g n) ===> True
#testOptimize [ "ExtPredTrue_2" ] ∀ (n : Nat), p n → p (g n) ===> True
#testOptimize [ "ExtPredFalse_1" ] ∀ (n : Nat), q (g n) → p n ===> True
#testOptimize [ "ExtPredFalse_2" ] ∀ (n : Nat), ¬ q (g n) ===> True

/-! `≠` conclusion: `gn n ≠ 0` is unfolded to `¬ (gn n = 0)` and normalized (`0 < gn n` for `Nat`,
`¬ (0 = gz n)` for `Int`), then handled as a predicate.
The `ExtPredNeSwap_*` cases write the goal as `gn n = N`: the operands of commutative operators are
reordered before the registered rules are looked up, so the rule fires on `N = gn n` as well. -/

axiom gn : Nat → Nat
axiom gz : Int → Int
axiom pz : Int → Prop

@[blaster (noRestart := true)]
axiom gn_ne_zero : ∀ (n : Nat), gn n ≠ 0

@[blaster (noRestart := true)]
axiom gn_ne_five : ∀ (n : Nat), gn n ≠ 5

@[blaster (noRestart := true)]
axiom gz_ne_zero : ∀ (n : Int), gz n ≠ 0

@[blaster (noRestart := true)]
axiom gz_ne_five : ∀ (n : Int), gz n ≠ 5

#testOptimize [ "ExtPredNe_1" ] ∀ (n : Nat), gn n ≠ 0 ===> True
#testOptimize [ "ExtPredNe_2" ] ∀ (n : Nat), ¬ (gn n = 0) ===> True
#testOptimize [ "ExtPredNe_3" ] ∀ (n : Nat), 0 < gn n ===> True
#testOptimize [ "ExtPredNe_4" ] ∀ (n : Nat), 0 < gn n → p n ===> ∀ (n : Nat), p n
#testOptimize [ "ExtPredNe_5" ] ∀ (n : Nat), ¬ (5 = gn n) ===> True
#testOptimize [ "ExtPredNe_6" ] ∀ (n : Nat), 5 = gn n → p n ===> True
#testOptimize [ "ExtPredNe_7" ] ∀ (n : Int), ¬ (0 = gz n) ===> True
#testOptimize [ "ExtPredNe_8" ] ∀ (n : Int), 0 = gz n → pz n ===> True
#testOptimize [ "ExtPredNe_9" ] ∀ (n : Int), ¬ (5 = gz n) ===> True
#testOptimize [ "ExtPredNe_10" ] ∀ (n : Int), 5 = gz n → pz n ===> True
-- goal written with the operands in the non-normalized order (reordered before the lookup)
#testOptimize [ "ExtPredNeSwap_1" ] ∀ (n : Nat), gn n ≠ 5 ===> True
#testOptimize [ "ExtPredNeSwap_2" ] ∀ (n : Nat), ¬ (gn n = 5) ===> True
#testOptimize [ "ExtPredNeSwap_3" ] ∀ (n : Nat), gn n = 5 → p n ===> True
#testOptimize [ "ExtPredNeSwap_4" ] ∀ (n : Int), gz n ≠ 0 ===> True
#testOptimize [ "ExtPredNeSwap_5" ] ∀ (n : Int), ¬ (gz n = 0) ===> True
#testOptimize [ "ExtPredNeSwap_6" ] ∀ (n : Int), gz n = 0 → pz n ===> True
#testOptimize [ "ExtPredNeSwap_7" ] ∀ (n : Int), gz n ≠ 5 ===> True
#testOptimize [ "ExtPredNeSwap_8" ] ∀ (n : Int), ¬ (gz n = 5) ===> True
#testOptimize [ "ExtPredNeSwap_9" ] ∀ (n : Int), gz n = 5 → pz n ===> True

/-! Iff conclusion. -/

axiom r : Nat → Prop

@[blaster (noRestart := true)]
axiom r_g_iff : ∀ (n : Nat), r (g n) ↔ p n

#testOptimize [ "ExtIff_1" ] ∀ (n : Nat), r (g n) ===> ∀ (n : Nat), p n

end Test.ExtensionConclusion
