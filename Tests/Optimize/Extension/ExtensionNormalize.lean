import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionNormalize

/-! ## Normalization of the theorem statement

The statement is normalized (see `normalizeExpr`) before the optimization function is generated:
`OfNat` literals, `let`, beta-redexes, `True`/`False` in premises and conclusions, double negation,
operand ordering of commutative operators, ... are all taken care of. Function unfolding is not
applied, so operators must be written in their normalized form (`Nat.add`, not `+`).
-/

axiom c1 : Nat → Prop
axiom c2 : Nat → Prop

/-! `Nat.add 0 n` and `Nat.add n 0` are simplified on both sides. -/
axiom nz : Nat → Nat

@[blaster]
axiom nz_zero_add : ∀ (n : Nat), nz (Nat.add 0 n) = Nat.add n 0

#testOptimize [ "ExtNormZeroAdd_1" ] ∀ (n m : Nat), nz n = m ===> ∀ (n m : Nat), n = m

/-! Beta-redex in the lhs. -/
axiom nb : Nat → Nat

@[blaster (noRestart := true)]
axiom nb_beta : ∀ (n : Nat), (fun x => nb x) (Nat.add 1 n) = n

#testOptimize [ "ExtNormBeta_1" ] ∀ (n m : Nat), nb (1 + n) = m ===> ∀ (n m : Nat), n = m
#testOptimize [ "ExtNormBeta_2" ] (norm-result: 1) ∀ (n m : Nat), nb (2 + n) = m ===> ∀ (n m : Nat), m = nb (Nat.add 2 n)

/-! `let` in the lhs. -/
axiom nl : Nat → Nat

@[blaster (noRestart := true)]
axiom nl_let : ∀ (n : Nat), (let k := Nat.add 2 n; nl k) = n

#testOptimize [ "ExtNormLet_1" ] ∀ (n m : Nat), nl (2 + n) = m ===> ∀ (n m : Nat), n = m

/-! `True` premises and `True` conjuncts are removed; `Nat.mul 1 n` is simplified. -/
axiom nt : Nat → Nat

@[blaster]
axiom nt_true : ∀ (n : Nat), True → (True ∧ c1 n) → nt (Nat.mul 1 n) = n

#testOptimize [ "ExtNormTrue_1" ] ∀ (n m : Nat), c1 n → nt n = m ===> ∀ (n m : Nat), c1 n → n = m
#testOptimize [ "ExtNormTrue_2" ] ∀ (n m : Nat), nt n = m ===> ∀ (n m : Nat), m = nt n

/-! `False` disjuncts are removed; `if` on a constant condition is reduced on both sides. -/
axiom nf : Nat → Nat

@[blaster]
axiom nf_false : ∀ (n : Nat), c2 n ∨ False → nf (if true then n else 0) = (if 1 = 1 then n else 0)

#testOptimize [ "ExtNormFalse_1" ] ∀ (n m : Nat), c2 n → nf n = m ===> ∀ (n m : Nat), c2 n → n = m
#testOptimize [ "ExtNormFalse_2" ] ∀ (n m : Nat), nf n = m ===> ∀ (n m : Nat), m = nf n

/-! Double negation in a premise; operands of `Nat.add` are reordered (`Nat.add n 1` ↦ `Nat.add 1 n`). -/
axiom nn : Nat → Nat

@[blaster (noRestart := true)]
axiom nn_notnot : ∀ (n : Nat), ¬ ¬ c2 n → nn (Nat.add n 1) = n

#testOptimize [ "ExtNormNotNot_1" ] ∀ (n m : Nat), c2 n → nn (n + 1) = m ===> ∀ (n m : Nat), c2 n → n = m
#testOptimize [ "ExtNormNotNot_2" ] (norm-result: 1) ∀ (n m : Nat), nn (n + 1) = m ===> ∀ (n m : Nat), m = nn (Nat.add 1 n)

/-! A statement that normalizes to `True` is handled natively: no optimization function is generated
    and an info message is logged by the attribute. -/
axiom ntriv : Nat → Nat

/-! `Eq`: the lhs and rhs are equal after normalization. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_triv` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster  (noRestart := true)]
axiom ntriv_triv : ∀ (n : Nat), ntriv (Nat.add 0 n) = ntriv n

#testOptimize [ "ExtNormTriv_1" ] ∀ (n m : Nat), ntriv (0 + n) = m ===> ∀ (n m : Nat), m = ntriv n

/-! `Eq`: reflexivity. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_eq_refl` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_eq_refl : ∀ (n : Nat), ntriv n = ntriv n

/-! `Iff`: both sides are equal after normalization. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_iff` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_iff : ∀ (n : Nat), c1 (Nat.add 0 n) ↔ c1 n

/-! Predicate: `c1 n ∨ True` normalizes to `True`. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_or_true` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_or_true : ∀ (n : Nat), c1 n ∨ True

/-! Predicate: `0 < Nat.add 1 n` is decided natively. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_zero_lt` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_zero_lt : ∀ (n : Nat), 0 < Nat.add 1 n

/-! Predicate: `n ≤ n` is decided natively. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_le_refl` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_le_refl : ∀ (n : Nat), n ≤ n

/-! Negation: `¬ (Nat.add 1 n = 0)` is decided natively. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_not_eq` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_not_eq : ∀ (n : Nat), ¬ (Nat.add 1 n = 0)

/-! Negation: `≠` is unfolded, `Nat.add 1 n ≠ 0` is decided natively as well. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_ne` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_ne : ∀ (n : Nat), Nat.add 1 n ≠ 0

/-! Negation: `¬ False` normalizes to `True` (the premise is dropped as well). -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_not_false` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_not_false : ∀ (n : Nat), c1 n → ¬ False

/-! Implication: the premise entails the conclusion. -/
/--
info: @[blaster]: `Test.ExtensionNormalize.ntriv_imp_self` is already handled natively by the Blaster, no optimization function generated
-/
#guard_msgs in
@[blaster]
axiom ntriv_imp_self : ∀ (n : Nat), c1 n → c1 n

/-! A statement that normalizes to `False` is rejected.
    NOTE: the axiom is nevertheless added to the environment; it is not used by any other test. -/
/-- error: blaster: theorem Test.ExtensionNormalize.ntriv_unsound is unsound -/
#guard_msgs in
@[blaster]
axiom ntriv_unsound : ∀ (n : Nat), ¬ (ntriv n = ntriv n)

end Test.ExtensionNormalize
