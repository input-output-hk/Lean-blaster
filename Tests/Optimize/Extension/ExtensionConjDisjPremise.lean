import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionConjDisjPremise

/-! ## Conjunction and disjunction premises

Each premise is compiled to a `TranslateEnvT Bool` check: atoms are looked up in the hypothesis
map, `∧` becomes `<&&>` and `∨` becomes `<||>`. Note that a disjunction is not looked up as a whole
in the hypothesis map: each disjunct is checked separately.
-/

axiom c1 : Nat → Prop
axiom c2 : Nat → Prop
axiom c3 : Nat → Prop
axiom c4 : Nat → Prop

/-! Conjunction. -/
axiom k1 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k1_conj : ∀ (n m : Nat), c1 n ∧ c2 m → k1 n m = n

#testOptimize [ "ExtConj_1" ] ∀ (n m z : Nat), c1 n → c2 m → k1 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → n = z
-- a conjunction hypothesis is split in the hypothesis map
#testOptimize [ "ExtConj_2" ] ∀ (n m z : Nat), c1 n ∧ c2 m → k1 n m = z ===> ∀ (n m z : Nat), c1 n ∧ c2 m → n = z
#testOptimize [ "ExtConj_3" ] ∀ (n m z : Nat), c1 n → k1 n m = z ===> ∀ (n m z : Nat), c1 n → z = k1 n m
#testOptimize [ "ExtConj_4" ] ∀ (n m z : Nat), c2 m → k1 n m = z ===> ∀ (n m z : Nat), c2 m → z = k1 n m

/-! Disjunction. -/
axiom k2 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k2_disj : ∀ (n m : Nat), c1 n ∨ c2 m → k2 n m = m

#testOptimize [ "ExtDisj_1" ] ∀ (n m z : Nat), c1 n → k2 n m = z ===> ∀ (n m z : Nat), c1 n → m = z
-- NOTE: the unused binder `n` is removed by the optimizer
#testOptimize [ "ExtDisj_2" ] ∀ (n m z : Nat), c2 m → k2 n m = z ===> ∀ (m z : Nat), c2 m → m = z
#testOptimize [ "ExtDisj_3" ] ∀ (n m z : Nat), c1 n → c2 m → k2 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → m = z
#testOptimize [ "ExtDisj_4" ] ∀ (n m z : Nat), c3 n → k2 n m = z ===> ∀ (n m z : Nat), c3 n → z = k2 n m
-- the disjunction as a whole is not looked up in the hypothesis map
#testOptimize [ "ExtDisj_5" ] ∀ (n m z : Nat), c1 n ∨ c2 m → k2 n m = z ===> ∀ (n m z : Nat), c1 n ∨ c2 m → z = k2 n m

/-! Disjunction of conjunctions. -/
axiom k3 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k3_disj_conj : ∀ (n m : Nat), (c1 n ∧ c2 m) ∨ (c3 n ∧ c4 m) → k3 n m = n

#testOptimize [ "ExtDisjConj_1" ] ∀ (n m z : Nat), c1 n → c2 m → k3 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → n = z
#testOptimize [ "ExtDisjConj_2" ] ∀ (n m z : Nat), c3 n → c4 m → k3 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → n = z
#testOptimize [ "ExtDisjConj_3" ] ∀ (n m z : Nat), c1 n → c3 n → k3 n m = z ===> ∀ (n m z : Nat), c1 n → c3 n → z = k3 n m
#testOptimize [ "ExtDisjConj_4" ] ∀ (n m z : Nat), c2 m → c4 m → k3 n m = z ===> ∀ (n m z : Nat), c2 m → c4 m → z = k3 n m

/-! Conjunction of disjunctions. -/
axiom k4 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k4_conj_disj : ∀ (n m : Nat), (c1 n ∨ c2 m) ∧ (c3 n ∨ c4 m) → k4 n m = m

#testOptimize [ "ExtConjDisj_1" ] ∀ (n m z : Nat), c1 n → c3 n → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c3 n → m = z
#testOptimize [ "ExtConjDisj_2" ] ∀ (n m z : Nat), c2 m → c3 n → k4 n m = z ===> ∀ (n m z : Nat), c2 m → c3 n → m = z
#testOptimize [ "ExtConjDisj_3" ] ∀ (n m z : Nat), c1 n → c4 m → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c4 m → m = z
#testOptimize [ "ExtConjDisj_4" ] ∀ (n m z : Nat), c1 n → c2 m → k4 n m = z ===> ∀ (n m z : Nat), c1 n → c2 m → z = k4 n m
#testOptimize [ "ExtConjDisj_5" ] ∀ (n m z : Nat), c3 n → c4 m → k4 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → z = k4 n m

/-! Deeper nesting. -/
axiom k5 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k5_nested : ∀ (n m : Nat), c1 n ∨ (c2 m ∧ (c3 n ∨ c4 m)) → k5 n m = n

-- NOTE: the unused binder `m` is removed by the optimizer
#testOptimize [ "ExtNested_1" ] ∀ (n m z : Nat), c1 n → k5 n m = z ===> ∀ (n z : Nat), c1 n → n = z
#testOptimize [ "ExtNested_2" ] ∀ (n m z : Nat), c2 m → c4 m → k5 n m = z ===> ∀ (n m z : Nat), c2 m → c4 m → n = z
#testOptimize [ "ExtNested_3" ] ∀ (n m z : Nat), c2 m → c3 n → k5 n m = z ===> ∀ (n m z : Nat), c2 m → c3 n → n = z
#testOptimize [ "ExtNested_4" ] ∀ (n m z : Nat), c2 m → k5 n m = z ===> ∀ (n m z : Nat), c2 m → z = k5 n m
#testOptimize [ "ExtNested_5" ] ∀ (n m z : Nat), c3 n → c4 m → k5 n m = z ===> ∀ (n m z : Nat), c3 n → c4 m → z = k5 n m

/-! Specialized atomic checks (`0 < n`, `¬ 0 = m`) inside a disjunction. -/
axiom k6 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k6_lit : ∀ (n m : Nat), 0 < n ∨ ¬ m = 0 → k6 n m = Nat.add n m

#testOptimize [ "ExtDisjLit_1" ] (norm-result: 1) ∀ (n m z : Nat), 0 < n → k6 n m = z ===> ∀ (n m z : Nat), 0 < n → z = Nat.add n m
#testOptimize [ "ExtDisjLit_2" ] (norm-result: 1) ∀ (n m z : Nat), ¬ m = 0 → k6 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
-- `¬ 0 = m` is derived from `0 < m` by `nonZeroNatInHyps`
#testOptimize [ "ExtDisjLit_3" ] (norm-result: 1) ∀ (n m z : Nat), 0 < m → k6 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjLit_4" ] ∀ (n m z : Nat), k6 n m = z ===> ∀ (n m z : Nat), z = k6 n m

/-! `≠` atoms inside a disjunction / conjunction (`m ≠ 0` is unfolded then normalized to `0 < m`). -/
axiom k14 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k14_disj_ne : ∀ (n m : Nat), 0 < n ∨ m ≠ 0 → k14 n m = Nat.add n m

#testOptimize [ "ExtDisjNe_1" ] (norm-result: 1) ∀ (n m z : Nat), m ≠ 0 → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjNe_2" ] (norm-result: 1) ∀ (n m z : Nat), ¬ (m = 0) → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
#testOptimize [ "ExtDisjNe_3" ] (norm-result: 1) ∀ (n m z : Nat), 0 < m → k14 n m = z ===> ∀ (n m z : Nat), 0 < m → z = Nat.add n m
-- `<missing> ∨ True`
#testOptimize [ "ExtDisjNe_4" ] (norm-result: 1) ∀ (n z : Nat), k14 n 5 = z ===> ∀ (n z : Nat), z = Nat.add 5 n
-- `False ∨ False`: no rewriting
#testOptimize [ "ExtDisjNe_5" ] (norm-result: 1) ∀ (z : Nat), k14 0 0 = z ===> ∀ (z : Nat), z = k14 0 0
#testOptimize [ "ExtDisjNe_6" ] ∀ (n m z : Nat), k14 n m = z ===> ∀ (n m z : Nat), z = k14 n m

axiom k15 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k15_conj_ne : ∀ (n m : Nat), c1 n ∧ m ≠ 0 → k15 n m = n

#testOptimize [ "ExtConjNe_1" ] (norm-result: 1) ∀ (n m z : Nat), c1 n → m ≠ 0 → k15 n m = z ===> ∀ (n m z : Nat), c1 n → 0 < m → n = z
#testOptimize [ "ExtConjNe_2" ] (norm-result: 1) ∀ (n m z : Nat), c1 n → 0 < m → k15 n m = z ===> ∀ (n m z : Nat), c1 n → 0 < m → n = z
-- `<hypothesis> ∧ True`
#testOptimize [ "ExtConjNe_3" ] (norm-result: 1) ∀ (n z : Nat), c1 n → k15 n 5 = z ===> ∀ (n z : Nat), c1 n → n = z
-- `<hypothesis> ∧ False`: no rewriting
#testOptimize [ "ExtConjNe_4" ] (norm-result: 1) ∀ (n z : Nat), c1 n → k15 n 0 = z ===> ∀ (n z : Nat), c1 n → z = k15 n 0
-- `<missing> ∧ True`: no rewriting
#testOptimize [ "ExtConjNe_5" ] (norm-result: 1) ∀ (n z : Nat), k15 n 5 = z ===> ∀ (n z : Nat), z = k15 n 5

end Test.ExtensionConjDisjPremise
