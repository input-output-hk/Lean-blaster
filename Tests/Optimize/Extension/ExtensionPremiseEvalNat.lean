import Lean
import Tests.Utils
import Blaster.Optimize.Env

open Lean Meta Blaster.Optimize

namespace Test.ExtensionPremiseEvalNat

/-! ## Premises evaluated at application time

A premise is rebuilt (`optimizeAppExt`, i.e. `optimizeAppAux` iterated until no restart is pending)
with the matched arguments before being checked with `isTruePremise`: when the instantiated premise is reduced to `True` the rule applies without any
hypothesis, when it is reduced to `False` the rule must not be triggered, otherwise the premise is
looked up in the hypothesis map. The cases below cover literals, structurally decided premises
(`n ≤ n`, `n < Nat.add 1 n`, `n = n`, `Nat.add 1 n ≠ n`), premises reduced to a literal
(`Nat.mul n 0`), and premises established by (derived) hypotheses, for both `Nat` and `Int`.
`≠` premises are unfolded to `¬ (_ = _)` by `normalizeTheorem` and behave like them.
NOTE: unused binders are removed by the optimizer when the rule applies.
-/

axiom c1 : Nat → Prop

/-! `Nat`: `0 < a`. -/
axiom k7 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k7_pos : ∀ (a z : Nat), 0 < a → k7 a z = z

#testOptimize [ "ExtPosNat_1" ] (norm-result: 1) ∀ (z w : Nat), k7 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtPosNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k7 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtPosNat_3" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k7 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
#testOptimize [ "ExtPosNat_4" ] (norm-result: 1) ∀ (n z w : Nat), 5 ≤ n → k7 n z = w ===> ∀ (n z w : Nat), ¬ (n < 5) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtPosNat_5" ] (norm-result: 1) ∀ (z w : Nat), k7 0 z = w ===> ∀ (z w : Nat), w = k7 0 z
#testOptimize [ "ExtPosNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k7 (n * 0) z = w ===> ∀ (z w : Nat), w = k7 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtPosNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k7 n z = w ===> ∀ (n z w : Nat), w = k7 n z

/-! `Nat`: `¬ (a = 0)` (normalized to `0 < a`). -/
axiom k8 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k8_nz : ∀ (a z : Nat), ¬ (a = 0) → k8 a z = z

#testOptimize [ "ExtNzNat_1" ] (norm-result: 1) ∀ (z w : Nat), k8 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNzNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k8 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNzNat_3" ] (norm-result: 1) ∀ (n z w : Nat), n ≠ 0 → k8 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNzNat_4" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k8 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNzNat_5" ] (norm-result: 1) ∀ (z w : Nat), k8 0 z = w ===> ∀ (z w : Nat), w = k8 0 z
#testOptimize [ "ExtNzNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k8 (n * 0) z = w ===> ∀ (z w : Nat), w = k8 0 z

/-! `Nat`: `a ≠ 0` (unfolded to `¬ (a = 0)`, then normalized to `0 < a`). -/
axiom k16 : Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k16_ne : ∀ (a z : Nat), a ≠ 0 → k16 a z = z

#testOptimize [ "ExtNeNat_1" ] (norm-result: 1) ∀ (z w : Nat), k16 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k16 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat_3" ] (norm-result: 1) ∀ (n z w : Nat), n ≠ 0 → k16 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNeNat_4" ] (norm-result: 1) ∀ (n z w : Nat), ¬ (n = 0) → k16 n z = w ===> ∀ (n z w : Nat), 0 < n → z = w
#testOptimize [ "ExtNeNat_5" ] (norm-result: 1) ∀ (n z w : Nat), 5 < n → k16 n z = w ===> ∀ (n z w : Nat), 5 < n → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeNat_6" ] (norm-result: 1) ∀ (z w : Nat), k16 0 z = w ===> ∀ (z w : Nat), w = k16 0 z
#testOptimize [ "ExtNeNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k16 (n * 0) z = w ===> ∀ (z w : Nat), w = k16 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNeNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k16 n z = w ===> ∀ (n z w : Nat), w = k16 n z

/-! `Nat`: `a ≤ b` (normalized to `¬ (b < a)`). -/
axiom k9 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k9_le : ∀ (a b z : Nat), a ≤ b → k9 a b z = z

#testOptimize [ "ExtLeNat_1" ] (norm-result: 1) ∀ (z w : Nat), k9 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_2" ] (norm-result: 1) ∀ (z w : Nat), k9 5 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k9 n n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_4" ] (norm-result: 1) ∀ (n z w : Nat), k9 0 n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_5" ] (norm-result: 1) ∀ (n z w : Nat), k9 n (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLeNat_6" ] (norm-result: 1) ∀ (n m z w : Nat), n ≤ m → k9 n m z = w ===> ∀ (n m z w : Nat), ¬ (m < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLeNat_7" ] (norm-result: 1) ∀ (z w : Nat), k9 5 3 z = w ===> ∀ (z w : Nat), w = k9 5 3 z
#testOptimize [ "ExtLeNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k9 (n + 1) n z = w ===> ∀ (n z w : Nat), w = k9 (Nat.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLeNat_9" ] (norm-result: 1) ∀ (n m z w : Nat), k9 n m z = w ===> ∀ (n m z w : Nat), w = k9 n m z

/-! `Nat`: `a < b`. -/
axiom k10 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k10_lt : ∀ (a b z : Nat), a < b → k10 a b z = z

#testOptimize [ "ExtLtNat_1" ] (norm-result: 1) ∀ (z w : Nat), k10 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k10 n (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k10 0 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtLtNat_4" ] (norm-result: 1) ∀ (n m z w : Nat), n < m → k10 n m z = w ===> ∀ (n m z w : Nat), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLtNat_5" ] (norm-result: 1) ∀ (z w : Nat), k10 5 5 z = w ===> ∀ (z w : Nat), w = k10 5 5 z
#testOptimize [ "ExtLtNat_6" ] (norm-result: 1) ∀ (z w : Nat), k10 5 3 z = w ===> ∀ (z w : Nat), w = k10 5 3 z
#testOptimize [ "ExtLtNat_7" ] (norm-result: 1) ∀ (n z w : Nat), k10 n n z = w ===> ∀ (n z w : Nat), w = k10 n n z
#testOptimize [ "ExtLtNat_8" ] (norm-result: 1) ∀ (n z w : Nat), k10 n 0 z = w ===> ∀ (n z w : Nat), w = k10 n 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtLtNat_9" ] (norm-result: 1) ∀ (n m z w : Nat), k10 n m z = w ===> ∀ (n m z w : Nat), w = k10 n m z

/-! `Nat`: `a = b`. -/
axiom k11 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k11_eq : ∀ (a b z : Nat), a = b → k11 a b z = z

#testOptimize [ "ExtEqNat_1" ] (norm-result: 1) ∀ (z w : Nat), k11 5 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k11 n n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k11 (n + 1) (1 + n) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtEqNat_4" ] (norm-result: 1) ∀ (n m z w : Nat), n = m → k11 n m z = w ===> ∀ (n m z w : Nat), n = m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtEqNat_5" ] (norm-result: 1) ∀ (z w : Nat), k11 5 6 z = w ===> ∀ (z w : Nat), w = k11 5 6 z
#testOptimize [ "ExtEqNat_6" ] (norm-result: 1) ∀ (n z w : Nat), k11 (n + 1) 0 z = w ===> ∀ (n z w : Nat), w = k11 (Nat.add 1 n) 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtEqNat_7" ] (norm-result: 1) ∀ (n m z w : Nat), k11 n m z = w ===> ∀ (n m z w : Nat), w = k11 n m z

/-! `Nat`: `a ≠ b` (unfolded to `¬ (a = b)`). -/
axiom k17 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k17_ne : ∀ (a b z : Nat), a ≠ b → k17 a b z = z

#testOptimize [ "ExtNeNat2_1" ] (norm-result: 1) ∀ (z w : Nat), k17 3 5 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_2" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) 0 z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_3" ] (norm-result: 1) ∀ (n z w : Nat), k17 0 (n + 1) z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_4" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) n z = w ===> ∀ (z w : Nat), z = w
#testOptimize [ "ExtNeNat2_5" ] (norm-result: 1) ∀ (n m z w : Nat), n ≠ m → k17 n m z = w ===> ∀ (n m z w : Nat), ¬ (n = m) → z = w
-- `¬ (n = m)` is derived from `n < m`
#testOptimize [ "ExtNeNat2_6" ] (norm-result: 1) ∀ (n m z w : Nat), n < m → k17 n m z = w ===> ∀ (n m z w : Nat), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeNat2_7" ] (norm-result: 1) ∀ (z w : Nat), k17 5 5 z = w ===> ∀ (z w : Nat), w = k17 5 5 z
#testOptimize [ "ExtNeNat2_8" ] (norm-result: 1) ∀ (n z w : Nat), k17 n n z = w ===> ∀ (n z w : Nat), w = k17 n n z
#testOptimize [ "ExtNeNat2_9" ] (norm-result: 1) ∀ (n z w : Nat), k17 (n + 1) (1 + n) z = w ===> ∀ (n z w : Nat), w = k17 (Nat.add 1 n) (Nat.add 1 n) z
-- premise not established: no rewriting
#testOptimize [ "ExtNeNat2_10" ] (norm-result: 1) ∀ (n m z w : Nat), k17 n m z = w ===> ∀ (n m z w : Nat), w = k17 n m z

/-! `Nat`: conjunction / disjunction with an evaluated conjunct / disjunct. -/
axiom k12 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k12_conj : ∀ (a n z : Nat), 0 < a ∧ c1 n → k12 a n z = z

#testOptimize [ "ExtConjNat_1" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k12 5 n z = w ===> ∀ (n z w : Nat), c1 n → z = w
-- `True ∧ <missing>`: no rewriting
#testOptimize [ "ExtConjNat_2" ] (norm-result: 1) ∀ (n z w : Nat), k12 5 n z = w ===> ∀ (n z w : Nat), w = k12 5 n z
-- `False ∧ <hypothesis>`: no rewriting
#testOptimize [ "ExtConjNat_3" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k12 0 n z = w ===> ∀ (n z w : Nat), c1 n → w = k12 0 n z

axiom k13 : Nat → Nat → Nat → Nat

@[blaster (noRestart := true)]
axiom k13_disj : ∀ (a n z : Nat), 0 < a ∨ c1 n → k13 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjNat_1" ] (norm-result: 1) ∀ (n z w : Nat), k13 5 n z = w ===> ∀ (z w : Nat), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjNat_2" ] (norm-result: 1) ∀ (n z w : Nat), c1 n → k13 0 n z = w ===> ∀ (n z w : Nat), c1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjNat_3" ] (norm-result: 1) ∀ (n z w : Nat), k13 0 n z = w ===> ∀ (n z w : Nat), w = k13 0 n z

end Test.ExtensionPremiseEvalNat
