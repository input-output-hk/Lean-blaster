import Lean
import Tests.Utils
import Blaster.Optimize.Env
import Tests.Optimize.Extension.ExtensionBasic

open Lean Meta Blaster.Optimize

namespace Test.ExtensionPremiseEvalInt

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

axiom d1 : Int → Prop

/-! `Int`: `0 < a`. -/
axiom j7 : Int → Int → Int

@[blaster (noRestart := true)]
axiom j7_pos : ∀ (a z : Int), 0 < a → j7 a z = z

#testOptimize [ "ExtPosInt_1" ] (norm-result: 1) ∀ (z w : Int), j7 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtPosInt_2" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j7 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtPosInt_3" ] (norm-result: 1) ∀ (n z w : Int), 5 ≤ n → j7 n z = w ===> ∀ (n z w : Int), ¬ (n < 5) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtPosInt_4" ] (norm-result: 1) ∀ (z w : Int), j7 0 z = w ===> ∀ (z w : Int), w = j7 0 z
#testOptimize [ "ExtPosInt_5" ] (norm-result: 1) ∀ (z w : Int), j7 (-5) z = w ===> ∀ (z w : Int), w = j7 (Int.negSucc 4) z
#testOptimize [ "ExtPosInt_6" ] (norm-result: 1) ∀ (n z w : Int), j7 (n * 0) z = w ===> ∀ (z w : Int), w = j7 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtPosInt_7" ] (norm-result: 1) ∀ (n z w : Int), j7 n z = w ===> ∀ (n z w : Int), w = j7 n z
-- premise on an `Int.ofNat` argument: deciding it needs a restart pass, the generated check
-- re-optimizes the premise until no restart is pending
#testOptimize [ "ExtPosIntLift_1" ] ∀ (n : Nat), 0 < Int.ofNat (n + 1) ===> True
#testOptimize [ "ExtPosIntLift_2" ] (norm-result: 1) ∀ (n : Nat) (z w : Int), j7 (Int.ofNat (n + 1)) z = w ===> ∀ (z w : Int), z = w

/-! `Int`: `a < 0`. -/
axiom j14 : Int → Int → Int

@[blaster (noRestart := true)]
axiom j14_neg : ∀ (a z : Int), a < 0 → j14 a z = z

#testOptimize [ "ExtNegInt_1" ] (norm-result: 1) ∀ (z w : Int), j14 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNegInt_2" ] (norm-result: 1) ∀ (n z w : Int), n < -5 → j14 n z = w ===> ∀ (n z w : Int), n < Int.negSucc 4 → z = w
#testOptimize [ "ExtNegInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j14 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNegInt_4" ] (norm-result: 1) ∀ (z w : Int), j14 0 z = w ===> ∀ (z w : Int), w = j14 0 z
#testOptimize [ "ExtNegInt_5" ] (norm-result: 1) ∀ (z w : Int), j14 5 z = w ===> ∀ (z w : Int), w = j14 5 z
-- premise not established: no rewriting
#testOptimize [ "ExtNegInt_6" ] (norm-result: 1) ∀ (n z w : Int), j14 n z = w ===> ∀ (n z w : Int), w = j14 n z

/-! `Int`: `¬ (a = 0)` (normalized to `¬ (0 = a)`). -/
axiom j8 : Int → Int → Int

@[blaster (noRestart := true)]
axiom j8_nz : ∀ (a z : Int), ¬ (a = 0) → j8 a z = z

#testOptimize [ "ExtNzInt_1" ] (norm-result: 1) ∀ (z w : Int), j8 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNzInt_2" ] (norm-result: 1) ∀ (z w : Int), j8 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNzInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≠ 0 → j8 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNzInt_4" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j8 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtNzInt_5" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j8 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNzInt_6" ] (norm-result: 1) ∀ (z w : Int), j8 0 z = w ===> ∀ (z w : Int), w = j8 0 z
#testOptimize [ "ExtNzInt_7" ] (norm-result: 1) ∀ (n z w : Int), j8 (n * 0) z = w ===> ∀ (z w : Int), w = j8 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNzInt_8" ] (norm-result: 1) ∀ (n z w : Int), j8 n z = w ===> ∀ (n z w : Int), w = j8 n z

/-! `Int`: `a ≠ 0` (unfolded to `¬ (a = 0)`, then normalized to `¬ (0 = a)`). -/
axiom j15 : Int → Int → Int

@[blaster (noRestart := true)]
axiom j15_ne : ∀ (a z : Int), a ≠ 0 → j15 a z = z

#testOptimize [ "ExtNeInt_1" ] (norm-result: 1) ∀ (z w : Int), j15 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt_2" ] (norm-result: 1) ∀ (z w : Int), j15 (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt_3" ] (norm-result: 1) ∀ (n z w : Int), n ≠ 0 → j15 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNeInt_4" ] (norm-result: 1) ∀ (n z w : Int), ¬ (n = 0) → j15 n z = w ===> ∀ (n z w : Int), ¬ (0 = n) → z = w
#testOptimize [ "ExtNeInt_5" ] (norm-result: 1) ∀ (n z w : Int), 5 < n → j15 n z = w ===> ∀ (n z w : Int), 5 < n → z = w
#testOptimize [ "ExtNeInt_6" ] (norm-result: 1) ∀ (n z w : Int), n ≤ -5 → j15 n z = w ===> ∀ (n z w : Int), ¬ (Int.negSucc 4 < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeInt_7" ] (norm-result: 1) ∀ (z w : Int), j15 0 z = w ===> ∀ (z w : Int), w = j15 0 z
#testOptimize [ "ExtNeInt_8" ] (norm-result: 1) ∀ (n z w : Int), j15 (n * 0) z = w ===> ∀ (z w : Int), w = j15 0 z
-- premise not established: no rewriting
#testOptimize [ "ExtNeInt_9" ] (norm-result: 1) ∀ (n z w : Int), j15 n z = w ===> ∀ (n z w : Int), w = j15 n z

/-! `Int`: `a ≤ b` (normalized to `¬ (b < a)`). -/
axiom j9 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j9_le : ∀ (a b z : Int), a ≤ b → j9 a b z = z

#testOptimize [ "ExtLeInt_1" ] (norm-result: 1) ∀ (z w : Int), j9 3 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_2" ] (norm-result: 1) ∀ (z w : Int), j9 (-5) 3 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_3" ] (norm-result: 1) ∀ (z w : Int), j9 (-5) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_4" ] (norm-result: 1) ∀ (n z w : Int), j9 n n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_5" ] (norm-result: 1) ∀ (n z w : Int), j9 n (n + 1) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLeInt_6" ] (norm-result: 1) ∀ (n m z w : Int), n ≤ m → j9 n m z = w ===> ∀ (n m z w : Int), ¬ (m < n) → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLeInt_7" ] (norm-result: 1) ∀ (z w : Int), j9 3 (-5) z = w ===> ∀ (z w : Int), w = j9 3 (Int.negSucc 4) z
#testOptimize [ "ExtLeInt_8" ] (norm-result: 1) ∀ (z w : Int), j9 5 3 z = w ===> ∀ (z w : Int), w = j9 5 3 z
#testOptimize [ "ExtLeInt_9" ] (norm-result: 1) ∀ (n z w : Int), j9 (n + 1) n z = w ===> ∀ (n z w : Int), w = j9 (Int.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLeInt_10" ] (norm-result: 1) ∀ (n m z w : Int), j9 n m z = w ===> ∀ (n m z w : Int), w = j9 n m z

/-! `Int`: `a < b`. -/
axiom j10 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j10_lt : ∀ (a b z : Int), a < b → j10 a b z = z

#testOptimize [ "ExtLtInt_1" ] (norm-result: 1) ∀ (z w : Int), j10 (-3) 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_2" ] (norm-result: 1) ∀ (n z w : Int), j10 n (n + 1) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_3" ] (norm-result: 1) ∀ (n z w : Int), j10 (n - 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtLtInt_4" ] (norm-result: 1) ∀ (n m z w : Int), n < m → j10 n m z = w ===> ∀ (n m z w : Int), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtLtInt_5" ] (norm-result: 1) ∀ (z w : Int), j10 5 5 z = w ===> ∀ (z w : Int), w = j10 5 5 z
#testOptimize [ "ExtLtInt_6" ] (norm-result: 1) ∀ (z w : Int), j10 5 (-3) z = w ===> ∀ (z w : Int), w = j10 5 (Int.negSucc 2) z
#testOptimize [ "ExtLtInt_7" ] (norm-result: 1) ∀ (n z w : Int), j10 n n z = w ===> ∀ (n z w : Int), w = j10 n n z
#testOptimize [ "ExtLtInt_8" ] (norm-result: 1) ∀ (n z w : Int), j10 (n + 1) n z = w ===> ∀ (n z w : Int), w = j10 (Int.add 1 n) n z
-- premise not established: no rewriting
#testOptimize [ "ExtLtInt_9" ] (norm-result: 1) ∀ (n m z w : Int), j10 n m z = w ===> ∀ (n m z w : Int), w = j10 n m z

/-! `Int`: `a = b`. -/
axiom j11 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j11_eq : ∀ (a b z : Int), a = b → j11 a b z = z

#testOptimize [ "ExtEqInt_1" ] (norm-result: 1) ∀ (z w : Int), j11 (-5) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_2" ] (norm-result: 1) ∀ (n z w : Int), j11 n n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_3" ] (norm-result: 1) ∀ (n z w : Int), j11 (n + 1) (1 + n) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtEqInt_4" ] (norm-result: 1) ∀ (n m z w : Int), n = m → j11 n m z = w ===> ∀ (n m z w : Int), n = m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtEqInt_5" ] (norm-result: 1) ∀ (z w : Int), j11 5 (-5) z = w ===> ∀ (z w : Int), w = j11 5 (Int.negSucc 4) z
#testOptimize [ "ExtEqInt_6" ] (norm-result: 1) ∀ (z w : Int), j11 5 6 z = w ===> ∀ (z w : Int), w = j11 5 6 z
-- premise not established: no rewriting
#testOptimize [ "ExtEqInt_7" ] (norm-result: 1) ∀ (n m z w : Int), j11 n m z = w ===> ∀ (n m z w : Int), w = j11 n m z

/-! `Int`: `a ≠ b` (unfolded to `¬ (a = b)`). -/
axiom j16 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j16_ne : ∀ (a b z : Int), a ≠ b → j16 a b z = z

#testOptimize [ "ExtNeInt2_1" ] (norm-result: 1) ∀ (z w : Int), j16 (-3) 5 z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_2" ] (norm-result: 1) ∀ (z w : Int), j16 (-3) (-5) z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_3" ] (norm-result: 1) ∀ (n z w : Int), j16 (n + 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_4" ] (norm-result: 1) ∀ (n z w : Int), j16 (n - 1) n z = w ===> ∀ (z w : Int), z = w
#testOptimize [ "ExtNeInt2_5" ] (norm-result: 1) ∀ (n m z w : Int), n ≠ m → j16 n m z = w ===> ∀ (n m z w : Int), ¬ (n = m) → z = w
-- `¬ (n = m)` is derived from `n < m`
#testOptimize [ "ExtNeInt2_6" ] (norm-result: 1) ∀ (n m z w : Int), n < m → j16 n m z = w ===> ∀ (n m z w : Int), n < m → z = w
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtNeInt2_7" ] (norm-result: 1) ∀ (z w : Int), j16 5 5 z = w ===> ∀ (z w : Int), w = j16 5 5 z
#testOptimize [ "ExtNeInt2_8" ] (norm-result: 1) ∀ (z w : Int), j16 (-5) (-5) z = w ===> ∀ (z w : Int), w = j16 (Int.negSucc 4) (Int.negSucc 4) z
#testOptimize [ "ExtNeInt2_9" ] (norm-result: 1) ∀ (n z w : Int), j16 n n z = w ===> ∀ (n z w : Int), w = j16 n n z
-- premise not established: no rewriting
#testOptimize [ "ExtNeInt2_10" ] (norm-result: 1) ∀ (n m z w : Int), j16 n m z = w ===> ∀ (n m z w : Int), w = j16 n m z

/-! `Int`: conjunction / disjunction with an evaluated conjunct / disjunct. -/
axiom j12 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j12_conj : ∀ (a n z : Int), 0 < a ∧ d1 n → j12 a n z = z

#testOptimize [ "ExtConjInt_1" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j12 5 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `True ∧ <missing>`: no rewriting
#testOptimize [ "ExtConjInt_2" ] (norm-result: 1) ∀ (n z w : Int), j12 5 n z = w ===> ∀ (n z w : Int), w = j12 5 n z
-- `False ∧ <hypothesis>`: no rewriting
#testOptimize [ "ExtConjInt_3" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j12 (-5) n z = w ===> ∀ (n z w : Int), d1 n → w = j12 (Int.negSucc 4) n z

axiom j13 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j13_disj : ∀ (a n z : Int), 0 < a ∨ d1 n → j13 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjInt_1" ] (norm-result: 1) ∀ (n z w : Int), j13 5 n z = w ===> ∀ (z w : Int), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjInt_2" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j13 0 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjInt_3" ] (norm-result: 1) ∀ (n z w : Int), j13 (-5) n z = w ===> ∀ (n z w : Int), w = j13 (Int.negSucc 4) n z

/-! `Int`: `≠` disjunct evaluated at application time. -/
axiom j17 : Int → Int → Int → Int

@[blaster (noRestart := true)]
axiom j17_disj_ne : ∀ (a n z : Int), a ≠ 0 ∨ d1 n → j17 a n z = z

-- `True ∨ <missing>`
#testOptimize [ "ExtDisjNeInt_1" ] (norm-result: 1) ∀ (n z w : Int), j17 (-5) n z = w ===> ∀ (z w : Int), z = w
-- `False ∨ <hypothesis>`
#testOptimize [ "ExtDisjNeInt_2" ] (norm-result: 1) ∀ (n z w : Int), d1 n → j17 0 n z = w ===> ∀ (n z w : Int), d1 n → z = w
-- `False ∨ <missing>`: no rewriting
#testOptimize [ "ExtDisjNeInt_3" ] (norm-result: 1) ∀ (n z w : Int), j17 0 n z = w ===> ∀ (n z w : Int), w = j17 0 n z

/-! `tdiv_eq_ediv_of_gt_zero` (see `ExtensionBasic`) applied with a literal dividend. -/
#testOptimize [ "ExtTdivEdiv_3" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv 5 b = c ===> ∀ (b c : Int), c = Int.ediv 5 b
#testOptimize [ "ExtTdivEdiv_4" ] (norm-result: 1) ∀ (a b c : Int), 5 ≤ a → Int.tdiv a b = c ===> ∀ (a b c : Int), ¬ (a < 5) → c = Int.ediv a b
-- premise reduced to `False`: no rewriting
#testOptimize [ "ExtTdivEdiv_5" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv (-5) b = c ===> ∀ (b c : Int), c = Int.tdiv (Int.negSucc 4) b
-- `Int.tdiv 0 b` is reduced to `0` natively (the rule is not involved)
#testOptimize [ "ExtTdivEdiv_6" ] (norm-result: 1) ∀ (b c : Int), Int.tdiv 0 b = c ===> ∀ (c : Int), (0 : Int) = c

end Test.ExtensionPremiseEvalInt
