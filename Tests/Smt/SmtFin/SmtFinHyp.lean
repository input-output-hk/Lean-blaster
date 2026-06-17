import Blaster

namespace Test.SmtFinHyp

/-! # Fin in theorem-hypothesis position (tactic mode).

Regression: a reverted hypothesis binder carries its bound as a proj-form
`OfNat.ofNat 5` (`Expr.proj OfNat 0 …`), not a raw `Nat` literal. The `Fin`
range qualifier is cached under the canonical `Fin (lit n)` key, so the
qualifier lookup must canonicalize the bound too — otherwise it misses with
"createPredQualifierAppAux: predicate declaration expected". -/

theorem fin_hyp_range (i : Fin 5) : i.val < 5 := by blaster

theorem fin_hyp_two (i j : Fin 8) : i.val < 8 ∧ j.val < 8 := by blaster

end Test.SmtFinHyp
