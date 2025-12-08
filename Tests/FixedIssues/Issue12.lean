import Lean
import Blaster

namespace Tests.Issue12

-- Issue: diteToPropExpr? : lambda expression expected but got Lean.Expr.fvar xxx
-- Diagnosis: There is a need to handle cases where then and else clauses are quantified function.

theorem dite_to_prop {c : Bool} {t : c → Prop} {e : ¬ c → Prop} :
  (dite c t e) → ∀ (h : c), t h ∧ ∀ (h : ¬ c), e h :=
    by split <;> rename_i ht <;> intro h1 h2 <;> constructor
       . assumption
       . intro h3
         contradiction
       . contradiction
       . intro h3
         assumption

#blaster (only-optimize:1) [dite_to_prop]

end Tests.Issue12
