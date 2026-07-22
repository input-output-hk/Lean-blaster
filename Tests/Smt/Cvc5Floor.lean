import Blaster

namespace Test.Cvc5Floor

/-! Minimal cvc5 support-floor checks. This module intentionally contains one
    satisfiable query, one unsatisfiable query, and one counterexample query. -/

-- Satisfiable negated goal: backend must report Falsified.
#blaster (solver: cvc5) (gen-cex: 0) (solve-result: 1) [∀ (x : Int), x = 0]

-- Unsatisfiable negated goal: backend must report Valid.
#blaster (solver: cvc5) [∀ (x : Int), x = x]

-- Satisfiable negated goal with a unique model value, exercising get-value.
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: 3
-/
#guard_msgs in
#blaster (solver: cvc5) (gen-cex: 1) (solve-result: 1) [∀ (x : Int), x ≠ 3]

end Test.Cvc5Floor
