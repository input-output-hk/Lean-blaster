import Blaster

namespace Tests.Issue413

-- Issues:
--  - https://github.com/input-output-hk/Lean-blaster/issues/413
-- Diagnosis:
--   - `max u v` universe level is commutative. We should normalize max universe by ordering the levels.

set_option warn.sorry false

/-- Should be reported as valid by Blaster -/
theorem unit_eq : PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} := by blaster

/-- error: ❌ Falsified
---
error: Counterexample:
---
error: Tactic `blaster` failed: Goal was falsified (see counterexample above)

⊢ PUnit.unit ≠ PUnit.unit
-/
#guard_msgs in
theorem unit_ne : PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1} := by blaster


end Tests.Issue413
