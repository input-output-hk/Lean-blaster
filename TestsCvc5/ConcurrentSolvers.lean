import Blaster
import Blaster.StateMachine

namespace Test.ConcurrentSolvers

open Blaster.StateMachine

/-! Both modes exercise one optimized Lean expression and one shared SMT translation.
    Concrete falsifying witnesses keep counterexample rendering backend-independent. -/

#blaster (solver-mode: first) [∀ (x y : Int), x + y = y + x]
#blaster (solver-mode: agree) [∀ (x y : Int), x + y = y + x]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: 3
-/
#guard_msgs in
#blaster (solver-mode: first) (solve-result: 1) [∀ (x : Int), x ≠ 3]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: 3
-/
#guard_msgs in
#blaster (solver-mode: agree) (solve-result: 1) [∀ (x : Int), x ≠ 3]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - value: Option.some 5
-/
#guard_msgs in
#blaster (solver-mode: first) (solve-result: 1) [∀ (value : Option Int), value ≠ some 5]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - value: Option.some 5
-/
#guard_msgs in
#blaster (solver-mode: agree) (solve-result: 1) [∀ (value : Option Int), value ≠ some 5]

instance counter : StateMachine Int Int where
  init input := input
  next input _ := input
  assumptions input _ := 0 ≤ input
  invariants _ state := 0 ≤ state

-- Repeated `check-sat-assuming` calls force first mode to restart a retired
-- loser and replay the same retained canonical query without retranslating.
#bmc (solver-mode: first) (max-depth: 2) [counter]

-- Agreement mode keeps both incremental sessions live across depths.
#bmc (solver-mode: agree) (max-depth: 2) [counter]

end Test.ConcurrentSolvers
