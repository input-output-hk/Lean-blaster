import Solver.StateMachine

open Solver.StateMachine

namespace Test.Counter05


inductive Request where
  | Idle : Request
  | Reset : Request

instance counter : StateMachine Request Nat where
  init _ := 0
  next i s :=
    match i with
    | .Reset => 0
    | _ => if s < 3 then s + 1
           else s

  assumptions _ _ := True -- no assumptions

  invariants _ s :=
    s ≤ 2
/--
error: ❌ Falsified
---
error: Counterexample detected at Depth 3:
---
error:  - «Test.Counter05.counter.input@3»: Test.Counter05.Request.Idle
---
error:  - «Test.Counter05.counter.input@2»: Test.Counter05.Request.Idle
---
error:  - «Test.Counter05.counter.input@1»: Test.Counter05.Request.Idle
-/
#guard_msgs in
#bmc (max-depth: 6) [counter]

/--
info: ⚠️ Induction failed at Depth 1
---
info: Counterexample to Induction:
---
info:  - «Test.Counter05.counter.state@0»: 2
---
info:  - «Test.Counter05.counter.input@1»: Test.Counter05.Request.Idle
---
info: ⚠️ Induction failed at Depth 2
---
info: Counterexample to Induction:
---
info:  - «Test.Counter05.counter.state@0»: 1
---
info:  - «Test.Counter05.counter.input@1»: Test.Counter05.Request.Idle
---
info:  - «Test.Counter05.counter.input@2»: Test.Counter05.Request.Idle
---
error: ❌ Falsified
---
error: Counterexample detected at Depth 3:
---
error:  - «Test.Counter05.counter.state@0»: 0
---
error:  - «Test.Counter05.counter.input@1»: Test.Counter05.Request.Idle
---
error:  - «Test.Counter05.counter.input@2»: Test.Counter05.Request.Idle
---
error:  - «Test.Counter05.counter.input@3»: Test.Counter05.Request.Idle
-/
#guard_msgs in
#kind (max-depth: 3) [counter]

end Test.Counter05
