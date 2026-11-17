import Blaster.StateMachine

open Blaster.StateMachine

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
error:  - «Test.Counter05.counter.input@3»: (Request.Idle : Request)
---
error:  - «Test.Counter05.counter.input@1»: (Request.Idle : Request)
---
error:  - «Test.Counter05.counter.input@2»: (Request.Idle : Request)
-/
#guard_msgs in
#bmc (max-depth: 6) [counter]

/--
info: ⚠️ Induction failed at Depth 1
---
info: Counterexample to Induction:
---
info:  - «Test.Counter05.counter.state@0»: (2 : Nat)
---
info:  - «Test.Counter05.counter.input@1»: (Request.Idle : Request)
---
info: ⚠️ Induction failed at Depth 2
---
info: Counterexample to Induction:
---
info:  - «Test.Counter05.counter.state@0»: (1 : Nat)
---
info:  - «Test.Counter05.counter.input@1»: (Request.Idle : Request)
---
info:  - «Test.Counter05.counter.input@2»: (Request.Idle : Request)
---
error: ❌ Falsified
---
error: Counterexample detected at Depth 3:
---
error:  - «Test.Counter05.counter.state@0»: (0 : Nat)
---
error:  - «Test.Counter05.counter.input@1»: (Request.Idle : Request)
---
error:  - «Test.Counter05.counter.input@2»: (Request.Idle : Request)
---
error:  - «Test.Counter05.counter.input@3»: (Request.Idle : Request)
-/
#guard_msgs in
#kind (max-depth: 3) [counter]

end Test.Counter05
