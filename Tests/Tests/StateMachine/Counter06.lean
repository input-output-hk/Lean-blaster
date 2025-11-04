import Solver.StateMachine

open Solver.StateMachine

namespace Test.Counter06

inductive Request where
  | Tr : Request
  | Fa : Request

inductive State where
  | Ready : State
  | Delay : State
  | Busy : State

structure CounterState where
  state : State
  timer : Nat
  prev_state : State -- pre temporal operator encoding on State
  prev_req : Request -- pre temporal operator encoding on Request
  prev_timer : Nat -- pre temporal operator encoding on timer


instance counterStateMachine : StateMachine Request CounterState where
  init i := { state := .Ready, timer := 0, prev_state := .Ready, prev_req := i, prev_timer := 0}
  next i s :=
    let s' := {s with prev_state := s.state, prev_req := i}
    match s.state with
    | .Ready =>
         match i with
         | .Tr => {s' with state := .Delay, timer := 0}
         | _ => s'
    | .Delay =>
         if s.timer < 3
         then {s' with timer := s.timer + 1}
         else {s' with state := .Busy }
    | .Busy =>
         match i with
         | .Fa => {s' with state := .Ready}
         | _ => s'

  assumptions _ _ := True -- no assumptions

  invariants _i s :=
    (s.prev_state = .Delay ∧ s.prev_timer = 3) → s.state = .Busy -- cannot be proved alone as not inductive

#bmc (max-depth: 8) [counterStateMachine]

/--
info: ⚠️ Induction failed at Depth 1
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: (Test.Counter06.CounterState.mk
  Test.Counter06.State.Delay
  2
  Test.Counter06.State.Busy
  Test.Counter06.Request.Tr
  3)
---
info:  - «Test.Counter06.counterStateMachine.input@1»: Test.Counter06.Request.Tr
---
info: ⚠️ Induction failed at Depth 2
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: (Test.Counter06.CounterState.mk
  Test.Counter06.State.Ready
  2
  Test.Counter06.State.Busy
  Test.Counter06.Request.Tr
  3)
---
info:  - «Test.Counter06.counterStateMachine.input@1»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.input@2»: Test.Counter06.Request.Tr
---
info: ⚠️ Induction failed at Depth 3
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: (Test.Counter06.CounterState.mk
  Test.Counter06.State.Ready
  2
  Test.Counter06.State.Busy
  Test.Counter06.Request.Tr
  3)
---
info:  - «Test.Counter06.counterStateMachine.input@1»: Test.Counter06.Request.Fa
---
info:  - «Test.Counter06.counterStateMachine.input@2»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.input@3»: Test.Counter06.Request.Tr
---
warning: ⚠️ Failed to establish induction up to Depth 3
-/
#guard_msgs in
#kind (max-depth: 3) [counterStateMachine]

end Test.Counter06
