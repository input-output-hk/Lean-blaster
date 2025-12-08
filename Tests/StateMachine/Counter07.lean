import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.Counter07

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
    (s.prev_state = .Delay ∧ s.prev_timer = 3) → s.state = .Busy ∧
    (s.prev_state = .Ready ∧ s.prev_req = .Tr) → s.state = .Delay ∧
    (s.prev_state = .Delay ∧ s.state = .Delay) → s.timer = s.prev_timer + 1 ∧ s.prev_timer < 3 ∧
    (s.prev_state = .Busy ∧ s.prev_req = .Fa) → s.state = .Ready

#bmc (max-depth: 8) [counterStateMachine]

#kind (max-depth: 1) [counterStateMachine]

end Test.Counter07
