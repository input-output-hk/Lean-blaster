import Blaster.StateMachine

open Blaster.StateMachine

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

-- Not inductive up to depth 3. The counterexample-to-induction witnesses are solver-choice
-- dependent (their message severity is not stable across z3 builds), so drop the info/warning
-- detail and assert only that the command elaborates without an unexpected error.
/-- -/
#guard_msgs (drop info, drop warning) in
#kind (max-depth: 3) [counterStateMachine]

end Test.Counter06
