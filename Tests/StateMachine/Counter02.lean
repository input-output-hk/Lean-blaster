import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.Counter02

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

instance counterStateMachine : StateMachine Request CounterState where
  init _ := { state := .Ready, timer := 0}
  next i s :=
    match s.state with
    | .Ready =>
         match i with
         | .Tr => { state := .Delay, timer := 0}
         | _ => s
    | .Delay =>
         if s.timer < 3
         then {s with timer := s.timer + 1}
         else {s with state := .Busy }
    | .Busy =>
         match i with
         | .Fa => {s with state := .Ready}
         | _ => s

  assumptions _ _ := True -- no assumptions

  invariants _ s :=
    (s.timer > 0 → s.timer < 3 → s.state = .Delay) ∧
    s.timer ≥ 0 ∧
    s.timer ≤ 3

#bmc (max-depth: 8) [counterStateMachine]

#kind (max-depth: 1) [counterStateMachine]

end Test.Counter02
