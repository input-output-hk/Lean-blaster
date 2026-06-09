import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.Counter01


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
    s ≤ 3

#bmc (max-depth: 6) [counter]

#kind (max-depth: 1) [counter]

end Test.Counter01
