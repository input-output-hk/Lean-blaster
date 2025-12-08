import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.Counter04

inductive Request where
  | Idle : Request
  | Reset : Request

structure Input where
  request : Request
  initState : Nat

instance counterInit : StateMachine Input Nat where
  init i := i.initState
  next i s :=
    match i.request with
    | .Reset => if s > 2 then 0 else s + 1
    | _ => if s < 3 then s + 1
           else s

  assumptions _ s := s < 2

  invariants _ s :=
    s ≤ 3
/--
error: ❌ Contradictory context at Depth 2
-/
#guard_msgs in
#bmc (max-depth: 6) [counterInit]

-- Note: Kind can be valid even in contradictory context
#kind (max-depth: 1) [counterInit]

end Test.Counter04
