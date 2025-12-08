import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.Counter03

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
    | .Reset => 0
    | _ => if s < 3 then s + 1
           else s

  assumptions i _ := i.initState ≥ 0 ∧ i.initState ≤ 2

  invariants _ s :=
    s ≤ 3

#bmc (max-depth: 7) [counterInit]

#kind (max-depth: 1) [counterInit]

end Test.Counter03
