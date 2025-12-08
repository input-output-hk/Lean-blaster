import Lean
import Blaster.StateMachine

open Blaster.StateMachine

namespace Tests.Issue23

-- Issue: Unexpected counterexample
-- Diagnosis : We need to consider axioms in the current namespace in #bmc and #kind command.

set_option warn.sorry false

inductive Request where
  | Idle : Request
  | Reset : Request

structure Input where
  request : Request
  initState : Nat

axiom init_and_no_reset : ∀ (x : Input), x.initState ≥ 0 ∧ x.initState ≤ 2 ∧ x.request ≠ .Reset

instance counterInit : StateMachine Input Nat where
  init i := i.initState
  next i s :=
    match i.request with
    | .Reset => 0
    | _ => if s < 3 then s + 1
           else s

  assumptions _ _ := True

  invariants _ s :=
    s ≤ 3

#bmc (max-depth: 7) [counterInit]

#kind (max-depth: 1) [counterInit]

end Tests.Issue23
