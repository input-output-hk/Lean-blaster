import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem9

-- Theorem9: Reserve is always > 0 once at least one successful non-zero order.
-- Observer: order_once = false -> (if successful_order and not (pre order_once) then true else pre order_once)
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + observer `order_once`.
    `order_once` starts false. It flips to true on the first step where a
    successful non-zero order occurs (and stays true thereafter). -/
structure St where
  core       : CoreState
  order_once : Bool
deriving BEq, Repr, Inhabited

instance theorem9 : StateMachine Inp St where
  -- step 0: order_once = false (the -> branch)
  init _ := { core := ⟨0, 0, 0⟩, order_once := false }
  next i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let successful := o_msg.ack != .Error && o_msg.ack != .NoReply && i.i_msg.qnt != 0
    let new_order_once :=
      if successful && !s.order_once then true
      else s.order_once
    { core := c, order_once := new_order_once }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve := c.reserve
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- THEOREM_9: Reserve > 0 once at least one order was successful
    (s.order_once = true → reserve > 0)
    -- Lemmas
    ∧ (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    ∧ (p_rc > 0 → p_reserve > 0)
    ∧ (p_sc > 0 → p_reserve > 0)

#kind (max-depth: 3) (timeout: 30) [theorem9]

end Tests.Stablecoin.Theorem9
