import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem9

-- Theorem9: Reserve is always > 0 once at least one successful non-zero order.
-- Observer: order_once = false ->
--   if (o_msg.ack <> Error and o_msg.ack <> NoReply and i_msg.qnt <> 0) and not (pre order_once)
--   then true else pre order_once
-- check "THEOREM_9" order_once => reserve > 0
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + `order_once_pre` (= "a success occurred in steps 0..k-1").
    `order_once_pre` starts false (the false -> branch gives order_once = false at step 0,
    so the pre of that is what we store for the NEXT step).
    In `invariants` we recompute the CURRENT-step `order_once` (covering steps 0..k inclusive)
    as `s.order_once_pre || success_now`, so the theorem obligation is not vacuous on the
    first-success step. -/
structure St where
  core            : CoreState
  order_once_pre  : Bool   -- "success occurred in 0..k-1" (= pre order_once at step k)
deriving BEq, Repr, Inhabited

instance theorem9 : StateMachine Inp St where
  -- step 0: order_once = false (-> branch); order_once_pre for step 0 = false
  init _ := { core := ⟨0, 0, 0⟩, order_once_pre := false }
  next i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let successful := o_msg.ack != .Error && o_msg.ack != .NoReply && i.i_msg.qnt != 0
    -- order_once at this step = s.order_once_pre || successful (but Lustre's "once flips" version)
    let order_once_now :=
      if successful && !s.order_once_pre then true
      else s.order_once_pre
    { core := c, order_once_pre := order_once_now }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve    := c.reserve
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    -- Recompute order_once at the CURRENT step (covering 0..k inclusive)
    let success_now    := o_msg.ack != .Error && o_msg.ack != .NoReply && i.i_msg.qnt != 0
    let order_once_now :=
      if success_now && !s.order_once_pre then true
      else s.order_once_pre
    -- THEOREM_9: Reserve > 0 once at least one order was successful (current step inclusive)
    (order_once_now = true → reserve > 0)
    -- Lemmas
    ∧ (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    ∧ (p_rc > 0 → p_reserve > 0)
    ∧ (p_sc > 0 → p_reserve > 0)

#kind (max-depth: 1) (timeout: 30) [theorem9]

end Tests.Stablecoin.Theorem9
