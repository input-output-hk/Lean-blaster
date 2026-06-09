import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem16

-- Theorem16: Liveness property.
-- IF a buying order for one SC or a selling order for one RC failed due to Min_Ratio_Violated
-- (in the PREVIOUS step), AND the current order is buying RC with qnt in (0, max_bound],
-- THEN the buying RC order must succeed.
-- Local streams:
--   min_violation_on_order (current step): (i_msg.order = MintSC and qnt=1 and ack=Error and err=Min_Ratio_Violated)
--                                       or (i_msg.order = MintRC and qnt=-1 and ack=Error and err=Min_Ratio_Violated)
--   max_bound: (p_sc * rate * r_max - p_reserve) div computeFee(fee_b_rc, price_rc(1, p_reserve, p_sc, p_rc, rate))
-- check "THEOREM_16":
--   (false -> pre min_violation_on_order) and i_msg.order = MintRC and i_msg.qnt > 0 and i_msg.qnt <= max_bound
--   => o_msg.ack = MintedRC
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + `min_viol_pre` (= false -> pre min_violation_on_order).
    `min_viol_pre` at step 0 = false (the false -> branch).
    At step k+1, it is set to the `min_violation_on_order` value of step k.
    `max_bound` depends on p_reserve/p_sc/p_rc (= s.core) and current rate, so it is
    recomputed inside `invariants` directly. -/
structure St where
  core          : CoreState
  min_viol_pre  : Bool   -- (false -> pre min_violation_on_order): false at step 0; min_viol at step k
deriving BEq, Repr, Inhabited

private def minViolationOnOrder (i_msg : InputMsg) (o_msg : OutputMsg) : Bool :=
  (i_msg.order == .MintSC && i_msg.qnt == 1  && o_msg.ack == .Error && o_msg.err == .Min_Ratio_Violated) ||
  (i_msg.order == .MintRC && i_msg.qnt == -1 && o_msg.ack == .Error && o_msg.err == .Min_Ratio_Violated)

instance theorem16 : StateMachine Inp St where
  -- step 0: min_viol_pre = false (the false -> branch)
  init _ := { core := ⟨0, 0, 0⟩, min_viol_pre := false }
  next i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    -- min_viol_pre for next step = current step's min_violation_on_order
    let mv := minViolationOnOrder i.i_msg o_msg
    { core := c, min_viol_pre := mv }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    -- max_bound = (p_sc * rate * r_max - p_reserve) div computeFee(fee_b_rc, price_rc(1, p_reserve, p_sc, p_rc, rate))
    let max_bound  := Int.ediv (p_sc * i.rate * params.r_max - p_reserve)
                               (computeFee params.fees.fee_b_rc (price_rc 1 p_reserve p_sc p_rc i.rate))
    -- THEOREM_16: Liveness
    ((s.min_viol_pre = true ∧
      i.i_msg.order = .MintRC ∧
      i.i_msg.qnt > 0 ∧
      i.i_msg.qnt ≤ max_bound) →
      o_msg.ack = .MintedRC)

#kind (max-depth: 3) (timeout: 30) [theorem16]

end Tests.Stablecoin.Theorem16
