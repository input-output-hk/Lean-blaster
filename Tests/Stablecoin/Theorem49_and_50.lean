import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem49and50

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem49and50 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    -- equity computed from PRE-state (p_reserve, p_sc)
    let eq_val := equity s.core.reserve s.core.n_sc i.rate
    -- THEOREM 49: A selling order for N reservecoins is always successful when:
    --   - rate > 0 AND
    --   - N < P_RC AND
    --   - min reserve ratio is satisfied
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt < 0 ∧ i.rate > 0 ∧
       -i.i_msg.qnt < s.core.n_rc ∧
       s.core.reserve + computeFee params.fees.fee_s_rc
         (Int.ediv eq_val s.core.n_rc * i.i_msg.qnt) ≥ s.core.n_sc * i.rate * params.r_min →
       o_msg.ack = .RedeemedRC)
    ∧
    -- THEOREM 50: A selling order for N reservecoins is always successful when:
    --   - N < P_RC AND
    --   - There are no stablecoins in circulation
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt < 0 ∧ -i.i_msg.qnt < s.core.n_rc ∧
       s.core.n_sc = 0 →
       o_msg.ack = .RedeemedRC)

#kind (max-depth: 3) (timeout: 30) [theorem49and50]

end Tests.Stablecoin.Theorem49and50
