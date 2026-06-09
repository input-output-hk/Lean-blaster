import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem11

-- Theorem11: When reserve ratio >= 1, SCs are always sold for 1 PC in BCs.
-- No temporal observers (no pre/->), combinational.
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem11 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let rate_price := i.i_msg.qnt * i.rate
    let sc_price_pc := computeFee params.fees.fee_s_sc rate_price
    -- THEOREM_11: When reserve ratio >= 1, SCs are always sold for 1 PC in BCs
    (o_msg.ack = .RedeemedSC ∧ p_reserve ≥ p_sc * i.rate → o_msg.price = sc_price_pc)

#kind (max-depth: 3) (timeout: 30) [theorem11]

end Tests.Stablecoin.Theorem11
