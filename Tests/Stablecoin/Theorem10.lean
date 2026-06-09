import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem10

-- Theorem10: SCs are always bought for 1 PC in BCs from bank.
-- No temporal observers (no pre/->), combinational.
-- --unroll_max 2

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem10 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let rate_price := i.i_msg.qnt * i.rate
    let sc_price_pc := computeFee params.fees.fee_b_sc rate_price
    -- THEOREM_10: SCs are always bought for 1 PC in BCs from bank
    (o_msg.ack = .MintedSC → o_msg.price = sc_price_pc)
    -- Lemma
    ∧ (o_msg.ack = .MintedSC → price_sc s.core.reserve s.core.n_sc i.rate = i.rate)

#kind (max-depth: 2) (timeout: 30) [theorem10]

end Tests.Stablecoin.Theorem10
