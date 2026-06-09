import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem21and22

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem21and22 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- Local definitions from Theorem21_and_22.lus
    let equity_price := if p_rc > 0 then Int.ediv (p_reserve - p_sc * i.rate) p_rc else params.p_min
    let b_price := maxR params.p_min equity_price * i.i_msg.qnt
    -- THEOREM 21: IF buying order for N reservecoins is successful AND N > 0
    --             THEN total buying price > 0
    ((o_msg.ack = .MintedRC ∧ i.i_msg.qnt > 0) → o_msg.price > 0)
    ∧
    -- THEOREM 22: IF buying order for N reservecoins is successful
    --             THEN total buying price = max(DefaultPrice, EquityPrice) * N * (1 + baseFee)
    (o_msg.ack = .MintedRC → o_msg.price = computeFee params.fees.fee_b_rc b_price)

#kind (max-depth: 1) (timeout: 30) [theorem21and22]

end Tests.Stablecoin.Theorem21and22
