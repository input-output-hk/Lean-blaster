import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem44to46

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem44to46 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    -- Local variables computed from PRE-state (p_reserve, p_sc, p_rc = s.core.*)
    let equity_price := if s.core.n_rc > 0
                        then Int.ediv (s.core.reserve - s.core.n_sc * i.rate) s.core.n_rc
                        else params.p_min
    let b_price := maxR params.p_min equity_price * i.i_msg.qnt
    -- THEOREM 44: A buying reservecoin order is always successful when N_SC < N*SC
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt ≥ 0 ∧ c.n_sc < params.n_sc_s → o_msg.ack = .MintedRC)
    ∧
    -- THEOREM 45: A buying reservecoin order is always successful when max reserve ratio is satisfied
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt ≥ 0 ∧
       s.core.reserve + computeFee params.fees.fee_b_rc b_price ≤ c.n_sc * i.rate * params.r_max →
       o_msg.ack = .MintedRC)
    ∧
    -- THEOREM 46: A buying reservecoin order is always successful when there are no stablecoins in circulation
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt ≥ 0 ∧ c.n_sc = 0 → o_msg.ack = .MintedRC)

#kind (max-depth: 3) (timeout: 30) [theorem44to46]

end Tests.Stablecoin.Theorem44to46
