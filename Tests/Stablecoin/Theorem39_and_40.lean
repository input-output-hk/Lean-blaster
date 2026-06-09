import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem39and40

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem39and40 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let p_sc      := s.core.n_sc
    -- THEOREM 39: IF a buying order for N stablecoins is NOT successful
    --             THEN rate <= 0 OR reserve + computeFee(...) < (p_sc + N) * rate * r_min
    (i.i_msg.order = .MintSC ∧ i.i_msg.qnt ≥ 0 ∧ o_msg.ack = .Error →
        (i.rate ≤ 0 ∨
          c.reserve + computeFee params.fees.fee_b_sc (i.rate * i.i_msg.qnt) <
            (p_sc + i.i_msg.qnt) * i.rate * params.r_min))
    ∧
    -- THEOREM 40: A buying stablecoin order is NOT successful WHEN
    --             rate > 0 AND p_sc > 0 AND rate > reserve div p_sc
    (i.i_msg.order = .MintSC ∧ i.i_msg.qnt ≥ 0 ∧ i.rate > 0 ∧ p_sc > 0 ∧
        i.rate > Int.ediv c.reserve p_sc →
      o_msg.ack = .Error)

#kind (max-depth: 3) (timeout: 30) [theorem39and40]

end Tests.Stablecoin.Theorem39and40
