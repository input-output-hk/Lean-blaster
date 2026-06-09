import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem23and24

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem23and24 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    -- THEOREM 23: IF a selling order for N stablecoins is successful AND
    --             equity is zero (reserve < p_sc * rate)
    --             THEN total selling price = (reserve / n_sc) * N * (1 - baseFee)
    ((o_msg.ack = .RedeemedSC ∧ p_reserve < p_sc * i.rate) →
        o_msg.price = computeFee params.fees.fee_s_sc (Int.ediv p_reserve p_sc * i.i_msg.qnt))
    ∧
    -- THEOREM 24: IF a selling stablecoin order is successful
    --             THEN total selling price is always >= 0
    (o_msg.ack = .RedeemedSC → -o_msg.price ≥ 0)
    ∧
    -- Lemma
    (p_sc > 0 → p_reserve > 0)

#kind (max-depth: 3) (timeout: 30) [theorem23and24]

end Tests.Stablecoin.Theorem23and24
