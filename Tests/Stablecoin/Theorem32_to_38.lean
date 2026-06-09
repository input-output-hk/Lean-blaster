import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem32to38

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem32to38 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- THEOREM 32: IF buying order for N reservecoins is successful
    --             THEN n_rc = p_rc + N AND reserve = p_reserve + price
    (o_msg.ack = .MintedRC →
        (c.n_rc = p_rc + i.i_msg.qnt ∧ c.reserve = p_reserve + o_msg.price))
    ∧
    -- THEOREM 33: IF selling order for N reservecoins is successful
    --             THEN n_rc = p_rc + N AND reserve = p_reserve + price (qnt/price negative)
    (o_msg.ack = .RedeemedRC →
        (c.n_rc = p_rc + i.i_msg.qnt ∧ c.reserve = p_reserve + o_msg.price))
    ∧
    -- THEOREM 34: IF a buying/selling reservecoin order is NOT successful
    --             THEN n_rc = p_rc
    ((o_msg.ack ≠ .MintedRC ∧ o_msg.ack ≠ .RedeemedRC) → c.n_rc = p_rc)
    ∧
    -- THEOREM 35: IF a buying order for N stablecoins is successful
    --             THEN n_sc = p_sc + N AND reserve = p_reserve + price
    (o_msg.ack = .MintedSC →
        (c.n_sc = p_sc + i.i_msg.qnt ∧ c.reserve = p_reserve + o_msg.price))
    ∧
    -- THEOREM 36: IF a selling order for N stablecoins is successful
    --             THEN n_sc = p_sc + N AND reserve = p_reserve + price (qnt/price negative)
    (o_msg.ack = .RedeemedSC →
        (c.n_sc = p_sc + i.i_msg.qnt ∧ c.reserve = p_reserve + o_msg.price))
    ∧
    -- THEOREM 37: IF a buying/selling stablecoin order is NOT successful
    --             THEN n_sc = p_sc
    ((o_msg.ack ≠ .MintedSC ∧ o_msg.ack ≠ .RedeemedSC) → c.n_sc = p_sc)
    ∧
    -- THEOREM 38: IF any buying/selling order is NOT successful
    --             THEN reserve = p_reserve
    ((o_msg.ack ≠ .MintedSC ∧ o_msg.ack ≠ .RedeemedSC ∧
      o_msg.ack ≠ .MintedRC ∧ o_msg.ack ≠ .RedeemedRC) →
        c.reserve = p_reserve)

#kind (max-depth: 3) (timeout: 30) [theorem32to38]

end Tests.Stablecoin.Theorem32to38
