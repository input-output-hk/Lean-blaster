import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem27to29

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem27to29 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_sc := s.core.n_sc
    -- THEOREM 27: IF a buying stablecoin order is successful
    --             THEN exchange rate > 0
    (o_msg.ack = .MintedSC → i.rate > 0)
    ∧
    -- THEOREM 28: IF a selling stablecoin is successful
    --             THEN exchange rate > 0
    (o_msg.ack = .RedeemedSC → i.rate > 0)
    ∧
    -- THEOREM 29: IF a selling stablecoin is successful
    --             THEN number of tokens being sold <= P_SC
    (o_msg.ack = .RedeemedSC → -i.i_msg.qnt ≤ p_sc)

#kind (max-depth: 3) (timeout: 30) [theorem27to29]

end Tests.Stablecoin.Theorem27to29
