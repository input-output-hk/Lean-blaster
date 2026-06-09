import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem30and31

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem30and31 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let p_rc := s.core.n_rc
    -- THEOREM 30: IF a selling reservecoin order is successful
    --             THEN either there are no stablecoins in circulation OR exchange rate > 0
    (o_msg.ack = .RedeemedRC → (c.n_sc = 0 ∨ i.rate > 0))
    ∧
    -- THEOREM 31: IF a selling reservecoin order is successful
    --             THEN number of tokens being sold <= P_RC
    (o_msg.ack = .RedeemedRC → -i.i_msg.qnt ≤ p_rc)

#kind (max-depth: 3) (timeout: 30) [theorem30and31]

end Tests.Stablecoin.Theorem30and31
