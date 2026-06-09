import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem48

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem48 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    -- THEOREM 48: A selling order for N stablecoins is always successful when:
    --   - rate > 0 AND
    --   - N < P_SC (i.e., |qnt| < p_sc)
    (i.i_msg.order = .MintSC ∧ i.i_msg.qnt < 0 ∧ i.rate > 0 ∧ -i.i_msg.qnt < s.core.n_sc →
       o_msg.ack = .RedeemedSC)

#kind (max-depth: 3) (timeout: 30) [theorem48]

end Tests.Stablecoin.Theorem48
