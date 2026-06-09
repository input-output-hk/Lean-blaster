import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem41

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem41 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_sc := s.core.n_sc
    -- THEOREM 41: IF a selling order for N stablecoins is NOT successful
    --             THEN rate <= 0 OR N > P_SC
    (i.i_msg.order = .MintSC ∧ i.i_msg.qnt < 0 ∧ o_msg.ack = .Error →
        (i.rate ≤ 0 ∨ -i.i_msg.qnt > p_sc))

#kind (max-depth: 3) (timeout: 30) [theorem41]

end Tests.Stablecoin.Theorem41
