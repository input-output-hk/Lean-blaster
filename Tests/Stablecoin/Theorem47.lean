import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem47

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem47 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    -- THEOREM 47: A buying stablecoin order is always successful when:
    --   - rate > 0 AND
    --   - min reserve ratio is satisfied
    (i.i_msg.order = .MintSC ∧ i.i_msg.qnt ≥ 0 ∧ i.rate > 0 ∧
       s.core.reserve + computeFee params.fees.fee_b_sc (i.i_msg.qnt * i.rate) ≥
         (s.core.n_sc + i.i_msg.qnt) * i.rate * params.r_min →
       o_msg.ack = .MintedSC)

#kind (max-depth: 3) (timeout: 30) [theorem47]

end Tests.Stablecoin.Theorem47
