import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem17

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem17 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve := c.reserve
    let n_sc    := c.n_sc
    -- THEOREM_17: SCs can be bought only when reserve ratio >= min ratio
    ( o_msg.ack = .MintedSC → reserve ≥ n_sc * i.rate * params.r_min )

#kind (max-depth: 3) (timeout: 30) [theorem17]

end Tests.Stablecoin.Theorem17
