import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem18

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem18 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve := c.reserve
    let n_sc    := c.n_sc
    let p_sc    := s.core.n_sc
    -- THEOREM_18: RCs can be bought only when p_sc < n_sc_s OR reserve ratio <= max ratio
    ( o_msg.ack = .MintedRC → (p_sc < params.n_sc_s ∨ reserve ≤ n_sc * i.rate * params.r_max) )

#kind (max-depth: 3) (timeout: 30) [theorem18]

end Tests.Stablecoin.Theorem18
