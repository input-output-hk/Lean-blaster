import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem4

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem4 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s := let (_, c) := stepStableCoin i.i_msg i.rate s.core; { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    equity c.reserve c.n_sc i.rate ≥ 0

#kind (max-depth: 3) (timeout: 60) [theorem4]

end Tests.Stablecoin.Theorem4
