import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem12

-- Theorem12: RCs can be sold only when E(R, N_SC) > 0.
-- No temporal observers (no pre/->), combinational.
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem12 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- THEOREM_12: RCs can be sold only when E(R, N_SC) > 0
    (o_msg.ack = .RedeemedRC → equity p_reserve p_sc i.rate > 0)
    -- Lemmas
    ∧ (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    ∧ (p_rc > 0 → p_reserve > 0)
    ∧ (p_sc > 0 → p_reserve > 0)

#kind (max-depth: 3) (timeout: 30) [theorem12]

end Tests.Stablecoin.Theorem12
