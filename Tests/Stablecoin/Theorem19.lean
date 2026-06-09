import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem19

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem19 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve  := c.reserve
    let n_sc     := c.n_sc
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- THEOREM_19: RCs can be sold only when reserve ratio >= min ratio
    ( o_msg.ack = .RedeemedRC → reserve ≥ n_sc * i.rate * params.r_min )
    -- Lemma: p_reserve >= 0 and p_sc >= 0 and p_rc >= 0
    ∧ ( p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0 )
    -- Lemma: p_rc > 0 => p_reserve > 0
    ∧ ( p_rc > 0 → p_reserve > 0 )
    -- Lemma: p_sc > 0 => p_reserve > 0
    ∧ ( p_sc > 0 → p_reserve > 0 )

#kind (max-depth: 3) (timeout: 30) [theorem19]

end Tests.Stablecoin.Theorem19
