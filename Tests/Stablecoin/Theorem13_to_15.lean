import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem13to15

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem13to15 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve  := c.reserve
    let n_sc     := c.n_sc
    let n_rc     := c.n_rc
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- THEOREM_13: R >= 0 and N_SC >= 0 and N_RC >= 0
    ( reserve ≥ 0 ∧ n_sc ≥ 0 ∧ n_rc ≥ 0 )
    -- THEOREM_14: If N_RC > 0 then R > 0
    ∧ ( n_rc > 0 → reserve > 0 )
    -- THEOREM_15: If N_SC > 0 then R > 0
    ∧ ( n_sc > 0 → reserve > 0 )
    -- Lemma: p_reserve >= 0 and p_sc >= 0 and p_rc >= 0
    ∧ ( p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0 )
    -- Lemma: p_rc > 0 => p_reserve > 0
    ∧ ( p_rc > 0 → p_reserve > 0 )
    -- Lemma: p_sc > 0 => p_reserve div p_sc > 0
    ∧ ( p_sc > 0 → Int.ediv p_reserve p_sc > 0 )
    -- Lemma: o_msg.ack = RedeemedSC => rate > 0
    ∧ ( o_msg.ack = .RedeemedSC → i.rate > 0 )
    -- Lemma: o_msg.ack = RedeemedSC => reserve > (p_reserve div p_sc) * (p_sc + i_msg.qnt)
    ∧ ( o_msg.ack = .RedeemedSC → reserve > Int.ediv p_reserve p_sc * (p_sc + i.i_msg.qnt) )
    -- Lemma: o_msg.ack = RedeemedSC => p_sc + i_msg.qnt >= 0
    ∧ ( o_msg.ack = .RedeemedSC → p_sc + i.i_msg.qnt ≥ 0 )
    -- Lemma: o_msg.ack = RedeemedSC => p_sc > 0
    ∧ ( o_msg.ack = .RedeemedSC → p_sc > 0 )
    -- Lemma: o_msg.ack = RedeemedSC => (p_reserve div p_sc) > 0
    ∧ ( o_msg.ack = .RedeemedSC → Int.ediv p_reserve p_sc > 0 )
    -- Lemma: o_msg.ack = RedeemedRC => p_sc * rate >= 0
    ∧ ( o_msg.ack = .RedeemedRC → p_sc * i.rate ≥ 0 )
    -- Lemma: o_msg.ack = RedeemedRC => p_reserve > 0
    ∧ ( o_msg.ack = .RedeemedRC → p_reserve > 0 )
    -- Lemma: o_msg.ack = RedeemedRC => reserve > ((p_reserve - p_sc * rate) div p_rc) * (p_rc + i_msg.qnt)
    ∧ ( o_msg.ack = .RedeemedRC → reserve > Int.ediv (p_reserve - p_sc * i.rate) p_rc * (p_rc + i.i_msg.qnt) )
    -- Lemma: o_msg.ack = RedeemedRC => p_rc + i_msg.qnt >= 0
    ∧ ( o_msg.ack = .RedeemedRC → p_rc + i.i_msg.qnt ≥ 0 )
    -- Lemma: o_msg.ack = RedeemedRC => p_rc > 0
    ∧ ( o_msg.ack = .RedeemedRC → p_rc > 0 )

#kind (max-depth: 3) (timeout: 30) [theorem13to15]

end Tests.Stablecoin.Theorem13to15
