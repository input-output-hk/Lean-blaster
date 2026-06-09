import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem42

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem42 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve   := s.core.reserve
    let p_sc        := s.core.n_sc
    let p_rc        := s.core.n_rc
    -- Local auxiliary vars (pre-state based, matching Lustre)
    let equity_price :=
      if p_rc > 0 then Int.ediv (p_reserve - p_sc * i.rate) p_rc else params.p_min
    let b_price := maxR params.p_min equity_price * i.i_msg.qnt
    -- THEOREM 42: IF a buying order for N reservecoins is NOT successful
    --             THEN (rate <= 0 AND n_sc >= n_sc_s) OR
    --                  p_reserve + computeFee(fee_b_rc, b_price) > n_sc * rate * r_max
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt ≥ 0 ∧ o_msg.ack = .Error →
        ((i.rate ≤ 0 ∧ c.n_sc ≥ params.n_sc_s) ∨
          p_reserve + computeFee params.fees.fee_b_rc b_price >
            c.n_sc * i.rate * params.r_max))

#kind (max-depth: 3) (timeout: 30) [theorem42]

end Tests.Stablecoin.Theorem42
