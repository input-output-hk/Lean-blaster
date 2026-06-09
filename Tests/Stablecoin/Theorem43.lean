import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem43

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem43 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- Local auxiliary var (pre-state based, matching Lustre)
    let equity_val :=
      if p_reserve > p_sc * i.rate then p_reserve - p_sc * i.rate else ZERO
    -- THEOREM 43: IF a selling order for N reservecoins is NOT successful
    --             THEN N > P_RC OR
    --                  (rate <= 0 AND n_sc > 0) OR
    --                  p_reserve + computeFee(fee_s_rc, (equity/p_rc)*N) < n_sc*rate*r_min
    (i.i_msg.order = .MintRC ∧ i.i_msg.qnt < 0 ∧ o_msg.ack = .Error →
        (-i.i_msg.qnt > p_rc ∨
          (i.rate ≤ 0 ∧ c.n_sc > 0) ∨
          p_reserve + computeFee params.fees.fee_s_rc
              (Int.ediv equity_val p_rc * i.i_msg.qnt) <
            c.n_sc * i.rate * params.r_min))
    ∧
    -- Lemmas (inductive strengtheners)
    (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    ∧
    (p_sc > 0 → p_reserve > 0)
    ∧
    (p_rc > 0 → p_reserve > 0)

#kind (max-depth: 1) (timeout: 30) [theorem43]

end Tests.Stablecoin.Theorem43
