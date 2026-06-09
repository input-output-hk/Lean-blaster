import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem6

-- Theorem6: Monotonically Increasing Equity per Reservecoin (constant rate).
-- Observer: constant_rate = true -> pre constant_rate and rate = pre rate
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + observer `constant_rate` and `p_rate` (prev rate).
    `constant_rate` at step 0 = true (the -> branch).
    At step k+1: constant_rate = prev_constant_rate AND (rate = prev_rate). -/
structure St where
  core          : CoreState
  constant_rate : Bool
  p_rate        : Int
deriving BEq, Repr, Inhabited

instance theorem6 : StateMachine Inp St where
  init i := { core := ⟨0, 0, 0⟩, constant_rate := true, p_rate := i.rate }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core          := c
      constant_rate := s.constant_rate && (i.rate == s.p_rate)
      p_rate        := i.rate }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve    := c.reserve
    let n_sc       := c.n_sc
    let n_rc       := c.n_rc
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    let constant_rate := s.constant_rate
    -- THEOREM_6: Monotonically Increasing Equity per Reservecoin
    (constant_rate = true ∧ p_rc > 0 ∧ n_rc > 0 →
       Int.ediv (equity reserve n_sc i.rate) n_rc ≥
       Int.ediv (equity p_reserve p_sc i.rate) p_rc)
    -- Lemmas
    ∧ (o_msg.ack = .RedeemedRC → p_reserve ≥ reserve)
    ∧ (o_msg.ack = .RedeemedRC → p_sc = n_sc)

#kind (max-depth: 3) (timeout: 30) [theorem6]

end Tests.Stablecoin.Theorem6
