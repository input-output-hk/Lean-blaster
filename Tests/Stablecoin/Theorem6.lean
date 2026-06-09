import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem6

-- Theorem6: Monotonically Increasing Equity per Reservecoin (constant rate).
-- Observer: constant_rate = true -> pre constant_rate and rate = pre rate
-- check "THEOREM_6":
--   (constant_rate and p_rc > 0 and n_rc > 0) =>
--      equity(reserve, n_sc, rate) div n_rc >= equity(p_reserve, p_sc, rate) div p_rc
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + `cr_pre` (constant_rate at PREVIOUS step) + `p_rate` (rate at PREVIOUS step).
    In `invariants`, RECOMPUTE `constant_rate = s.cr_pre && (i.rate == s.p_rate)` for the current step. -/
structure St where
  core   : CoreState
  cr_pre : Bool   -- constant_rate at PREVIOUS step
  p_rate : Int    -- rate at PREVIOUS step
deriving BEq, Repr, Inhabited

instance theorem6 : StateMachine Inp St where
  -- step 0: constant_rate = true (-> branch); cr_pre = true, p_rate = rate
  init i := { core := ⟨0, 0, 0⟩, cr_pre := true, p_rate := i.rate }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    -- constant_rate at THIS step stored as cr_pre for next step
    let cr_cur := s.cr_pre && (i.rate == s.p_rate)
    { core   := c
      cr_pre := cr_cur
      p_rate := i.rate }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve    := c.reserve
    let n_sc       := c.n_sc
    let n_rc       := c.n_rc
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    -- Recompute current constant_rate = true -> pre constant_rate and rate = pre rate
    let constant_rate := s.cr_pre && (i.rate == s.p_rate)
    -- THEOREM_6: Monotonically Increasing Equity per Reservecoin
    (constant_rate = true ∧ p_rc > 0 ∧ n_rc > 0 →
       Int.ediv (equity reserve n_sc i.rate) n_rc ≥
       Int.ediv (equity p_reserve p_sc i.rate) p_rc)
    -- Lemmas
    ∧ (o_msg.ack = .RedeemedRC → p_reserve ≥ reserve)
    ∧ (o_msg.ack = .RedeemedRC → p_sc = n_sc)

#kind (max-depth: 1) (timeout: 30) [theorem6]

end Tests.Stablecoin.Theorem6
