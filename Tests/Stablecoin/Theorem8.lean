import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem8

-- Theorem8: Bounded Dilution — number of RCs bought <= max_bound.
-- Observers: constant_rate (= true -> pre cr AND rate = pre rate)
--            p_max_bound   (= ZERO -> pre max_bound)
-- Extra input: f_max : bool (declared but unused in the node body)
-- assert n_sc >= 0  (source line 32 — node-level assert, i.e. assumption)
-- --unroll_max 3

structure Inp where
  i_msg : InputMsg
  rate  : Int
  f_max : Bool   -- declared in node signature (unused in body)
deriving BEq, Repr, Inhabited

/-- max_bound computed from post-state values at the current step. -/
private def computeMaxBound (rate n_sc n_rc reserve : Int) : Int :=
  if rate > ZERO then
    let num  := (n_sc * rate * params.r_max - reserve) * PER - 99
    let dnum := price_rc 1 reserve n_sc n_rc rate * params.fees.fee_b_rc
    maxR ZERO (Int.ediv num dnum)
  else 0

/-- State = bank pre-state + `cr_pre` (constant_rate at PREVIOUS step) + `p_rate` (rate at
    PREVIOUS step) + `p_max_bound` (= ZERO -> pre max_bound).
    In `invariants`, RECOMPUTE `constant_rate = s.cr_pre && (i.rate == s.p_rate)`. -/
structure St where
  core        : CoreState
  cr_pre      : Bool   -- constant_rate at PREVIOUS step
  p_rate      : Int    -- rate at PREVIOUS step
  p_max_bound : Int
deriving BEq, Repr, Inhabited

instance theorem8 : StateMachine Inp St where
  init i := { core := ⟨0, 0, 0⟩, cr_pre := true, p_rate := i.rate, p_max_bound := ZERO }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let max_bound := computeMaxBound i.rate c.n_sc c.n_rc c.reserve
    -- constant_rate at THIS step stored as cr_pre for next step
    let cr_cur := s.cr_pre && (i.rate == s.p_rate)
    { core        := c
      cr_pre      := cr_cur
      p_rate      := i.rate
      p_max_bound := max_bound }
  -- assert ParameterConstraints() AND assert n_sc >= 0
  -- n_sc in the source is the post-state n_sc (result of current step)
  assumptions i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    paramConstraints ∧ c.n_sc ≥ 0
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    -- Recompute current constant_rate = true -> pre constant_rate and rate = pre rate
    let constant_rate := s.cr_pre && (i.rate == s.p_rate)
    let p_max_bound   := s.p_max_bound
    let dnum := price_rc 1 p_reserve p_sc p_rc i.rate * params.fees.fee_b_rc
    -- THEOREM_8: Bounded Dilution
    (constant_rate = true ∧ p_sc ≥ params.n_sc_s ∧ o_msg.ack = .MintedRC →
       i.i_msg.qnt ≤ p_max_bound)
    -- Lemmas
    ∧ (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    ∧ (p_rc > 0 → p_reserve > 0)
    ∧ (p_sc > 0 → p_reserve > 0)
    ∧ (constant_rate = true ∧ p_sc > 0 → i.rate > 0)
    ∧ (dnum > 0)

#kind (max-depth: 3) (timeout: 30) [theorem8]

end Tests.Stablecoin.Theorem8
