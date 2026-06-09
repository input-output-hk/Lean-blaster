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

/-- State = bank pre-state + constant_rate observer + p_max_bound observer.
    `constant_rate` at step 0 = true; at step k+1 = prev AND (rate = prev_rate).
    `p_max_bound`   at step 0 = ZERO; at step k+1 = max_bound from step k. -/
structure St where
  core          : CoreState
  constant_rate : Bool
  p_rate        : Int
  p_max_bound   : Int
deriving BEq, Repr, Inhabited

instance theorem8 : StateMachine Inp St where
  init i := { core := ⟨0, 0, 0⟩, constant_rate := true, p_rate := i.rate, p_max_bound := ZERO }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let max_bound := computeMaxBound i.rate c.n_sc c.n_rc c.reserve
    { core          := c
      constant_rate := s.constant_rate && (i.rate == s.p_rate)
      p_rate        := i.rate
      p_max_bound   := max_bound }
  assumptions _ _ := paramConstraints ∧ True  -- assert n_sc >= 0 is a lemma not assumption
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve    := c.reserve
    let n_sc       := c.n_sc
    let n_rc       := c.n_rc
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    let constant_rate := s.constant_rate
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
