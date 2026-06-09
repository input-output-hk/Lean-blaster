import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem7

-- Theorem7: No Reserve Draining (constant rate, arbitrary initial bank state).
-- Node inputs: i_msg, rate, i_reserve, i_sc, i_rc
-- StableCoin_InitState(i_reserve, i_sc, i_rc, i_msg, rate) → init core = ⟨i_reserve, i_sc, i_rc⟩
-- Observers (all -> pre recurrences):
--   constant_rate = true -> pre constant_rate and rate = pre rate
--   reserve_0 = i_reserve -> pre reserve_0   (frozen initial reserve)
--   n_sc_0    = i_sc      -> pre n_sc_0       (frozen initial n_sc)
--   n_rc_0    = i_rc      -> pre n_rc_0       (frozen initial n_rc)
--   coins_positive = (i_sc > 0 and i_rc > 0) -> pre coins_positive and p_sc > 0 and p_rc > 0
-- --unroll_max 3 (Kind2 needed 600s + invariant generation)

structure Inp where
  i_msg     : InputMsg
  rate      : Int
  i_reserve : Int
  i_sc      : Int
  i_rc      : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + observer fields.
    `cr_pre`  and `p_rate`: store the PREVIOUS step's constant_rate and rate, so that
      `constant_rate` for the CURRENT step is recomputed in `invariants` as
      `s.cr_pre && (i.rate == s.p_rate)`.
    `coins_positive_pre`: store the PREVIOUS step's coins_positive, so that
      `coins_positive` for the CURRENT step is recomputed in `invariants` as
      `s.coins_positive_pre && (s.core.n_sc > 0 && s.core.n_rc > 0)`.
      (s.core = p_sc/p_rc = pre-state at step k, so p_sc>0 and p_rc>0 is the source's "pre" values.)
    `reserve_0`, `n_sc_0`, `n_rc_0`: frozen at step 0. -/
structure St where
  core               : CoreState
  cr_pre             : Bool   -- constant_rate at PREVIOUS step
  p_rate             : Int    -- rate at PREVIOUS step
  reserve_0          : Int
  n_sc_0             : Int
  n_rc_0             : Int
  coins_positive_pre : Bool   -- coins_positive at PREVIOUS step
deriving BEq, Repr, Inhabited

instance theorem7 : StateMachine Inp St where
  -- At step 0: pre-state = (i_reserve, i_sc, i_rc);
  -- constant_rate = true (-> branch) → cr_pre = true;  p_rate = rate;
  -- frozen observers = initial inputs;
  -- coins_positive at step 0 = (i_sc > 0 ∧ i_rc > 0) (-> branch) → coins_positive_pre = that value.
  init i :=
    { core               := ⟨i.i_reserve, i.i_sc, i.i_rc⟩
      cr_pre             := true
      p_rate             := i.rate
      reserve_0          := i.i_reserve
      n_sc_0             := i.i_sc
      n_rc_0             := i.i_rc
      coins_positive_pre := (i.i_sc > 0 && i.i_rc > 0) }
  -- At step k+1: advance core; update all stored-previous values.
  -- cr_pre_{k+1}             = constant_rate at step k = s.cr_pre && (i.rate == s.p_rate)
  -- coins_positive_pre_{k+1} = coins_positive at step k = s.coins_positive_pre && (s.core.n_sc > 0 && s.core.n_rc > 0)
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let cr_cur := s.cr_pre && (i.rate == s.p_rate)
    let cp_cur := s.coins_positive_pre && (s.core.n_sc > 0 && s.core.n_rc > 0)
    { core               := c
      cr_pre             := cr_cur
      p_rate             := i.rate
      reserve_0          := s.reserve_0
      n_sc_0             := s.n_sc_0
      n_rc_0             := s.n_rc_0
      coins_positive_pre := cp_cur }
  -- Assumptions: ParameterConstraints() + initial bank state validity asserts
  assumptions i _ :=
    paramConstraints ∧
    i.i_reserve ≥ 0 ∧
    i.i_sc ≥ 0 ∧
    i.i_rc ≥ 0 ∧
    i.rate > 0 ∧
    (i.i_sc > 0 → Int.ediv i.i_reserve i.i_sc > 0) ∧
    (i.i_sc > 0 → Int.ediv i.i_reserve i.i_sc > i.rate) ∧
    (i.i_rc > 0 → i.i_reserve > 0)
  -- Invariants: ALL non-commented check expressions.
  -- Recompute constant_rate and coins_positive for the CURRENT step inside invariants.
  invariants i s :=
    let (_, c)   := stepStableCoin i.i_msg i.rate s.core
    let reserve  := c.reserve
    let n_sc     := c.n_sc
    let n_rc     := c.n_rc
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let p_rc      := s.core.n_rc
    -- Recompute current constant_rate = true -> pre constant_rate and rate = pre rate
    let constant_rate   := s.cr_pre && (i.rate == s.p_rate)
    -- Recompute current coins_positive = (i_sc>0 and i_rc>0) -> pre coins_positive and p_sc>0 and p_rc>0
    -- (p_sc/p_rc at step k = s.core.n_sc/n_rc = the source's p_sc/p_rc)
    let coins_positive  := s.coins_positive_pre && (s.core.n_sc > 0 && s.core.n_rc > 0)
    let reserve_0       := s.reserve_0
    let n_sc_0          := s.n_sc_0
    let n_rc_0          := s.n_rc_0
    -- check "THEOREM_7": constant_rate => not (coins_positive and reserve < reserve_0 and n_sc = n_sc_0 and n_rc = n_rc_0)
    (constant_rate = true →
       ¬(coins_positive = true ∧ reserve < reserve_0 ∧ n_sc = n_sc_0 ∧ n_rc = n_rc_0))
    -- check (constant_rate and coins_positive and p_sc <> n_sc_0) => rate > 0
    ∧ (constant_rate = true ∧ coins_positive = true ∧ p_sc ≠ n_sc_0 → i.rate > 0)
    -- check coins_positive => reserve_0 > 0
    ∧ (coins_positive = true → reserve_0 > 0)
    -- check coins_positive => p_reserve > 0
    ∧ (coins_positive = true → p_reserve > 0)
    -- check coins_positive => (p_rc > 0 and p_sc > 0)
    ∧ (coins_positive = true → p_rc > 0 ∧ p_sc > 0)
    -- check coins_positive => (n_rc_0 > 0 and n_sc_0 > 0)
    ∧ (coins_positive = true → n_rc_0 > 0 ∧ n_sc_0 > 0)
    -- check p_reserve >= 0 and p_sc >= 0 and p_rc >= 0
    ∧ (p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0)
    -- check p_rc > 0 => p_reserve > 0
    ∧ (p_rc > 0 → p_reserve > 0)
    -- check p_sc > 0 => p_reserve div p_sc > 0
    ∧ (p_sc > 0 → Int.ediv p_reserve p_sc > 0)
    -- check i_reserve >= 0 and i_rc >= 0 and i_sc >= 0
    ∧ (i.i_reserve ≥ 0 ∧ i.i_rc ≥ 0 ∧ i.i_sc ≥ 0)
    -- check i_rc > 0 => i_reserve > 0
    ∧ (i.i_rc > 0 → i.i_reserve > 0)
    -- check i_sc > 0 => i_reserve div i_sc > 0
    ∧ (i.i_sc > 0 → Int.ediv i.i_reserve i.i_sc > 0)
    -- check reserve_0 >= 0 and n_rc_0 >= 0 and n_sc_0 >= 0
    ∧ (reserve_0 ≥ 0 ∧ n_rc_0 ≥ 0 ∧ n_sc_0 ≥ 0)
    -- check n_rc_0 > 0 => reserve_0 > 0
    ∧ (n_rc_0 > 0 → reserve_0 > 0)
    -- check n_sc_0 > 0 => reserve_0 div n_sc_0 > 0
    ∧ (n_sc_0 > 0 → Int.ediv reserve_0 n_sc_0 > 0)

#kind (max-depth: 1) (timeout: 45) [theorem7]

end Tests.Stablecoin.Theorem7
