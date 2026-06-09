import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem16

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + observer `constant_rate` = (true -> pre constant_rate and rate = pre rate).
    We store `cr_pre` (= constant_rate at the PREVIOUS step) and `p_rate` (= rate at the previous step)
    so that in `invariants` we can recompute current `constant_rate` as `cr_pre && (rate == p_rate)`.
    (This cannot be pre-stored because it depends on the current input `rate`.) -/
structure St where
  core   : CoreState
  cr_pre : Bool   -- constant_rate value at PREVIOUS step
  p_rate : Int    -- rate at PREVIOUS step
deriving BEq, Repr, Inhabited

instance theorem16 : StateMachine Inp St where
  -- step 0: constant_rate = true -> ...; at step 0 it evaluates to `true`.
  --         cr_pre tracks the current constant_rate for use as pre in the next step.
  --         At step 0: constant_rate = true, so cr_pre := true.  p_rate := rate.
  init i := { core := ⟨0, 0, 0⟩, cr_pre := true, p_rate := i.rate }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    -- current constant_rate = s.cr_pre && (i.rate == s.p_rate)
    let cr_cur := s.cr_pre && (i.rate == s.p_rate)
    { core := c, cr_pre := cr_cur, p_rate := i.rate }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve   := c.reserve
    let n_sc      := c.n_sc
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    let p_rc       := s.core.n_rc
    -- Recompute current constant_rate (= true -> pre constant_rate and rate = pre rate)
    let constant_rate := s.cr_pre && (i.rate == s.p_rate)
    -- THEOREM_16: If constant_rate AND n_sc > 0 AND n_rc = 0 THEN reserve >= n_sc * rate * r_min
    ( (constant_rate = true ∧ n_sc > 0 ∧ c.n_rc = 0) → reserve ≥ n_sc * i.rate * params.r_min )
    -- Lemma: o_msg.ack = RedeemedRC => p_reserve > 0
    ∧ ( o_msg.ack = .RedeemedRC → p_reserve > 0 )
    -- Lemma: o_msg.ack = RedeemedRC => p_rc > 0
    ∧ ( o_msg.ack = .RedeemedRC → p_rc > 0 )
    -- Lemma: p_reserve >= 0 and p_sc >= 0 and p_rc >= 0
    ∧ ( p_reserve ≥ 0 ∧ p_sc ≥ 0 ∧ p_rc ≥ 0 )
    -- Lemma: p_rc > 0 => p_reserve > 0
    ∧ ( p_rc > 0 → p_reserve > 0 )
    -- Lemma: p_sc > 0 => p_reserve div p_sc > 0
    ∧ ( p_sc > 0 → Int.ediv p_reserve p_sc > 0 )

#kind (max-depth: 3) (timeout: 30) [theorem16]

end Tests.Stablecoin.Theorem16
