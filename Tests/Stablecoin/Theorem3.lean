import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem3

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + observer `p_rate` (= previous step's rate).
    Framework pairing (KInduction.lean / BMC.lean):
      `st₀ = init in₀`, `stₖ = next inₖ₋₁ stₖ₋₁`, invariant checked as `invariants inₖ stₖ`.
    `st.core` holds the bank PRE-state at step k (= `p_reserve, p_sc, p_rc` in StableCoin_InitState);
    the invariant recomputes the current (post) bank state via `stepStableCoin`. -/
structure St where
  core   : CoreState
  p_rate : Int
deriving BEq, Repr, Inhabited

instance theorem3 : StateMachine Inp St where
  -- step 0: pre-state = (0,0,0) (StableCoin instantiates StableCoin_InitState(ZERO,ZERO,ZERO,...));
  --         `p_rate = rate -> pre rate` so at step 0 p_rate = rate.
  init i := { core := ⟨0, 0, 0⟩, p_rate := i.rate }
  -- pre-state for the NEXT step = THIS step's post bank state; p_rate for NEXT step = THIS step's rate.
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c, p_rate := i.rate }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    let reserve := c.reserve
    let n_sc := c.n_sc
    let rate := i.rate
    let p_rate := s.p_rate
    ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate ∧
        (rate - p_rate) * reserve ≤ (reserve - n_sc * p_rate) * rate) →
          price_sc reserve n_sc rate = rate )
    ∧ ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate ∧
        (rate - p_rate) * reserve ≤ (reserve - n_sc * p_rate) * rate) →
          reserve ≥ n_sc * rate )
    ∧ ( (n_sc > 0 ∧ p_rate > 0 ∧ rate > p_rate ∧ reserve > n_sc * p_rate) →
          (reserve - n_sc * p_rate) * rate > 0 )

#kind (max-depth: 3) (timeout: 60) [theorem3]

end Tests.Stablecoin.Theorem3
