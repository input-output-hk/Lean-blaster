import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

/-! EXPERIMENT (not the faithful artifact — see Theorem9.lean for that).
    Goal: find a hand-supplied strengthening invariant that lets PLAIN k-induction
    close THEOREM_9 (`order_once → reserve > 0`), confirming the only gap vs Kind2 is
    invariant synthesis. We conjoin candidate strengthening lemmas to `invariants`. -/

namespace Tests.Stablecoin.Theorem9Experiment

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

structure St where
  core            : CoreState
  order_once_pre  : Bool
deriving BEq, Repr, Inhabited

/-- V1: original property + structural non-negativity (reserve/n_sc/n_rc ≥ 0 on pre AND post). -/
instance thm9_v1 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩, order_once_pre := false }
  next i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let successful := o_msg.ack != .Error && o_msg.ack != .NoReply && i.i_msg.qnt != 0
    let order_once_now := if successful && !s.order_once_pre then true else s.order_once_pre
    { core := c, order_once_pre := order_once_now }
  -- WALL-1-SOLVED-BY-HAND: assume ALL the reachable structural facts (the invariants
  -- synthesis would discover), so the only thing left to prove is the target. This isolates
  -- Wall 2 (the per-step nonlinear + integer-division arithmetic).
  -- CORRECT SPLIT: paramConstraints is an ENVIRONMENT AXIOM (params is arbitrary; it cannot
  -- be proven, only assumed) → assumptions. The reachable-state facts go in invariants to be PROVEN.
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    let success_now := o_msg.ack != .Error && o_msg.ack != .NoReply && i.i_msg.qnt != 0
    let order_once_now := if success_now && !s.order_once_pre then true else s.order_once_pre
    (order_once_now = true → c.reserve > 0)
    -- Strengthening lemmas — now PROVEN as invariants (not trusted)
    ∧ (s.core.reserve ≥ 0 ∧ s.core.n_sc ≥ 0 ∧ s.core.n_rc ≥ 0)
    ∧ (s.core.n_sc > 0 → s.core.reserve > 0) ∧ (s.core.n_rc > 0 → s.core.reserve > 0)
    ∧ (s.core.n_sc > 0 → price_sc s.core.reserve s.core.n_sc i.rate * s.core.n_sc ≤ s.core.reserve)
    ∧ (equity s.core.reserve s.core.n_sc i.rate ≥ 0)
    -- the inductive hypothesis itself: the property on the PRE-state (excludes the
    -- unreachable (0,0,0, order_once=true) CTI). This is what induction must carry.
    ∧ (s.order_once_pre = true → s.core.reserve > 0)

#kind (max-depth: 1) (timeout: 20) [thm9_v1]

end Tests.Stablecoin.Theorem9Experiment
