import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

namespace Tests.Stablecoin.Theorem5

-- Theorem5: No Bank Runs for StableCoins (selling price per SC is non-decreasing under constant rate).
-- Local type: SCSellerType
-- Observers: constant_rate = true -> pre constant_rate and rate = pre rate
--            p_seller = defaultSeller_SC -> pre c_seller
--            c_seller = update_SCSeller(p_reserve, p_sc, rate, o_msg, p_seller)
-- --unroll_max 3

/-- Tracks selling history: whether any SC was sold and at what price. -/
structure SCSellerType where
  sold_once    : Bool
  price_per_sc : Int
deriving BEq, Repr, Inhabited

def defaultSeller_SC : SCSellerType := { sold_once := false, price_per_sc := 0 }

/-- update_SCSeller: if o_msg redeemed SC, record the sale; otherwise keep previous seller info. -/
def update_SCSeller (p_reserve p_sc rate : Int) (o_msg : OutputMsg) (seller : SCSellerType) : SCSellerType :=
  if o_msg.ack = .RedeemedSC then
    { sold_once := true, price_per_sc := minR (Int.ediv p_reserve p_sc) rate }
  else
    seller

structure Inp where
  i_msg : InputMsg
  rate  : Int
deriving BEq, Repr, Inhabited

/-- State = bank pre-state + constant_rate observer (stored as cr_pre + p_rate) + p_seller observer.
    `cr_pre` at step 0 = true (constant_rate at step 0 = true -> branch).
    `p_rate` at step 0 = rate of step 0.
    In `invariants`, RECOMPUTE `constant_rate = s.cr_pre && (i.rate == s.p_rate)` (current step).
    `p_seller` at step 0 = defaultSeller_SC; at k+1 = c_seller from step k. -/
structure St where
  core     : CoreState
  cr_pre   : Bool          -- constant_rate at PREVIOUS step
  p_rate   : Int           -- rate at PREVIOUS step
  p_seller : SCSellerType
deriving BEq, Repr, Inhabited

instance theorem5 : StateMachine Inp St where
  init i := { core := ⟨0, 0, 0⟩, cr_pre := true, p_rate := i.rate,
              p_seller := defaultSeller_SC }
  next i s :=
    let (o_msg, c) := stepStableCoin i.i_msg i.rate s.core
    -- constant_rate at THIS step (will be stored as cr_pre for next step)
    let cr_cur   := s.cr_pre && (i.rate == s.p_rate)
    let c_seller := update_SCSeller s.core.reserve s.core.n_sc i.rate o_msg s.p_seller
    { core     := c
      cr_pre   := cr_cur
      p_rate   := i.rate
      p_seller := c_seller }
  assumptions _ _ := paramConstraints
  invariants i s :=
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let p_reserve  := s.core.reserve
    let p_sc       := s.core.n_sc
    -- Recompute current constant_rate = true -> pre constant_rate and rate = pre rate
    let constant_rate := s.cr_pre && (i.rate == s.p_rate)
    let p_seller   := s.p_seller
    let c_seller   := update_SCSeller p_reserve p_sc i.rate o_msg p_seller
    -- THEOREM_5: No Bank Runs for StableCoins
    (constant_rate = true ∧ p_seller.sold_once = true ∧ o_msg.ack = .RedeemedSC →
       c_seller.price_per_sc ≥ p_seller.price_per_sc)
    -- Lemma: sold_once => price_per_sc <= rate
    ∧ (constant_rate = true ∧ p_seller.sold_once = true →
       p_seller.price_per_sc ≤ i.rate)
    -- Lemma: sold_once and p_sc > 0 => price_per_sc <= min(p_reserve div p_sc, rate)
    ∧ (constant_rate = true ∧ p_seller.sold_once = true ∧ p_sc > 0 →
       p_seller.price_per_sc ≤ minR (Int.ediv p_reserve p_sc) i.rate)

#kind (max-depth: 1) (timeout: 30) [theorem5]

end Tests.Stablecoin.Theorem5
