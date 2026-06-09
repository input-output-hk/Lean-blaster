import Stablecoin.Base
import Stablecoin.Params
import Stablecoin.StableCoin
import Blaster.StateMachine

open Stablecoin Blaster.StateMachine

-- Types for modeling secondary market (from Theorem1_and_2.lus)
inductive MarketAction where | BuyOffer | SellOffer | NoOffer
deriving BEq, Repr, DecidableEq, Inhabited

structure SecondaryMarket where
  action : MarketAction
  price  : Int
deriving BEq, Repr, Inhabited

namespace Tests.Stablecoin.Theorem1and2

structure Inp where
  i_msg        : InputMsg
  rate         : Int
  rational_user : Bool
  s_market     : SecondaryMarket
deriving BEq, Repr, Inhabited

structure St where
  core : CoreState
deriving BEq, Repr, Inhabited

instance theorem12 : StateMachine Inp St where
  init _ := { core := ⟨0, 0, 0⟩ }
  next i s :=
    let (_, c) := stepStableCoin i.i_msg i.rate s.core
    { core := c }
  assumptions i s :=
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    paramConstraints ∧
    -- Assert 1: rational user buys SC from bank if secondary market sells SC cheaply
    ((i.rational_user = true ∧ i.s_market.action = .SellOffer ∧
      computeFee params.fees.fee_b_sc (price_sc p_reserve p_sc i.rate) ≤ i.s_market.price) →
        (i.i_msg.order = .MintSC ∧ i.i_msg.qnt > 0)) ∧
    -- Assert 2: rational user does not buy SC from bank if secondary market sells SC at higher price
    ((i.rational_user = true ∧ i.s_market.action = .SellOffer ∧
      computeFee params.fees.fee_b_sc (price_sc p_reserve p_sc i.rate) > i.s_market.price) →
        i.i_msg.order = .NoOrder) ∧
    -- Assert 3: rational user sells SC to bank if secondary market buys SC at lower price
    ((i.rational_user = true ∧ i.s_market.action = .BuyOffer ∧
      (-(computeFee params.fees.fee_s_sc (price_sc p_reserve p_sc i.rate * (-1)))) > i.s_market.price) →
        (i.i_msg.order = .MintSC ∧ i.i_msg.qnt < 0)) ∧
    -- Assert 4: rational user does not sell SC to bank if secondary market buys SC at sufficient price
    ((i.rational_user = true ∧ i.s_market.action = .BuyOffer ∧
      (-(computeFee params.fees.fee_s_sc (price_sc p_reserve p_sc i.rate * (-1)))) ≤ i.s_market.price) →
        i.i_msg.order = .NoOrder)
  invariants i s :=
    let p_reserve := s.core.reserve
    let p_sc      := s.core.n_sc
    let (o_msg, _) := stepStableCoin i.i_msg i.rate s.core
    let sufficient_reserve := p_reserve + i.i_msg.qnt * i.rate ≥ (p_sc + i.i_msg.qnt) * i.rate * params.r_min
    -- THEOREM_1: Peg Maintenance - Upper Bound
    ((i.rational_user = true ∧
      sufficient_reserve ∧
      i.rate > 0 ∧
      i.s_market.action = .SellOffer ∧
      i.s_market.price > computeFee params.fees.fee_b_sc (price_sc p_reserve p_sc i.rate)) →
        o_msg.ack = .MintedSC) ∧
    -- THEOREM_2: Peg Maintenance - Lower Bound
    ((i.rational_user = true ∧
      p_reserve ≥ p_sc * i.rate ∧
      i.rate > 0 ∧
      (-i.i_msg.qnt) ≤ p_sc ∧
      i.s_market.action = .BuyOffer ∧
      i.s_market.price < (-(computeFee params.fees.fee_s_sc (price_sc p_reserve p_sc i.rate * (-1))))) →
        o_msg.ack = .RedeemedSC)

#bmc (max-depth: 1) (timeout: 60) [theorem12]
#kind (max-depth: 1) (timeout: 60) [theorem12]

end Tests.Stablecoin.Theorem1and2
