import Lean
import Blaster
import Stablecoin.Base
import Stablecoin.Params

namespace Stablecoin

/-- The bank state (reserve, number of stablecoins, number of reserve coins). -/
structure CoreState where
  reserve : Int
  n_sc    : Int
  n_rc    : Int
deriving BEq, Repr, Inhabited

/-- equity = reserve - min(reserve, n_sc*rate), expressed as the source's if-form. -/
def equity (reserve n_sc rate : Int) : Int :=
  if reserve > n_sc * rate then reserve - (n_sc * rate) else ZERO

def price_sc (reserve n_sc rate : Int) : Int :=
  if n_sc > ZERO then
    (if reserve ≥ n_sc * rate then rate else Int.ediv reserve n_sc)
  else rate

def price_rc (d_rc reserve n_sc n_rc rate : Int) : Int :=
  if n_rc = ZERO then params.p_min
  else if d_rc ≥ ZERO then maxR (Int.ediv (equity reserve n_sc rate) n_rc) params.p_min
  else Int.ediv (equity reserve n_sc rate) n_rc

def mintSC (d_sc rate reserve n_sc : Int) : OutputMsg :=
  let s_price := price_sc reserve n_sc rate * d_sc
  let b_fee := if d_sc ≥ ZERO then params.fees.fee_b_sc else params.fees.fee_s_sc
  let t_price := computeFee b_fee s_price
  let t_reserve := reserve + t_price
  if d_sc ≥ ZERO then
    if rate > ZERO ∧ t_reserve ≥ (n_sc + d_sc) * rate * params.r_min then
      { ack := .MintedSC, err := .None, price := t_price }
    else ErrorCode1
  else if -d_sc ≤ n_sc ∧ rate > ZERO then
    { ack := .RedeemedSC, err := .None, price := t_price }
  else ErrorCode3

def mintRC (d_rc rate reserve n_sc n_rc : Int) : OutputMsg :=
  let r_price := price_rc d_rc reserve n_sc n_rc rate * d_rc
  let b_fee := if d_rc ≥ ZERO then params.fees.fee_b_rc else params.fees.fee_s_rc
  let t_price := computeFee b_fee r_price
  let t_reserve := reserve + t_price
  if d_rc ≥ ZERO then
    if n_sc < params.n_sc_s ∨ t_reserve ≤ n_sc * rate * params.r_max then
      { ack := .MintedRC, err := .None, price := t_price }
    else ErrorCode2
  else if -d_rc ≤ n_rc then
    if n_sc = ZERO ∨ (rate > ZERO ∧ t_reserve ≥ n_sc * rate * params.r_min) then
      { ack := .RedeemedRC, err := .None, price := t_price }
    else ErrorCode1
  else ErrorCode3

/-- One transition step (the `StableCoin_InitState` body). Given the previous bank
    state `p` (= `(p_reserve, p_sc, p_rc)`) and the input, returns `(output, new state)`. -/
def stepStableCoin (i_msg : InputMsg) (rate : Int) (p : CoreState) : OutputMsg × CoreState :=
  let o_msg :=
    if i_msg.order = .NoOrder then NullReply
    else if i_msg.order = .MintSC then mintSC i_msg.qnt rate p.reserve p.n_sc
    else mintRC i_msg.qnt rate p.reserve p.n_sc p.n_rc
  let reserve := if o_msg.ack = .Error then p.reserve else p.reserve + o_msg.price
  let n_sc := if o_msg.ack = .MintedSC ∨ o_msg.ack = .RedeemedSC then p.n_sc + i_msg.qnt else p.n_sc
  let n_rc := if o_msg.ack = .MintedRC ∨ o_msg.ack = .RedeemedRC then p.n_rc + i_msg.qnt else p.n_rc
  (o_msg, { reserve := reserve, n_sc := n_sc, n_rc := n_rc })

end Stablecoin
