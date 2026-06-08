import Lean
import Blaster

namespace Stablecoin

inductive Order where | MintSC | MintRC | NoOrder
deriving BEq, Repr, DecidableEq, Inhabited

inductive Proceed where | MintedSC | MintedRC | RedeemedSC | RedeemedRC | Error | NoReply
deriving BEq, Repr, DecidableEq, Inhabited

inductive ErrorInfo where | Min_Ratio_Violated | Max_Ratio_Violated | Invalid_Mint_Value | None
deriving BEq, Repr, DecidableEq, Inhabited

inductive Stable where | Undefined | Variable | Constant
deriving BEq, Repr, DecidableEq, Inhabited

structure InputMsg where
  order : Order
  qnt   : Int
deriving BEq, Repr, Inhabited

structure OutputMsg where
  ack   : Proceed
  err   : ErrorInfo
  price : Int
deriving BEq, Repr, Inhabited

structure Fees where
  fee_b_sc : Int
  fee_s_sc : Int
  fee_b_rc : Int
  fee_s_rc : Int
deriving BEq, Repr, Inhabited

structure Parameters where
  r_min  : Int
  r_max  : Int
  fees   : Fees
  n_sc_s : Int
  p_min  : Int
deriving BEq, Repr, Inhabited

def PER : Int := 100
def ZERO : Int := 0
def TWOPER : Int := 200

def ErrorCode1 : OutputMsg := { ack := .Error, err := .Min_Ratio_Violated, price := 0 }
def ErrorCode2 : OutputMsg := { ack := .Error, err := .Max_Ratio_Violated, price := 0 }
def ErrorCode3 : OutputMsg := { ack := .Error, err := .Invalid_Mint_Value, price := 0 }
def NullReply  : OutputMsg := { ack := .NoReply, err := .None, price := 0 }

/-- Lustre `min` (named `minR` to avoid clashing with `_root_.min`). -/
def minR (a b : Int) : Int := if a < b then a else b
/-- Lustre `max`. -/
def maxR (a b : Int) : Int := if a < b then b else a
/-- Lustre `abs`. -/
def absR (a : Int) : Int := if a < 0 then -a else a

/-- computeFee: rounds the fee toward +∞ via the +99 trick; `div` → `Int.ediv`. -/
def computeFee (baseFee t_price : Int) : Int :=
  let delta_fee := if t_price > 0 then baseFee - PER else PER - baseFee
  let t_fee := Int.ediv (absR t_price * delta_fee + 99) PER
  t_price + t_fee

end Stablecoin
