import PlutusCore
import Tests.Smt.Benchmarks.UPLC.Examples.Utils
import Tests.Smt.Benchmarks.UPLC.Examples.Onchain.Ratio

namespace Tests.Uplc.Onchain

open PlutusCore.Integer (Integer)
open UPLC.Uplc

def maxDjedMintingToken : Integer := 1000000000000000000

inductive NormalizedAction where
  | NormalizedSC : Integer → Integer → NormalizedAction
  | NormalizedRC : Integer → Integer → NormalizedAction
  | NormalizedDoubleSell : Integer → Integer → NormalizedAction
  | NormalizedDoubleBuy : Integer → Integer → Integer -> NormalizedAction


-- TODO: Add concrete representation
abbrev BuiltinAddress := Integer
abbrev POSIXTime := Integer
abbrev TxOutRef := Integer

structure NormalizedOrder where
  nrmAction : NormalizedAction
  nrmSubmitter : BuiltinAddress
  nrmRate : Ratio
  nrmTimeStamp : POSIXTime
  nrmTxOutRef : TxOutRef
  nrmAdaInUtxo : Integer

structure ComputeReserve where
  crReserve : Integer
  crN_SC : Integer
  crN_RC : Integer

-- TODO: Update with concrete representation
def addressToBuiltin (addr : BuiltinAddress) : Term := integerToBuiltin addr

-- TODO: Update with concrete representation
def posixTimeToBuiltin (p : POSIXTime) : Term := integerToBuiltin p

-- TODO: Update with concrete representation
def txOutRefToBuiltin (out : TxOutRef) : Term := integerToBuiltin out

def actionToBuiltin : NormalizedAction → Term
| .NormalizedSC n p =>
     Term.Constr 3 [Term.Const (Const.Integer n), Term.Const (Const.Integer p)]
| .NormalizedRC n p =>
     Term.Constr 2 [Term.Const (Const.Integer n), Term.Const (Const.Integer p)]
| .NormalizedDoubleSell m n =>
     Term.Constr 1 [Term.Const (Const.Integer (-m)), Term.Const (Const.Integer (-n))]
| .NormalizedDoubleBuy m n p =>
     Term.Constr 0 [Term.Const (Const.Integer m), Term.Const (Const.Integer n), Term.Const (Const.Integer p)]

def normalizedSCToBuiltin : NormalizedAction → Term
| .NormalizedSC n p =>
     Term.Constr 3 [Term.Const (Const.Integer n), Term.Const (Const.Integer p)]
| _ => Term.Error

def orderToBuiltin (x : NormalizedOrder) : Term :=
  Term.Constr 0
  [ actionToBuiltin x.nrmAction, addressToBuiltin x.nrmSubmitter,
    ratioToConstr x.nrmRate, posixTimeToBuiltin x.nrmTimeStamp,
    txOutRefToBuiltin x.nrmTxOutRef, integerToBuiltin x.nrmAdaInUtxo
  ]

def buySCOrderToBuiltin (x : NormalizedOrder) : Term :=
  Term.Constr 0
  [ normalizedSCToBuiltin x.nrmAction, addressToBuiltin x.nrmSubmitter,
    ratioToConstr x.nrmRate, posixTimeToBuiltin x.nrmTimeStamp,
    txOutRefToBuiltin x.nrmTxOutRef, integerToBuiltin x.nrmAdaInUtxo
  ]

def computeReserveToBuiltin (x : ComputeReserve) : Term :=
  Term.Constr 0 [integerToBuiltin x.crReserve, integerToBuiltin x.crN_SC, integerToBuiltin x.crN_RC]

def validAction (x : NormalizedAction) : Prop :=
  match x with
  | .NormalizedSC n p
  | .NormalizedRC n p => (n < 0 ∧ p = 0) ∨ (n > 0 ∧ p > 0)
  | .NormalizedDoubleSell n m => n < 0 ∧ m < 0
  | .NormalizedDoubleBuy m n p => m > 0 ∧ n > 0 ∧ p > 0

def computeOperatorFees
  (minOpFee : Integer) (maxOpFee : Integer) (opFeeRatio : Ratio) (price : Integer) : Integer :=
  let currentFee := ceil $ fromInteger price * opFeeRatio
  if currentFee < minOpFee
  then minOpFee
  else if currentFee < maxOpFee then currentFee else maxOpFee

def validAdaAtUtxo
  (x : NormalizedOrder) (minAda : Integer) (minOpFee : Integer)
  (maxOpFee : Integer) (opFeeRatio : Ratio) : Prop :=
 match x.nrmAction with
  | .NormalizedSC n p
  | .NormalizedRC n p =>
       if n < 0
       then x.nrmAdaInUtxo > minAda
       else x.nrmAdaInUtxo ≥ computeOperatorFees minOpFee maxOpFee opFeeRatio p + minAda + p
  | .NormalizedDoubleSell _ _ => x.nrmAdaInUtxo > minAda
  | .NormalizedDoubleBuy _ _ p =>
       x.nrmAdaInUtxo ≥ computeOperatorFees minOpFee maxOpFee opFeeRatio p + minAda + p

def validOrder
  (x : NormalizedOrder) (minAda : Integer) (minOpFee : Integer)
  (maxOpFee : Integer) (opFeeRatio : Ratio) : Prop :=
 validAction x.nrmAction ∧
 validRatio x.nrmRate ∧
 zeroRatio < x.nrmRate ∧
 validAdaAtUtxo x minAda minOpFee maxOpFee opFeeRatio


def validReserve (x : ComputeReserve) : Prop :=
 x.crReserve ≥ 0 ∧
 x.crN_SC ≥ 0 ∧
 x.crN_SC ≤ maxDjedMintingToken ∧
 x.crN_RC ≥ 0 ∧
 x.crN_RC ≤ maxDjedMintingToken ∧
 (x.crN_SC > 0 → x.crReserve > 0) ∧
 (x.crN_RC > 0 → x.crReserve > 0)

end Tests.Uplc.Onchain
