import Tests.Smt.Benchmarks.UPLC.Uplc
import Tests.Smt.Benchmarks.UPLC.Examples.Onchain.Action

namespace Tests.Uplc.Onchain
open PlutusCore.Integer (Integer)
open UPLC.CekValue (CekValue)
open UPLC.Uplc

structure ProcessSCInput where
  scMinRatio : Ratio
  scMinOperatorFee : Integer
  scMaxOperatorFee : Integer
  scOperatorFeeRatio : Ratio
  scBaseFeeBSC : Ratio
  scBaseFeeSSC : Ratio
  nbTokens : Integer
  totalPrice : Integer
  orderSubmitter : BuiltinAddress
  orderRate : Ratio
  orderTimeStamp : POSIXTime
  orderTxOutRef : TxOutRef
  adaAtOrderUtxo : Integer
  minAdaTransfer : Integer
  state : ComputeReserve


def toNormalizedOrder (x : ProcessSCInput) : NormalizedOrder :=
  { nrmAction := .NormalizedSC x.nbTokens x.totalPrice,
    nrmSubmitter := x.orderSubmitter,
    nrmRate := x.orderRate,
    nrmTimeStamp := x.orderTimeStamp,
    nrmTxOutRef := x.orderTxOutRef,
    nrmAdaInUtxo := x.adaAtOrderUtxo
  }

def validOrderInput (x : ProcessSCInput) : Prop :=
  validRatio x.scMinRatio ∧
  validRatio x.scOperatorFeeRatio ∧
  validRatio x.scBaseFeeBSC ∧
  validRatio x.scBaseFeeSSC ∧
  zeroRatio < x.scMinRatio ∧
  x.scMinRatio ≤ (fromInteger 4) ∧
  x.scMinOperatorFee > 0 ∧
  x.scMaxOperatorFee ≥ x.scMinOperatorFee ∧
  zeroRatio < x.scOperatorFeeRatio ∧
  x.scOperatorFeeRatio ≤ oneRatio ∧
  oneRatio < x.scBaseFeeBSC ∧
  x.scBaseFeeBSC ≤ (fromInteger 2) ∧
  zeroRatio ≤ x.scBaseFeeSSC ∧
  x.scBaseFeeSSC < oneRatio ∧
  x.scBaseFeeBSC < x.scMinRatio ∧
  x.minAdaTransfer > 0 ∧
  validReserve x.state ∧
  validOrder (toNormalizedOrder x) x.minAdaTransfer x.scMinOperatorFee x.scMaxOperatorFee x.scOperatorFeeRatio

def orderInputToParams (x : ProcessSCInput) : List Term :=
  [ ratioToConstr x.scMinRatio, integerToBuiltin x.scMinOperatorFee,
    integerToBuiltin x.scMaxOperatorFee, ratioToConstr x.scOperatorFeeRatio,
    ratioToConstr x.scBaseFeeBSC, ratioToConstr x.scBaseFeeSSC,
    orderToBuiltin (toNormalizedOrder x), integerToBuiltin x.minAdaTransfer,
    computeReserveToBuiltin x.state ]

def isBuySCOrder (x : ProcessSCInput) : Prop := x.nbTokens > 0

def isSellSCOrder (x : ProcessSCInput) : Prop := x.nbTokens < 0

def resultToComputeReserve (result : Option CekValue) : Option ComputeReserve :=
  match result with
  | some (.VConstr 1
           [.VConstr 0
             [ .VCon (Const.Integer reserve)
               , .VCon (Const.Integer n_sc)
               , .VCon (Const.Integer n_rc)
             ]
           ]) => some {crReserve := reserve, crN_SC := n_sc, crN_RC := n_rc }
  | _ => none

def successfulOrderImpliesPredicate (result : Option CekValue) (p : ComputeReserve → Prop) : Prop :=
  match (resultToComputeReserve result) with
  | some newState => p newState
  | none => True


def isInvalidMinReserveStatus (result : Option CekValue) : Prop :=
  match result with
  | some (.VConstr 0 [.VCon $ Const.Data $ .Constr 0 [.I _allowed, .I _actual]]) => True
      -- Left $ InvalidMinReserve allowed actual
  | _ => False

def isSuccessfulOrder (result : Option CekValue) : Prop :=
  (resultToComputeReserve result).isSome


def isMaxStablecoinMintingReachedStatus (result : Option CekValue) : Prop :=
  match result with
  | some (.VConstr 0 [.VCon $ Const.Data $ .Constr 7 []]) => True
      -- Left $ MaxStablecoinMintingReached
  | _ => False

def isInsufficientOperatorFees (result : Option CekValue) : Prop :=
  match result with
  | some (.VConstr 0 [.VCon $ Const.Data $ .Constr 10 [.I _expected, .I _current]]) => True
      -- Left $ InsufficientOperatorFees expected current
  | _ => False

def validMinRatioViolation (x : ProcessSCInput) : Prop :=
  let totalPrice := fromInteger x.nbTokens * (x.orderRate * x.scBaseFeeBSC)
  let minReserve := fromInteger (x.state.crN_SC + x.nbTokens) * x.orderRate * x.scMinRatio
  let currentReserve := fromInteger x.state.crReserve + totalPrice
  currentReserve < minReserve

def validMaxMintingViolation (x : ProcessSCInput) : Prop :=
  x.state.crN_SC + x.nbTokens > maxDjedMintingToken

def basePriceSC (x : ProcessSCInput) : Ratio :=
  if x.state.crN_SC = 0
  then x.orderRate
  else if x.state.crN_RC = 0
       then mkRatio x.state.crReserve x.state.crN_SC
       else fromInteger x.state.crReserve * (unsafeRecip $ fromInteger x.state.crN_SC * x.scBaseFeeBSC)

def priceSC (x : ProcessSCInput) : Ratio :=
  let reserve_p := basePriceSC x
  if x.orderRate.lt reserve_p
  then x.orderRate
  else reserve_p

def validBuySC (x : ProcessSCInput) (newState : ComputeReserve) : Prop :=
  let totalPrice := ceil $ fromInteger x.nbTokens * (x.orderRate * x.scBaseFeeBSC)
  let minReserve := fromInteger (x.state.crN_SC + x.nbTokens) * x.orderRate * x.scMinRatio
  newState.crReserve = x.state.crReserve + totalPrice ∧
  fromInteger newState.crReserve ≥ minReserve ∧
  newState.crN_SC = x.state.crN_SC + x.nbTokens ∧
  newState.crN_SC ≤ maxDjedMintingToken ∧
  newState.crN_RC = x.state.crN_RC


def priceSCWithFees (x : ProcessSCInput) : Ratio :=
   priceSC x * x.scBaseFeeBSC

def scForFees (x : ProcessSCInput) (adaForOrder : Integer) (n : Integer) : Integer :=
  let price_with_fee := priceSCWithFees x
  if adaForOrder < x.scMinOperatorFee then 0
  else if zeroRatio.lt price_with_fee
       then truncate $ fromInteger adaForOrder * (recip $ price_with_fee * x.scOperatorFeeRatio)
       else n

def totalSellSCPrice (x : ProcessSCInput) (n : Integer) : Integer :=
    truncate $ fromInteger n * priceSCWithFees x

def effectiveFees (x : ProcessSCInput) (exact_fees : Integer) : Integer :=
  if exact_fees < x.scMinOperatorFee
  then x.scMinOperatorFee
  else if exact_fees < x.scMaxOperatorFee
       then exact_fees
       else x.scMaxOperatorFee

def operatorFees (x : ProcessSCInput) (totalPrice : Integer) : Integer :=
  let exact_fees := ceil $ fromInteger totalPrice * x.scOperatorFeeRatio
  effectiveFees x exact_fees

def validSellSC (x : ProcessSCInput) (newState : ComputeReserve) : Prop :=
  let n := -x.nbTokens
  let adaForOrder := x.adaAtOrderUtxo - x.minAdaTransfer
  let n' := if operatorFees x (totalSellSCPrice x n) > adaForOrder
            then scForFees x adaForOrder n
            else n
  let totalPrice := totalSellSCPrice x n'
  newState.crReserve = x.state.crReserve - totalPrice ∧
  n' > 0 ∧
  n' ≤ n ∧
  adaForOrder ≥ operatorFees x totalPrice ∧
  ( n' < n → operatorFees x (totalSellSCPrice x (n' + 1)) ≥ adaForOrder ) ∧
  newState.crN_SC = x.state.crN_SC - n' ∧
  newState.crN_RC = x.state.crN_RC


def validInsufficientFeesForSellSC (x : ProcessSCInput) : Prop :=
  let price_with_fee := priceSCWithFees x
  let providedFees := x.adaAtOrderUtxo - x.minAdaTransfer
  let currentFeesForOneSC := effectiveFees x (ceil $ price_with_fee * x.scOperatorFeeRatio)
  providedFees < currentFeesForOneSC

end Tests.Uplc.Onchain
