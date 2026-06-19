import Lean
import Blaster.Optimize.Rewriting.OptimizeITE
import Blaster.Optimize.Telescope
import Blaster.Smt.Env
import Blaster.Smt.Translate.Match
import Blaster.Smt.Translate.Quantifier
import Blaster.SmtArray


open Lean Meta Blaster.Optimize

namespace Blaster.Smt

/-- Generate an smt symbol from a given function  name. -/
def funNameToSmtSymbol (funName : Name) : SmtSymbol :=
  mkNormalSymbol s!"@{funName}"


/-- list of Lean operators expected to be fully applied at translation phase. -/
def fullyAppliedConst : NameHashSet :=
  List.foldr (fun c s => s.insert c) Std.HashSet.emptyWithCapacity
  [ ``And,
    ``Or,
    ``Not,
    ``Int.add,
    ``Int.neg,
    ``Int.mul,
    ``Int.toNat,
    ``Int.tdiv,
    ``Int.tmod,
    ``Int.fdiv,
    ``Int.fmod,
    ``Int.ediv,
    ``Int.emod,
    ``Int.pow,
    ``and,
    ``or,
    ``not,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.pow,
    ``BitVec.add,
    ``BitVec.sub,
    ``BitVec.mul,
    ``BitVec.neg,
    ``BitVec.and,
    ``BitVec.or,
    ``BitVec.xor,
    ``BitVec.not,
    ``BitVec.ult,
    ``BitVec.ule,
    ``BitVec.slt,
    ``BitVec.sle,
    ``BitVec.udiv,
    ``BitVec.umod,
    ``BitVec.sdiv,
    ``BitVec.smod,
    ``BitVec.srem,
    ``BitVec.append,
    ``String.append,
    ``String.length,
    ``String.replace
  ]

/-- Return `true` when `e` corresponds to one of the following:
     - `e := Prop`; or
     - `e := α₁ → ... → αₙ → Prop`;
    Assume that `e` does not contain any let expression.
-/
def isArrowPropType (e : Expr) : Bool :=
  (Expr.getForallBody e).isProp


/-- Return `true` when `indName` corresponds to an inductive predicate. -/
def isInductivePredicate (indName : Name) : TranslateEnvT Bool := do
  let ConstantInfo.inductInfo indVal ← getConstEnvInfo indName | return false
  return isArrowPropType indVal.type


/-- Given `f x₁ ... xₙ` a function instance and `sid` a unique smt identifier for `f x₁ ... xₙ`,
    add entry `f x₁ ... xₙ := sid` to `funInstCache`.
-/
def updateFunInstCacheBase (f : Expr) (sid : SmtQualifiedIdent) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.funInstCache := env.smtEnv.funInstCache.insert f sid})

/-- Same as `updateFunInstCacheBase` but accepts an SmtSymbol as argument and returns
    the SmtQualifiedIdent instance added to `funInstCache`.
-/
def updateFunInstCache (f : Expr) (sid : SmtSymbol) : TranslateEnvT SmtQualifiedIdent := do
  let smtId := .SimpleIdent sid
  updateFunInstCacheBase f smtId
  return smtId

/-- Perform the following actions:
     - Return `SimpleIdent "Nat.sub"` when entry `n := SimpleIdent "Nat.sub"` exists in `funInstCache`
     - Otherwise:
        - define Nat sort (if necessary)
        - define Nat.sub Smt function (i.e., see `defineNatSub`)
        - add entry `n := SimpleIdent "Nat.sub"` to `funInstCache`
        - return `SimpleIdent "Nat.sub"`
  Assume that `n := Expr.const ``Nat.sub []`.
-/
def translateNatSub (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    discard $ translateNatType (← mkNatType)
    defineNatSub
    updateFunInstCache n natSubSymbol
 | some smtId => return smtId

/-- Perform the following actions:
     - Return `SimpleIdent "@Int.ediv"` when entry `f := SimpleIdent "@Int.ediv"` exists in `funInstCache`
     - Otherwise:
        - define @Int.ediv Smt function (i.e., see `defineIntEDiv`)
        - add entry `f := SimpleIdent "@Int.ediv"` to `funInstCache`
        - add entry `f' := SimpleIdent "@Int.ediv"` to `funInstCache` with:
              - f' := Expr.const `Nat.div _  if `f := Expr.const ``Int.ediv _`
              - f' := Expr.const `@Int.ediv _ otherwise
        - return `SimpleIdent "@Int.ediv"`
  Assume that `f := Expr.const ``Int.ediv []` or `f := Expr.const ``Nat.div []`.
-/
def translateIntEDiv (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? f with
 | none =>
    defineIntEDiv
    let smtId ← updateFunInstCache f edivSymbol
    updateFunInstCacheBase (← toEDivAlias f) smtId
    return smtId
 | some smtId => return smtId

 where
   toEDivAlias (f : Expr) : TranslateEnvT Expr := do
     let Expr.const n _ := f | throwEnvError "toEDivAlias: name expression expected but got {reprStr f}"
     match n with
     | ``Int.ediv => mkNatDivOp
     | ``Nat.div => mkIntEDivOp
     | _ => throwEnvError "toEDivAlias: unexpected div operator {n}"


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.emod"` when entry `f := SimpleIdent "@Int.emod"` exists in `funInstCache`
     - Otherwise:
        - define @Int.emod Smt function (i.e., see `defineIntEMod`)
        - add entry `f := SimpleIdent "@Int.emod"` to `funInstCache`
        - add entry `f' := SimpleIdent "@Int.emod"` to `funInstCache` with:
              - f' := Expr.const `Nat.mod _  if `f := Expr.const ``Int.emod _`
              - f' := Expr.const `@Int.emod _ otherwise
        - return `SimpleIdent "@Int.emod"`
  Assume that `f := Expr.const ``Int.emod []` or f := `Expr.const ``Nat.mod []`
-/
def translateIntEMod (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? f with
 | none =>
    defineIntEMod
    let smtId ← updateFunInstCache f emodSymbol
    updateFunInstCacheBase (← toEModAlias f) smtId
    return smtId
 | some smtId => return smtId

 where
   toEModAlias (f : Expr) : TranslateEnvT Expr := do
     let Expr.const n _ := f | throwEnvError "toEModAlias: name expression expected but got {reprStr f}"
     match n with
     | ``Int.emod => mkNatModOp
     | ``Nat.mod => mkIntEModOp
     | _ => throwEnvError "toEModAlias: unexpected mod operator {n}"


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.tdiv"` when entry `n := SimpleIdent "@Int.tdiv"` exists in `funInstCache`
     - Otherwise:
        - define @Int.tdiv Smt function (i.e., see `defineIntTDiv`)
        - add entry `n := SimpleIdent "@Int.tdiv"` to `funInstCache`
        - return `SimpleIdent "@Int.tdiv"`
  Assume that `n := Expr.const ``Int.tdiv []`.
-/
def translateIntTDiv (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    defineIntTDiv
    updateFunInstCache n tdivSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.tmod"` when entry `n := SimpleIdent "@Int.tmod"` exists in `funInstCache`
     - Otherwise:
        - define @Int.tmod Smt function (i.e., see `defineIntTMod`)
        - add entry `n := SimpleIdent "@Int.tmod"` to `funInstCache`
        - return `SimpleIdent "@Int.tmod"`
  Assume that `n := Expr.const ``Int.tmod []`.
-/
def translateIntTMod (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    defineIntTMod
    updateFunInstCache n tmodSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.fdiv"` when entry `n := SimpleIdent "@Int.fdiv"` exists in `funInstCache`
     - Otherwise:
        - define @Int.fdiv Smt function (i.e., see `defineIntFDiv`)
        - add entry `n := SimpleIdent "@Int.fdiv"` to `funInstCache`
        - return `SimpleIdent "@Int.fdiv"`
  Assume that `n := Expr.const ``Int.fdiv []`.
-/
def translateIntFDiv (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    defineIntFDiv
    updateFunInstCache n fdivSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.fmod"` when entry `n := SimpleIdent "@Int.fmod"` exists in `funInstCache`
     - Otherwise:
        - define @Int.fmod Smt function (i.e., see `defineIntFMod`)
        - add entry `n := SimpleIdent "@Int.fmod"` to `funInstCache`
        - return `SimpleIdent "@Int.fmod"`
  Assume that `n := Expr.const ``Int.fmod []`.
-/
def translateIntFMod (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    defineIntFMod
    updateFunInstCache n fmodSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.pow"` when entry `f := SimpleIdent "@Int.pow"` exists in `funInstCache`
     - Otherwise:
        - define Nat.sub function (if necessary)
        - define @Int.pow Smt function (i.e., see `defineIntPow`)
        - add entry `f := SimpleIdent "@Int.pow"` to `funInstCache`
        - return `SimpleIdent "@Int.pow"`
  Assume that `f := Expr.const ``Int.pow []`
-/
def translateIntPow (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? f with
 | none =>
    discard $ translateNatSub (mkConst ``Nat.sub)
    defineIntPow
    let smtId ← updateFunInstCache f intPowSymbol
    return smtId
 | some smtId => return smtId

/-- Perform the following actions:
     - Return `SimpleIdent "@Nat.pow"` when entry `f := SimpleIdent "@Nat.pow"` exists in `funInstCache`
     - Otherwise:
        - define Nat.sub function (if necessary)
        - define @Nat.pow Smt function (i.e., see `defineNatPow`)
        - add entry `f := SimpleIdent "@Nat.pow"` to `funInstCache`
        - return `SimpleIdent "@Nat.pow"`
  Assume that `f := `Expr.const ``Nat.pow []`
-/
def translateNatPow (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? f with
 | none =>
    discard $ translateNatSub (mkConst ``Nat.sub)
    defineNatPow
    let smtId ← updateFunInstCache f natPowSymbol
    return smtId
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@Int.toNat"` when entry `n := SimpleIdent "@Int.toNat"` exists in `funInstCache`
     - Otherwise:
        - define Nat sort (if necessary)
        - define @Int.toNat Smt function (i.e., see `defineInttoNat`)
        - add entry `n := SimpleIdent "@Int.toNat"` to `funInstCache`
        - return `SimpleIdent "@Int.toNat"`
  Assume that `n := Expr.const ``Int.toNat []`.
-/
def translateInttoNat (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.get? n with
 | none =>
    discard $ translateNatType (← mkNatType)
    defineInttoNat
    updateFunInstCache n toNatSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "@BitVec.udiv_w"` (resp. `"@BitVec.sdiv_w"`) when entry
       `f w := SimpleIdent "@BitVec.udiv_w"` (resp. `"@BitVec.sdiv_w"`) exists in `funInstCache`
     - Otherwise:
        - define `@BitVec.udiv_w` (resp. `@BitVec.sdiv_w`) Smt wrapper (see `defineBitVecUDiv`/`defineBitVecSDiv`)
        - add entry `f w := SimpleIdent "@BitVec.udiv_w"` (resp. `"@BitVec.sdiv_w"`) to `funInstCache`
        - return `SimpleIdent "@BitVec.udiv_w"` (resp. `"@BitVec.sdiv_w"`)
  Assume that `f := Expr.const ``BitVec.udiv _` or `f := Expr.const ``BitVec.sdiv _`.
  An error is triggered when `args.size != 3` or when the width is not a Nat literal.
-/
def translateBitVecWrappedDiv (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT SmtQualifiedIdent := do
  if args.size != 3 then
    throwEnvError "translateBitVecWrappedDiv: fully applied {n} expected but got {args.size} arguments"
  let some w := isNatValue? args[0]!
    | throwEnvError "translateBitVecWrappedDiv: literal width expected for {n} but got {reprStr args[0]!}"
  let instApp := mkApp f args[0]!
  match (← get).smtEnv.funInstCache.get? instApp with
  | some smtId => return smtId
  | none =>
      if n == ``BitVec.udiv then
        defineBitVecUDiv w
        updateFunInstCache instApp (bitvecUDivSymbol w)
      else
        defineBitVecSDiv w
        updateFunInstCache instApp (bitvecSDivSymbol w)

/-- Return `stₙ` when entry `f := stₙ` exists in `funInstCache`.
    Otherwise:
     - add entry `f := SimpleIdent s` to `funInstCache`
     - return `SimpleIdent s`
-/
def getOpaqueSmtEquivFun (f : Expr) (s : SmtSymbol) : TranslateEnvT SmtQualifiedIdent := do
  match (← get).smtEnv.funInstCache.get? f with
  | none => updateFunInstCache f s
  | some smtId => return smtId

/-- Given `f` a name expression for which a corresponding smt operator exists and `n`
    its corresponding name, and `args` the effective parameters for `f`,
    perform the following actions:
     - When `f := stₙ` exists in `funInstCache`
        - return stₙ
     - When no entry for `f` exists in `funInstCache`
        - add entry `f := SimpleIdent (smtSymbolFor f)` to `funInstCache`
        - define corresponding smt function only when `hasSmtDefinedOperator f`
        - return `SimpleIdent (smtSymbolFor f)`

    An error is triggered
      - when `n` corresponds to one of the opaque functions:
        - Exists
        - Blaster.decide'
        - Iff
        - Int.le
        - Nat.beq
        - Nat.ble
        - Nat.pred
        - Nat.le
      - when `args.size == 0` for `Lt.lt`

-/
def translateOpaqueFun (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT SmtQualifiedIdent := do
  match n with
  | ``Eq
  | ``BEq.beq => getOpaqueSmtEquivFun f eqSymbol
  | ``And
  | ``and => getOpaqueSmtEquivFun f andSymbol
  | ``Or
  | ``or => getOpaqueSmtEquivFun f orSymbol
  | ``Not
  | ``not => getOpaqueSmtEquivFun f notSymbol
  | ``Blaster.dite' => getOpaqueSmtEquivFun f iteSymbol
  | ``Int.add
  | ``Nat.add => getOpaqueSmtEquivFun f addSymbol
  | ``Int.neg => getOpaqueSmtEquivFun f subSymbol
  | ``Int.mul
  | ``Nat.mul => getOpaqueSmtEquivFun f mulSymbol
  | ``Int.toNat => translateInttoNat f
  | ``Int.tdiv => translateIntTDiv f
  | ``Int.tmod => translateIntTMod f
  | ``Int.fdiv => translateIntFDiv f
  | ``Int.fmod => translateIntFMod f
  | ``Int.ediv
  | ``Nat.div => translateIntEDiv f
  | ``Int.emod
  | ``Nat.mod => translateIntEMod f
  | ``Int.pow => translateIntPow f
  | ``Nat.pow => translateNatPow f
  | ``LE.le =>
        if Nat.blt args.size 2 then throwEnvError "translateOpaqueFun: at least two arguments expected for Le.le"
        if isBitVecType args[0]!
        then return .SimpleIdent bvuleSymbol
        else getOpaqueSmtEquivFun f leqSymbol
  | ``Nat.ble => getOpaqueSmtEquivFun f leqSymbol
  | ``LT.lt =>
        if Nat.blt args.size 2 then throwEnvError "translateOpaqueFun: at least two arguments expected for Lt.lt"
        if isBitVecType args[0]!
        then return .SimpleIdent bvultSymbol
        else if isStringType args[0]!
        then return .SimpleIdent strLtSymbol
        else getOpaqueSmtEquivFun f ltSymbol
  | ``Nat.sub => translateNatSub f
  | ``String.append => getOpaqueSmtEquivFun f strAppendSymbol
  | ``String.length => getOpaqueSmtEquivFun f strLengthSymbol
  | ``String.replace => getOpaqueSmtEquivFun f strReplaceAllSymbol
  | ``BitVec.add => getOpaqueSmtEquivFun f bvaddSymbol
  | ``BitVec.sub => getOpaqueSmtEquivFun f bvsubSymbol
  | ``BitVec.mul => getOpaqueSmtEquivFun f bvmulSymbol
  | ``BitVec.neg => getOpaqueSmtEquivFun f bvnegSymbol
  | ``BitVec.and => getOpaqueSmtEquivFun f bvandSymbol
  | ``BitVec.or  => getOpaqueSmtEquivFun f bvorSymbol
  | ``BitVec.xor => getOpaqueSmtEquivFun f bvxorSymbol
  | ``BitVec.not => getOpaqueSmtEquivFun f bvnotSymbol
  | ``BitVec.ult => getOpaqueSmtEquivFun f bvultSymbol
  | ``BitVec.ule => getOpaqueSmtEquivFun f bvuleSymbol
  | ``BitVec.slt => getOpaqueSmtEquivFun f bvsltSymbol
  | ``BitVec.sle => getOpaqueSmtEquivFun f bvsleSymbol
  | ``BitVec.udiv
  | ``BitVec.sdiv => translateBitVecWrappedDiv f n args
  | ``BitVec.umod => getOpaqueSmtEquivFun f bvuremSymbol
  | ``BitVec.smod => getOpaqueSmtEquivFun f bvsmodSymbol
  | ``BitVec.srem => getOpaqueSmtEquivFun f bvsremSymbol
  | ``BitVec.append => getOpaqueSmtEquivFun f bvconcatSymbol
  | _ => throwEnvError "translateOpaqueFun: unexpected opaque operator {n}"


/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ`, infer the instanitated type w.r.t. `args` such that:
     - let S := [ αᵢ | i ∈ [0..n] ∧ ¬ αᵢ.isExplicit ]
     - let R := [ args[i] | i ∈ [0..n] ∧ ¬ αᵢ.isExplicit ]
     - let k := S.size-1
     - let [α'₀, ..., α'ₚ] := [ αᵢ [S[0]/R[0]] ... [S[k]/R[k]] | i ∈ [0..n] ∧  αᵢ.isExplicit ]
     - return `∀ α'₀ → ∀ α'₁ ... → α'ₚ`
    TODO: change function to pure tail rec call using stack-based approach
-/
partial def inferFunType (t : Expr) (args : Array Expr) : Expr :=
  let rec visit (idx : Nat) (e : Expr) : Expr :=
    if idx ≥ args.size then e
    else
      match e with
      | Expr.forallE n t b bi =>
          if !bi.isExplicit then
            visit (idx + 1) (b.instantiate1 args[idx]!)
          else Expr.forallE n t (visit (idx + 1) b) bi
      | _ => e
  visit 0 t


def updateCoerceCache (fromSmtType toSmtType : SortExpr) (coeName : SmtSymbol) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.coerceCache := env.smtEnv.coerceCache.insert (fromSmtType, toSmtType) coeName })

/-- Given two smt types `fromSmtType` and `toSmtType` and optional coDomainType corresponding to the Lean4 type of toSmtType,
    perform the following:
     - When (fromSmtType, toSmtType) := coeInst ∈ coerceCache
         - return `coeInst`
     - Otherwise:
         - let n ← mkFreshId
         - let coeName := @coerce ++ n
         - add the following entry in coerceCache
             - `(fromSmtType, toSmtType) := coeName`
         - Declare the following smt function:
            - `(declare-fun coeName ((fromSmtType)) toSmtType)`
         - When `coDomainType := some toType` assert the following codomain value constraints:
             - `(assert (forall ((@x fromSmtType)),
                     ( ! (@isToSmtType (coeName @x)) :pattern ((coeName @x)) :qid @coeName_co_cstr)))`
         - return `coeName`
-/
def getConversionFunction (fromSmtType toSmtType : SortExpr) (coDomainType : Option Expr) : TranslateEnvT SmtSymbol := do
  match (← get).smtEnv.coerceCache.get? (fromSmtType, toSmtType) with
  | some coeInst => return coeInst
  | none =>
      let n ← mkFreshId
      let coeName := mkReservedSymbol s!"@coerce{n}"
      -- update coerce cache
      updateCoerceCache fromSmtType toSmtType coeName
      -- declare smt coercion function
      declareFun coeName #[fromSmtType] toSmtType
      if let some toType := coDomainType then
         -- asserting codomain value constraint
        let xsym := mkReservedSymbol s!"@x"
        let xId := smtSimpleVarId xsym
        let f_coeTerm := mkSimpleSmtAppN coeName #[xId]
        let coeQuant := #[(xsym, fromSmtType)]
        let coDomain ← createPredQualifierAppAux f_coeTerm toType
        let qidName := mkQid $ appendSymbol coeName "co_cstr"
        let patterns := some #[mkPattern #[f_coeTerm], qidName]
        assertTerm (mkForallTerm none coeQuant coDomain patterns)
      return coeName

/-- Helper function for createAppN -/
def createAppNAux (pInfo : FunEnvInfo) (s : Sum SmtQualifiedIdent SmtTerm)
  (args : Array Expr) (termTranslator : Expr → TranslateEnvT SmtTerm)
  (isHOF := false) : TranslateEnvT SmtTerm := do
  let nbSize := if args.size < pInfo.paramsInfo.size then args.size else pInfo.paramsInfo.size
  if isHOF then
    let instType := inferFunType pInfo.type args
    withInstantiatedImplicitArgs pInfo.type fun polyType' => do
      let instArgTypes := retrieveArrowTypes instType
      let polyArgTypes := retrieveArrowTypes polyType'
      let mut idxType := 0
      let mut genArgs := #[]
      for i in [:nbSize] do
        if pInfo.paramsInfo[i]!.isExplicit then
          let sarg ← termTranslator args[i]!
          let t1 := instArgTypes[idxType]!
          let t2 := polyArgTypes[idxType]!
          let st1 ← translateType termTranslator t1
          let st2 ← translateType termTranslator t2
          idxType := idxType + 1
          if st1 == st2 then
            genArgs := genArgs.push sarg
          else
            let coerceInst ← getConversionFunction st1 st2 none
            genArgs := genArgs.push (mkSimpleSmtAppN coerceInst #[sarg])
      if genArgs.size == 0
      then genUnapplied s
      else
        let retTypeIdx := instArgTypes.size - 1
        let t1 := instArgTypes[retTypeIdx]!
        let t2 := polyArgTypes[retTypeIdx]!
        let st1 ← translateType termTranslator t1
        let st2 ← translateType termTranslator t2
        let coeReturn ← if st1 == st2 then pure none else some <$> getConversionFunction st2 st1 (some t1)
        genApplied s genArgs coeReturn

  else
    let mut genArgs := #[]
    for i in [:nbSize] do
      if pInfo.paramsInfo[i]!.isExplicit then
        genArgs := genArgs.push (← termTranslator args[i]!)
    if genArgs.size == 0
    then genUnapplied s
    else genApplied s genArgs none

  where
    genUnapplied (id : Sum SmtQualifiedIdent SmtTerm) : TranslateEnvT SmtTerm := do
      if isHOF then
        match id with
        | Sum.inl qi => return .SmtIdent qi
        | Sum.inr st => return st -- case when f corresponds to a function in a ctor argument.
      else
        match id with
        | Sum.inl qi => return .SmtIdent qi
        | _ => throwEnvError "genUnapplied: SmtQualifiedIdent expected !!!"

    genApplied (id : Sum SmtQualifiedIdent SmtTerm) (sargs : Array SmtTerm) (coeReturn : Option SmtSymbol) : TranslateEnvT SmtTerm := do
      if isHOF then
        let applyInst ← getApplyInstName pInfo.type
        let fApp :=
          match id with
          | Sum.inl qi => .SmtIdent qi
          | Sum.inr st => st -- case when f corresponds to a function in a ctor argument.
        let smtApp := mkSimpleSmtAppN applyInst (#[fApp] ++ sargs)
        match coeReturn with
        | some coerceInst => return mkSimpleSmtAppN coerceInst #[smtApp]
        | none => return smtApp
      else
        match id with
        | Sum.inl qi => return mkSmtAppN qi sargs
        | _ => throwEnvError "genApplied: SmtQualifiedIdent expected !!!"
         -- At this stage, we only accept defined function


/-- Given a function application `f x₀ ... xₙ` and `s` the corresponding generated
    smt identifier/term for `f`, perform the following:
      - When `n = 0 ∨ ∀ i ∈ [0..n], ¬ isExplicit xᵢ` (i.e., instantiated polymorphic function passed as argument):
         - When isHOF:
             - When `isSmtQualifiedIdent s`
                - return `.SmtIdent s`
             - Otherwise (i.e., s is an Smt term, case when f corresponds to a function in a ctor argument)
                - return `s`
         - Otherwise:
             - When `isSmtQualifiedIdent s`
                - return `.SmtIdent s`
             - Otherwise (i.e., only a defined function expected)
                 - return ⊥
      - When `∃ i ∈ [0..n], isExplicit xᵢ,`
           - When isHOF:
              - let pInfo ← getFunEnvInfo f
              - let ∀ α₀ → .. → αₖ := inferFunType pInfo.types #[x₀ ... xₙ]`
              - let ∀ p₀ → .. → pₖ := withInstantiatedImplicitArgs pInfo.type
              - let [b₀, ..., bₖ] := [termTranslator xᵢ | i ∈ [0..n] ∧ isExplicit xᵢ]
              - let B := [ eᵢ | i ∈ [0..k-1] ∧
                                taᵢ = translateType termTranslator αᵢ
                                tpᵢ = translateType termTranslator pᵢ
                                (taᵢ = tpᵢ → eᵢ = bᵢ) ∧
                                (taᵢ ≠ tpᵢ → eᵢ = mkSimpleSmtAppN (← getConversionFunction taᵢ tpᵢ none) bᵢ)
                         ]
              - let taₖ = translateType termTranslator αₖ
              - let tpₖ = translateType termTranslator pₖ
              - let applyInst ← getApplyInstName pInfo.type
              - When taₖ = tpₖ
                   - When `isSmtQualifiedIdent s`
                        - return `mkSimpleSmtAppN applyInst (#[.SmtIdent s] ++ B)`
                   - Otherwise:
                        - return `mkSimpleSmtAppN applyInst (#[s] ++ B)`
               - Otherwise
                   - let coeInst ← getConversionFunction tpₖ taₖ (some taₖ)
                   - When `isSmtQualifiedIdent s`
                        - return `mkSimpleSmtAppN coeInst #[mkSimpleSmtAppN applyInst (#[.SmtIdent s] ++ B)]`
                   - Otherwise:
                        - return `mkSimpleSmtAppN coeInst #[mkSimpleSmtAppN applyInst (#[s] ++ B)]`
           - Otherwise:
              - When `isSmtQualifiedIdent s`
                  - let B := [termTranslator xᵢ | i ∈ [0..n] ∧ isExplicit xᵢ]
                  - return `mkSmtAppN s B`
              - Otherwise (i.e., only a defined function expected)
                  - return ⊥
-/
@[always_inline, inline]
def createAppN
  (f : Expr) (s : Sum SmtQualifiedIdent SmtTerm) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) (isHOF := false) : TranslateEnvT SmtTerm := do
  let pInfo ← getFunEnvInfo f
  createAppNAux pInfo s args termTranslator isHOF

/-- Given `t` corresponding the type of a function/lambda parameter:
     - return `translateType termTranslator t
    An error is triggered if `t` corresponds to the type of an implicit argument.
-/
def translateFunLambdaParamType
  (t : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SortExpr := do
  translateType termTranslator t

structure FunctionDefinitions where
  funDecls : Array SmtFunDecl
  funBodies : Array SmtTerm
  isRec : Bool
deriving Inhabited

abbrev FunctionGenEnv := StateRefT FunctionDefinitions TranslateEnvT

def defineFunctions (defs : FunctionDefinitions) : TranslateEnvT Unit := do
 if defs.funDecls.size == 1 then
   let funDecl := defs.funDecls[0]!
   defineFun funDecl.name funDecl.params funDecl.ret defs.funBodies[0]! defs.isRec
 else defineMutualFuns defs.funDecls defs.funBodies

/-- Given `f := Expr.const n _` corresponding to a function name and
    `params` its implicit parameter infos, perform the following actions:
      let instanceArgs := Array.filter (λ p => p.isInstance) params
       - When instanceArgs.isEmpty:
          - instName := funNameToSmtSymbol n
          - add entry `f := SimpleIdent instName` to `funInstCache`
          - return `SimpleIdent instName`
      - When ¬ instanceArgs.isEmpty:
          - instName := funNameToSmtSymbol (n ++ (← mkFreshId))
          - instApp ← getInstApp f params
          - add entry `instApp := SimpleIdent instName` to `funInstCache`
          - return `SimpleIdent instName`
     An error is triggered when `f` is not a named expression.
-/
def generateFunInst (f : Expr) (params : ImplicitParameters) : TranslateEnvT SmtQualifiedIdent := do
   let Expr.const n _ := f | throwEnvError "generateFunInst: name expression expected but got {reprStr f}"
   let instanceArgs := Array.filter (λ p => p.isInstance) params
   -- get instance application
   if instanceArgs.isEmpty
   then
     let instName := funNameToSmtSymbol n
     updateFunInstCache f instName
   else
     let v ← mkFreshId
     let instName := funNameToSmtSymbol (n ++ v)
     let instApp ← getInstApp f params
     updateFunInstCache instApp instName

/-- Given a recursive function application `f x₁ ... xₙ`, perform the following:
     let insApp := getInstApp f (← getImplicitParameters f x₁ ... xₙ)
      - When ∃ `instApp := smtId` ∈ `funInstCache`
         - return `createApp f smtId #[x₁ ... xₙ] termTranslator`
      - Otherwise,
          - generate function definition for `f` at the Smt level
          - smtId ← generateFunInst f (← getImplicitParameters f x₁ ... xₙ)
          - return `createApp f smtId #[x₁ ... xₙ] termTranslator`

    Assume that `f` is a recursive function not tagged as opaque.

    An error is triggered when
      - `f` is not a name expression.
      - No entry in `recFunInstCache` exists for `f`
-/
partial def translateRecFun
  (f : Expr) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  -- get instance application
  let params ← getImplicitParameters f args
  let instApp ← getInstApp f params
  match (← get).smtEnv.funInstCache.get? instApp with
  | none =>
      let Expr.const n l := f
        | throwEnvError "translateRecFun: name expression expected but got {reprStr f}"
      let ConstantInfo.defnInfo dInfo ← getConstEnvInfo n
        | throwEnvError "translateRecFun: no defnInfo for {n}"
      generateRecFunDefinitions dInfo.all l params
      let some smtId := (← get).smtEnv.funInstCache.get? instApp
        | throwEnvError "translateRecFun: instance function name expected for {reprStr instApp}"
      createAppN f (Sum.inl smtId) args termTranslator
  | some smtId =>
      createAppN f (Sum.inl smtId) args termTranslator

  where
    updateFunDefinitions
      (id : SmtQualifiedIdent) (fbody : Expr)
      (defs : FunctionDefinitions) : TranslateEnvT FunctionDefinitions := do
      let pInfo ← getFunEnvInfo fbody
      Optimize.lambdaTelescope fbody fun fvars b => do
        let mut params := (#[] : SortedVars)
        for h : i in [:fvars.size] do
          let fv := fvars[i]
          let decl ← getFVarLocalDecl fv
          updateQuantifiedFVarsCache fv.fvarId! false
          if pInfo.paramsInfo[i]!.isExplicit then
            let st ← translateFunLambdaParamType decl.type termTranslator
            params := params.push (← fvarIdToSmtSymbol fv.fvarId!, st)
        let ret ← translateFunLambdaParamType (← inferTypeEnv b) termTranslator
        let funDecl := {name := getSymbol id, params, ret}
        let sBody ← termTranslator b
        return { defs with funDecls := defs.funDecls.push funDecl, funBodies := defs.funBodies.push sBody }

    replaceGenericRecFun (f : Expr) (params : ImplicitParameters) (e : Expr) : Option Expr :=
      match e with
      | Expr.app .. =>
          Expr.withApp e fun x xargs => do
            match x with
            | Expr.const n _ =>
                if n == internalRecFun then
                  let mut pargs := #[]
                  let mut idxArg := 0
                  for i in [:params.size] do
                    let p := params[i]!
                    if !(p.isInstance) then
                      pargs := pargs.push xargs[idxArg]!
                    else
                      pargs := pargs.push params[i]!.effectiveArg
                    if p.isGeneric || !p.isInstance then
                      idxArg := idxArg + 1
                  some (mkAppN f pargs)
                else none
            | _ => none
      | _ => none

    generateRecFunDefinitions
      (funs : List Name) (us : List Level) (params : ImplicitParameters) : TranslateEnvT Unit := do
      let env ← get
      let mut funDefs := { (default : FunctionDefinitions) with isRec := true }
      let mut finfos := #[]
      -- add all rec fun instance to cache first
      for f in funs do
        let auxApp := mkConst f us
        let smtId ← generateFunInst auxApp params
        finfos := finfos.push (auxApp, smtId)
      for i in [:finfos.size] do
        let auxApp := finfos[i]!.1
        let smtId := finfos[i]!.2
        let instApp ← getInstApp auxApp params
        let some fbody := env.optEnv.recFunInstCache.get? instApp
          | throwEnvError "translateRecFun: function body expected for {reprStr instApp}"
        let fbody' := fbody.replace (replaceGenericRecFun auxApp params)
        -- apply polymorphic instances on body
        let genFVars ← retrieveGenericFVars params
        funDefs ← updateFunDefinitions smtId (Expr.beta fbody' genFVars) funDefs
      defineFunctions funDefs

/-- Return `true` only when `n` corresponds to a function/constructor name
    expected to be eliminated during optimization phase.
-/
def isForbiddenConst (n : Name) : Bool :=
  match n with
  | ``Decidable.decide
  | ``ite
  | ``dite
  | `Iff
  | ``Int.negSucc
  | ``Int.le
  | ``Nat.zero
  | ``Nat.succ
  | ``Nat.pred
  | ``Nat.beq
  | ``Nat.ble
  | ``Nat.le => true
  | _ => false

/-- Same as `isForbiddenConst` but expects a const expression as argument. -/
def isForbiddenConstExpr (e : Expr) : Bool :=
  match e with
  | Expr.const n _ => isForbiddenConst n
  | _ => false

@[always_inline, inline]
def updateAxiomMap (n : Name) : TranslateEnvT SmtSymbol := do
  let s := nameToSmtSymbol n
  modify (fun env => { env with smtEnv.options.axiomMap := env.smtEnv.options.axiomMap.insert n s })
  return s

/-- Given `t := ∀ α₀ → ∀ α₁ ... → αₙ`, infer the instanitated type w.r.t. `params` such that:
     - let S := [ αᵢ | i ∈ [0..n] ∧ ¬ params[i].isInstance ]
     - let R := [ params[i].effectiveArg | i ∈ [0..n] ∧ ¬ params[i].isInstance ]
     - let k := S.size-1
     - let [α'₀, ..., α'ₚ] := [ αᵢ [S[0]/R[0]] ... [S[k]/R[k]] | i ∈ [0..n] ∧ params[i].isInstance ]
     - return `∀ α'₀ → ∀ α'₁ ... → α'ₚ`
    TODO: change function to pure tail rec call using stack-based approach
-/
partial def inferUndeclFunType (t : Expr) (params : ImplicitParameters) : Expr :=
  let rec visit (idx : Nat) (t : Expr) : Expr :=
    if idx ≥ params.size then t
    else
      match t with
      | Expr.forallE n t b bi =>
           let p := params[idx]!
           if p.isInstance
           then visit (idx + 1) (b.instantiate1 p.effectiveArg)
           else Expr.forallE n t (visit (idx + 1) b) bi
      | _ => t
  visit 0 t

/-- Given `f` corresponding to either an undeclared class function, an axiom function or an opaque function
    `params` its corresponding implicit/explicit parameters and `s` its corresponding smt symbol,
     perform the following:
       - Let `∀ α₀ → ∀ α₁ ... → αₙ` := inferUndecFunType (← getFunEnvInfo f).type params
       - declare smt function `declare-fun s ((st₀) .. (stₙ₋₁)) stₙ)`
       - assert the following proposition to constraint the codomain value:
          - `(assert (forall ((@x₀ st₀) ... (@xₙ₋₁ stₙ₋₁))
              (! (@isTypeₙ (s @x₁ ... @xₙ₋₁))
                 :pattern ((s @x₁ ... @xₙ₋₁))) :qid s_cstr)`

     where ∀ i ∈ [0..n], αᵢ translates to Smt type stᵢ
-/
def generateUndeclaredFun
  (f : Expr) (s : SmtSymbol) (params : ImplicitParameters)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT Unit := do
  let pInfo ← getFunEnvInfo f
  -- infer fun type and removing implicit arguments (i.e., even class constraints)
  let funType := inferUndeclFunType pInfo.type params
  Optimize.forallTelescope funType fun fvars retType => do
    let xsyms := Array.ofFn (λ f : Fin fvars.size => mkReservedSymbol s!"@x{f.val}")
    let mut pargs := (#[] : Array SortExpr)
    let mut co_quantifiers := (#[] : SortedVars)
    for h : i in [:fvars.size] do
      let decl ← getFVarLocalDecl fvars[i]
      let st ← translateFunLambdaParamType decl.type termTranslator
      pargs := pargs.push st
      co_quantifiers := co_quantifiers.push (xsyms[i]!, st)
    let ret ← translateFunLambdaParamType retType termTranslator
    declareFun s pargs ret
    -- assert codomain constraint
    if fvars.size > 0 then
      let xIds := Array.map (λ v => smtSimpleVarId v) xsyms
      let f_applyTerm := mkSimpleSmtAppN s xIds
      let forallBody ← createPredQualifierAppAux f_applyTerm retType
      let qidName := mkQid $ appendSymbol s "cstr"
      let pattern := some #[mkPattern #[f_applyTerm], qidName]
      assertTerm (mkForallTerm none co_quantifiers forallBody pattern)
    else
      assertTerm (← createPredQualifierAppAux (smtSimpleVarId s) retType)


def updateAbstractTypeCache (t : Expr) (abstName : SmtSymbol) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.abstractTypeCache := env.smtEnv.abstractTypeCache.insert t abstName })

/-- Given `t` a potential type expression, perform the following:
     - When isInductiveTypeExpr t
         - When t := absInst ∈ abstractTypeCache
           - return `smtSimpleVarId abstInst`
         - Otherwise:
             - let sortType ← inferTypeEnv t
             - When sortType := decl ∈ indTypeInstCache:
                 - let st ← translateType termTranslator t
                 - let n ← mkFreshId
                 - let abstName := "@abstractType{n}"
                 - add entry `t := abstName` to `abstractTypeCache`
                 - declare global abstract type for t at smt level
                    `(declare-const abstName decl.instSort)`
                 - let instSort ← getInstanceSort decl
                 - let coerceInst ← getConversionFunction st instSort none
                 - assert inhabited constraint at smt level
                    - `(forall ((@x st)) (=> (@isType @x) (decl.instName (coerceInst @x) abstName)))`
                    - E.g., for Nat
                       `(forall ((@x Nat)) (=> (@isNat @x) (@isInstance_<UUID> (@coerce @x) @abstractType<UUID>)))`
                       with
                         - `(declare-fun @coerce ((Nat)) @Instance_<UUID>)`
                         - `(declare-const @abstractType<UUID> @Type_<UUID>)`
                         - `(declare-fun @isInstance_<UUID> @Instance_<UUID> @Type_<UUID>)`
                 - return `smtSimpleVarId abstName`
             - Otherwise:
                - return ⊥
     - Otherwise:
         - return `none`
-/
def translateIndTypeExpr? (t : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT (Option SmtTerm) := do
 let env ← get
 if !(← isInductiveTypeExpr t) then return none
 match env.smtEnv.abstractTypeCache.get? t with
 | some abstInst => return smtSimpleVarId abstInst
 | none =>
      let sortType ← inferTypeEnv t
      match env.smtEnv.indTypeInstCache.get? sortType with
      | none => throwEnvError "translateConst: Abstract sort instance expected for {reprStr t}"
      | some decl =>
          let st ← translateType termTranslator t
          let n ← mkFreshId
          -- declare global abstract type
          let abstName := mkReservedSymbol s!"@abstractType{n}"
          -- update abstract type cache
          updateAbstractTypeCache t abstName
          declareConst abstName decl.instSort
          -- assert inhabited constraint
          let instSort ← getInstanceSort decl
          let coerceInst ← getConversionFunction st instSort none
          let xsym := mkReservedSymbol s!"@x"
          let xId := smtSimpleVarId xsym
          let predQualifier ← createPredQualifierAppAux xId t
          let coerceApp := mkSimpleSmtAppN coerceInst #[xId]
          let instPred := mkSimpleSmtAppN decl.instName #[coerceApp, smtSimpleVarId abstName]
          let forallBody := impliesSmt predQualifier instPred
          assertTerm (mkForallTerm none #[(xsym, st)] forallBody none)
          return smtSimpleVarId abstName

/-- Given `e := Expr.const n l`,
     - When `n := false`
        - return `BoolTerm false`
     - When `n := False`
        - return `BoolTerm false`
     - When `n := true`
        - return `BoolTerm true`
     - When `n := True`
         - return `BoolTerm true`
     - When `n := Int.ofNat`
         - return `termTranslator (← etaExpand e)`
     - When `isInductiveTypeExpr e`
         - return ⊥
     - When `isForbiddenUnappliedConst n`
         - return ⊥
     - When `isMatchExpr e`
         - return ⊥
     - When `n` is a constructor with implicit arguments
         - return ⊥
     - When `n` is a nullary constructor
         - return `SmtIdent (.QualifiedIdent n (translateType termTranslator Type(n)))`
     - When `n` is a parameterized constructor
         - return `termTranslator (← etaExpand e)`
     - When `hasImplicitArgs e`
         - return ⊥
     - When `n` ∈ opaqueFuns ∨ isRecursiveFun `n`
         - return `termTranslator (← etaExpand e)`
     - When `isTheorem n` ∧ `¬ hasSorryTheorem e` ∧ ¬ Type(e).isForAll
         - return termTranslator (← optimizeExpr' Type(e))
     - When `isAxiom n ∨ some ConstantInfo.opaqueInfo _ ← getConstEnvInfo n`
         - When n := s ∈ axiomMap:
             - return `smtSimpleVarId s`
         - Otherwise:
             - When `isFunType Type(e)`
                 - return `termTranslator (← etaExpand e)`
             - Otherwise:
                 - Let s = nameToSmtSymbol n
                 - add `n := s` to axiomMap
                 - Let t' ← removeTypeAbbrev Type(e)
                 - Let st ← translateTypeAux termTranslator t'
                 - declare smt symbol `(declare-const s st)`
                 - Let pterm ← createPredQualifierApp s t'
                 - assert term `(assert pterm)`
                 - return `smtSimpleVarId s`
     - Otherwise
         - return ⊥
    An error is triggered when `e` is not a name expression.

    NOTE: This function cannot be called on fun name expression
    (i.e., f x₁ ... xₙ, where `e := f` and `f` is a partially or totally applied function).
    It can only be applied on functions passed as arguments.
-/
def translateConst
  (e : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let Expr.const n _ := e | throwEnvError "translateConst: name expression expected but got {reprStr e}"
  match n with
  | ``false
  | ``False => return falseSmt
  | ``true
  | ``True => return trueSmt
  | ``Int.ofNat => return (← termTranslator (← Optimize.etaExpand e))
  | _ =>
    if isForbiddenUnappliedConst n then
      throwEnvError "translateConst: unexpected name expression {reprStr e}"
    if (← isMatchExpr e) then
      throwEnvError "translateConst: unexpected match function passed as argument {n}"
    if let some r ← translateCtor n then return r
    if (← hasImplicitArgs e) then
      throwEnvError "translateConst: unexpected implicit arguments for function {reprStr e}"
    if let some r ← translateDefineFun? n then return r
    if let some r ← translateTheorem? n then return r
    if let some r ← translateAxiomOrOpaque? n then return r
    if let some r ← translateIndTypeExpr? e termTranslator then return r
    throwEnvError "translateConst: only inductive type/opaque/recursive functions and theorems expected but got {reprStr e}"


  where

    translateCtor (c : Name) : TranslateEnvT (Option SmtTerm) := do
      let ConstantInfo.ctorInfo info ← getConstEnvInfo c | return none
      if info.numParams != 0 then
        throwEnvError "translateConst: unexpected implicit arguments for ctor {c}"
      if info.numFields == 0 then
        -- nullary constructor case
        let st ← translateType termTranslator (← inferTypeEnv e)
        return (smtQualifiedVarId (nameToSmtSymbol c) st)
      else termTranslator (← Optimize.etaExpand e) -- parameterized constructor case

    translateDefineFun? (n : Name) : TranslateEnvT (Option SmtTerm) := do
      if (opaqueFuns.contains n) || (← isRecursiveFun n) then
        termTranslator (← Optimize.etaExpand e)
      else return none

    translateTheorem? (n : Name) : TranslateEnvT (Option SmtTerm) := do
      if !(← isTheorem n) then return none
      let ConstantInfo.thmInfo info ← getConstEnvInfo n | return none
      -- check if e has sorry theorem and trigger error if this is the case
      hasSorryTheorem e "translateConst: Theorem {n} has `sorry` demonstration"
      if info.type.isForall then
        throwEnvError "translateConst: Fully applied theorem expected but got {reprStr info.type}"
      termTranslator (← optimizeExpr' info.type)

    getAxiomOpaqueType (n : Name) : TranslateEnvT (Option Expr) := do
       match ← getConstEnvInfo n with
       | ConstantInfo.axiomInfo info =>
            if ← isPropEnv info.type then
              throwEnvError "translateConst: Unexpected Axiom of type Prop {n}"
            return info.type
       | ConstantInfo.opaqueInfo info => return info.type
       | _ => return none

    translateAxiomOrOpaque? (n : Name) : TranslateEnvT (Option SmtTerm) := do
       let some t ← getAxiomOpaqueType n | return none
       match (← get).smtEnv.options.axiomMap.get? n with
       | some s => return (smtSimpleVarId s)
       | none =>
           if ← isFunType t then
             termTranslator (← Optimize.etaExpand e)
           else
             let smtSym ← updateAxiomMap n
             let t' ← removeTypeAbbrev t
             let smtType ← translateTypeAux termTranslator t'
             -- declare free variable at top level
             declareConst smtSym smtType
             let pTerm ← createPredQualifierApp smtSym t'
             assertTerm pTerm
             return (smtSimpleVarId smtSym)

    isForbiddenUnappliedConst (n : Name) : Bool :=
      match n with
      | ``Exists
      | ``Blaster.decide'
      | ``Blaster.dite'
      | _ => isForbiddenConst n


/-- Given `n` corresponding to the name of a structure, return the structure ctor name.
    An error is triggered when:
      - Induction Info is not found for `n`
      - Induction type `n` has more than one ctor
-/
def getProjectionCtor (n : Name) : TranslateEnvT Name := do
  let ConstantInfo.inductInfo indVal ← getConstEnvInfo n
    | throwEnvError "getProjectionCtor: induction info expected for {n}"
  match indVal.ctors with
  | [c] => return c
  | _ => throwEnvError "getProjectionCtor: only one ctor expected for structure for {n}"

/-! ## BitVec ops requiring custom translation -/

/-- Translate BitVec shifts.
    For `BitVec.shiftLeft x (s : Nat)`, `BitVec.ushiftRight x (s : Nat)`, and
    `BitVec.sshiftRight x (s : Nat)`, `s` must be either:
      (a) a Nat literal → emitted as `(_ bv{min s w} w)` (a width-`w` bitvec constant,
          clamped to `w` so the SMT numeral stays representable); or
      (b) `BitVec.toNat w' y'` where `w' = w` → emitted as `(bvOP sx sy')`.

    Case (b) arises from `x <<< y` with `y : BitVec w`, which Lean unfolds to
    `BitVec.shiftLeft x y.toNat`.  With `BitVec.toNat` opaque the toNat call
    survives optimization and is detected here.  The encoding is faithful: both Lean
    and SMT bvshl/bvlshr/bvashr agree on the out-of-range behavior (≥ width yields
    0 / sign-fill).

    For case (a), the literal is clamped to `min s w` before encoding.  This is
    sound because Lean and SMT shifts both saturate at amounts ≥ width (bvshl/bvlshr
    → 0, bvashr → sign-fill), so any `s ≥ w` is equivalent to `w`.  The clamping
    also avoids a Z3 bug: Z3 silently truncates `(_ bvS w)` mod 2^w when S ≥ 2^w,
    which would make e.g. `x <<< 256` at width 8 appear as shift-by-0 and
    produce false counterexamples.

    All three Lean shift functions share the same arg layout:
      args[0] : Nat      — width (implicit, must be a literal)
      args[1] : BitVec w — the value to shift
      args[2] : Nat      — the shift amount (literal OR `BitVec.toNat w' y'`)

    A symbolic Nat shift amount (neither a literal nor a same-width toNat) triggers
    an error suggesting the BitVec-amount form.
-/
def translateBitVecShift
  (n : Name) (args : Array Expr) (sym : SmtSymbol)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if args.size != 3 then
    throwEnvError "translateBitVecShift: fully applied {n} expected but got {args.size} arguments"
  let some w := isNatValue? args[0]!
    | throwEnvError "translateBitVecShift: literal width expected for {n}"
  let sx ← termTranslator args[1]!
  -- bv-by-bv shifts arrive as `shiftLeft x (y.toNat)`: faithful as a direct
  -- bv shift when y has the same width
  if let some (w', sAmount) := isBitVecToNat? args[2]! then
    if w' != w then
      throwEnvError "translateBitVecShift: shift amount width {w'} ≠ operand width {w} for {n}"
    return mkSimpleSmtAppN sym #[sx, ← termTranslator sAmount]
  let some s := isNatValue? args[2]!
    | throwEnvError "translateBitVecShift: literal shift amount expected for {n}; use a `BitVec {w}` shift amount for symbolic shifts"
  -- Lean and SMT shifts both saturate at s ≥ w, so clamp the literal: keeps
  -- the numeral representable (Z3 silently truncates `(_ bvS w)` mod 2^w).
  return mkSimpleSmtAppN sym #[sx, bitvecLitSmt (min s w) w]

/-- Translate BitVec structure ops that require indexed Smt identifiers.

    Arg layouts (from `@`-checked signatures; all widths are the first implicit arg):
      - `BitVec.extractLsb {n} hi lo x`  → args := #[n, hi, lo, x]
            SMT: `((_ extract hi lo) x)`     result width = hi - lo + 1
      - `BitVec.extractLsb' {n} start len x` → args := #[n, start, len, x]
            SMT: `((_ extract (start+len-1) start) x)`  result width = len
      - `BitVec.setWidth {w} v x`          → args := #[w, v, x]
            v ≥ w: `((_ zero_extend (v-w)) x)`
            v < w: `((_ extract (v-1) 0) x)`   (truncation; same semantics as Lean)
            v = 0: error (would produce illegal `(_ BitVec 0)`)
      - `BitVec.signExtend {w} v x`        → args := #[w, v, x]
            v ≥ w: `((_ sign_extend (v-w)) x)`
            v < w: `((_ extract (v-1) 0) x)`   (truncation; same semantics as Lean)
            v = 0: error (would produce illegal `(_ BitVec 0)`)
      - `BitVec.rotateLeft {w} x k`        → args := #[w, x, k]
            SMT: `((_ rotate_left (k % w)) x)`  (modular; k = 0 when w = 0, guarded)
      - `BitVec.rotateRight {w} x k`       → args := #[w, x, k]
            SMT: `((_ rotate_right (k % w)) x)`

    All index arguments must be Nat literals; non-literal indices trigger an error.
    Width-0 results (setWidth 0, signExtend 0, extractLsb' with len=0) trigger an error
    since `(_ BitVec 0)` is illegal in SMT-LIB.
    Out-of-range extracts (`hi ≥ srcW` for extractLsb/extractLsb', `hi < lo` for extractLsb)
    trigger errors even though Lean zero-fills them — SMT `(_ extract hi lo)` requires
    `lo ≤ hi < srcW`.
-/
def translateBitVecIndexed
  (n : Name) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  -- Helper: extract a Nat literal from args[i]; error on non-literal
  let litArg : Nat → String → TranslateEnvT Nat := fun i role => do
    let some v := isNatValue? args[i]!
      | throwEnvError "translateBitVecIndexed: literal Nat {role} expected for {n}"
    return v
  match n with
  | ``BitVec.extractLsb =>
    -- args: #[n(implicit), hi, lo, x]
    if args.size != 4 then
      throwEnvError "translateBitVecIndexed: extractLsb expects 4 args, got {args.size}"
    let srcW ← litArg 0 "width"
    let hi ← litArg 1 "high index"
    let lo ← litArg 2 "low index"
    if hi ≥ srcW then
      throwEnvError "translateBitVecIndexed: extractLsb hi={hi} out of range for BitVec {srcW} (SMT requires hi < source width)"
    if hi < lo then
      throwEnvError "translateBitVecIndexed: extractLsb hi={hi} < lo={lo} is invalid"
    let sx ← termTranslator args[3]!
    return mkSimpleSmtAppN (bvextractSymbol hi lo) #[sx]
  | ``BitVec.extractLsb' =>
    -- args: #[n(implicit), start, len, x]
    if args.size != 4 then
      throwEnvError "translateBitVecIndexed: extractLsb' expects 4 args, got {args.size}"
    let srcW ← litArg 0 "width"
    let start ← litArg 1 "start index"
    let len   ← litArg 2 "length"
    if len == 0 then
      throwEnvError "translateBitVecIndexed: extractLsb' with len=0 would produce illegal (_ BitVec 0)"
    let hi := start + len - 1
    if hi ≥ srcW then
      throwEnvError "translateBitVecIndexed: extractLsb' start={start} len={len} (hi={hi}) out of range for BitVec {srcW}"
    let sx ← termTranslator args[3]!
    return mkSimpleSmtAppN (bvextractSymbol hi start) #[sx]
  | ``BitVec.setWidth | ``BitVec.signExtend =>
    -- args: #[w(implicit), v, x]
    if args.size != 3 then
      throwEnvError "translateBitVecIndexed: {n} expects 3 args, got {args.size}"
    let extSym := if n == ``BitVec.signExtend then bvsignExtendSymbol else bvzeroExtendSymbol
    let w ← litArg 0 "width"
    let v ← litArg 1 "target width"
    if v == 0 then
      throwEnvError "translateBitVecIndexed: {n} 0 would produce illegal (_ BitVec 0)"
    let sx ← termTranslator args[2]!
    if v ≥ w then
      return mkSimpleSmtAppN (extSym (v - w)) #[sx]
    else
      -- v < w: truncate to lowest v bits (same semantics as Lean's setWidth/signExtend shrink)
      return mkSimpleSmtAppN (bvextractSymbol (v - 1) 0) #[sx]
  | ``BitVec.rotateLeft | ``BitVec.rotateRight =>
    -- args: #[w(implicit), x, k]
    if args.size != 3 then
      throwEnvError "translateBitVecIndexed: {n} expects 3 args, got {args.size}"
    let rotSym := if n == ``BitVec.rotateLeft then bvrotateLeftSymbol else bvrotateRightSymbol
    let w ← litArg 0 "width"
    let k ← litArg 2 "rotation amount"
    if w == 0 then
      throwEnvError "translateBitVecIndexed: {n} on BitVec 0 is not supported"
    let sx ← termTranslator args[1]!
    return mkSimpleSmtAppN (rotSym (k % w)) #[sx]
  | _ => throwEnvError "translateBitVecIndexed: unexpected op {n}"

/-- Max Vector length unrolled into an explicit equality conjunction; above this, a bounded forall is used. -/
def vectorUnrollThreshold : Nat := 16

/-- Max nesting depth for recursive pointwise equality of nested Vector elements. -/
def vectorMaxNestDepth : Nat := 16

/-- Translate Application
    TODO: UPDATE
-/
def translateApp
  (e : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if isForbiddenConstExpr e then throwEnvError "unexpected name expression {reprStr e}"
  Expr.withApp e fun f args => do
    match f with
    | Expr.const n _ =>
         if let some r ← translateFullyApplied? f n args then return r
         if let some r ← translateFinOp? n args then return r
         if let some r ← translateVectorOp? n args then return r
         if let some r ← translateVectorUnsupported? n then return r
         if let some r ← translateUIntOp? n args then return r
         if let some r ← translateUIntConv? n args then return r
         if let some r ← translateFinArith? n args then return r
         if let some r ← translateSMTArrayOp? n args then return r
         if let some r ← translateArrayLit? n args then return r
         if let some r ← translateSMTArrayCtor? n then return r
         if let some r ← translateBitVecShift? n args then return r
         if let some r ← translateBitVecIndexed? n args then return r
         if let some r ← translateUnsupportedConv? n then return r
         if let some r ← translateEq? f n args then return r
         if let some r ← translateRelational? f n args then return r
         if let some r ← translateDITE? f n args then return r
         if let some r ← translateOfNat? n args then return r
         if let some r ← translateDecide? n args then return r
         if let some r ← translateMatch? f args termTranslator then return r
         if let some r ← translateExists? n args then return r
         if let some r ← translateRecFun? f n args then return r
         if let some r ← translateAppliedCtor? f n args then return r
         if let some r ← translateAxiomOrUndeclFun? f n args then return r
         if let some r ← translateTheorem n args then return r
         if let some r ← translateInductivePredicate? f n args then return r
         if let some r ← translateIndTypeExpr? e termTranslator then return r
         throwEnvError "translateApp: unexpected application {reprStr e}"

    | Expr.fvar _ => -- case for HOF
         let .SmtIdent smtId ← translateFreeVar f termTranslator
           | throwEnvError "translateApp: SmtIdent expected for {reprStr f}"
         createAppN f (Sum.inl smtId) args termTranslator (isHOF := true)

    | Expr.mdata .. => -- case when f is defined as a ctor argument and is used in a ctor proposition
        match toTaggedCtorSelector? f with
        | some (Expr.app (Expr.const s _) _) =>
            match (← get).smtEnv.funCtorCache.get? s with
            | none => throwEnvError "translateApp (mdata): FunEnvInfo expected for {reprStr s}"
            | some pInfo =>
               createAppNAux pInfo (← Sum.inr <$> termTranslator f) args termTranslator (isHOF := true)
        | _ => throwEnvError "translateApp: ctor selector tag expected but got {reprStr f}"

    | Expr.proj n i s => -- case when f is a function within a ctor.
         let ctor ← getProjectionCtor n
         let sctor := s!"{ctor}.{i}".toName
         let some pInfo := (← get).smtEnv.funCtorCache.get? sctor
           | throwEnvError "translateApp (proj): FunEnvInfo expected for {reprStr sctor}"
         createAppNAux pInfo (← Sum.inr <$> termTranslator f) args termTranslator (isHOF := true)

    | _ => throwEnvError "translateApp: unexpected application {reprStr e}"

  where
    /-- Build a pointwise conjunction for `Vector α n` equality between SMT terms `tv` and `tw`.
        Dispatches on the element type `elemTypeExpr` to handle nested Vectors faithfully:
        - Leaf element: emits `(= (select tv k) (select tw k))`
        - `Vector β m` element: recurses to produce nested pointwise equality

        `depth` bounds the recursion (default `vectorMaxNestDepth`; sufficient for any realistic nesting depth).

        - n = 0 → `true`
        - 1 ≤ n ≤ `vectorUnrollThreshold` → unrolled conjunction (recursive for nested Vectors)
        - n > `vectorUnrollThreshold` → bounded forall `∀ @__veq_i, 0 ≤ i < n → (sel tv i) = (sel tw i)`.
          **Limitation**: n > `vectorUnrollThreshold` uses plain `=` for elements even if the element type is
          itself a Vector (nested pointwise inside forall requires additional quantifiers).
    -/
    vectorPointwiseEqSmtM (elemTypeExpr : Expr) (tv tw : SmtTerm) (n : Nat) (depth : Nat := vectorMaxNestDepth) : TranslateEnvT SmtTerm := do
      if n == 0 then return trueSmt
      else if n ≤ vectorUnrollThreshold then do
        -- Hoist loop-invariant element-type analysis: check once whether elemTypeExpr is a
        -- nested Vector with a literal length, so the per-index closure just builds select-eq.
        let innerVec? : Option (Expr × Nat) ←
          if elemTypeExpr.getAppFn.isConstOf ``Vector then do
            let innerArgs := elemTypeExpr.getAppArgs
            if innerArgs.size >= 2 then do
              let mExpr ← whnf innerArgs[1]!
              if let some mVal := isNatValue? mExpr then
                pure (some (innerArgs[0]!, mVal))
              else pure none
            else pure none
          else pure none
        -- Build element equality, recursing into nested Vectors when depth allows.
        let mkElemEq (te1 te2 : SmtTerm) : TranslateEnvT SmtTerm := do
          match depth, innerVec? with
          | depth' + 1, some (innerElem, mVal) =>
            return ← vectorPointwiseEqSmtM innerElem te1 te2 mVal depth'
          | _, _ => return eqSmt te1 te2
        -- Unrolled conjunction over [0, n)
        let mut result ← mkElemEq (selectSmt tv #[natLitSmt 0]) (selectSmt tw #[natLitSmt 0])
        for k in List.range (n - 1) do
          let kNext := k + 1
          let conjunct ← mkElemEq (selectSmt tv #[natLitSmt kNext]) (selectSmt tw #[natLitSmt kNext])
          result := andSmt result conjunct
        return result
      else
        -- Bounded forall (n > vectorUnrollThreshold): uses plain `=` for elements (limitation for nested Vectors).
        let iSym := mkReservedSymbol "@__veq_i"
        let iTerm : SmtTerm := .SmtIdent (.SimpleIdent iSym)
        let guard := andSmt (leqSmt (natLitSmt 0) iTerm) (ltSmt iTerm (natLitSmt n))
        let body := impliesSmt guard (eqSmt (selectSmt tv #[iTerm]) (selectSmt tw #[iTerm]))
        return mkForallTerm none #[(iSym, intSort)] body none
      termination_by depth

    /-- If `typeExpr` is `Vector α n` with literal length `n`, translate the two operands
        `lhsExpr`/`rhsExpr` and return `some (pointwise conjunction)`.
        Returns `none` if `typeExpr` is not a Vector with a literal length (falls through to
        generic equality). -/
    translateVectorEq? (typeExpr lhsExpr rhsExpr : Expr) : TranslateEnvT (Option SmtTerm) := do
      -- Quick check: head constant must be Vector
      if !typeExpr.getAppFn.isConstOf ``Vector then return none
      let vecArgs := typeExpr.getAppArgs
      -- Vector has two type parameters: α (index 0) and n (index 1)
      if vecArgs.size < 2 then return none
      let nExpr ← whnf vecArgs[1]!
      let some nVal := isNatValue? nExpr | return none
      -- Type confirmed as `Vector α (literal nVal)` — build pointwise eq
      let tv ← termTranslator lhsExpr
      let tw ← termTranslator rhsExpr
      return some (← vectorPointwiseEqSmtM vecArgs[0]! tv tw nVal)

    translateEq? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Eq =>
         if args.size == 2 then
           throwEnvError "translateEq?: unexpected partially applied Eq got {reprStr args}"
         if args.size == 1 then return (← termTranslator (← Optimize.etaExpand e))
         -- Intercept Vector equality: emit pointwise conjunction instead of extensional SMT `=`
         if let some r ← translateVectorEq? args[0]! args[1]! args[2]! then return r
         match args[1]! with
          | Expr.const ``true _ => termTranslator args[2]!
          | Expr.const ``false _ => termTranslator (mkApp (← mkBoolNotOp) args[2]!)
          | _ => createAppN f (← Sum.inl <$> translateOpaqueFun f n args) args termTranslator
       | _ => return none

    translateDITE? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Blaster.dite' =>
            if args.size != 4 then
               throwEnvError "translateDITE?: unexpected partially applied dite' got {reprStr args}"
            let args := args.set! 2 (args[2]!.beta #[← mkOfDecideEqProof args[1]! true])
            let args := args.set! 3 (args[3]!.beta #[← mkOfDecideEqProof args[1]! false])
            createAppN f (← Sum.inl <$> translateOpaqueFun f n args) args termTranslator
       | _ => return none

    translateOfNat? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Int.ofNat =>
            if args.size != 1 then
               throwEnvError "translateOfNat?: exaclty one argument expected"
            termTranslator args[0]!
       | _ => return none

    translateDecide? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Blaster.decide' =>
            if args.size != 1 then
               throwEnvError "translateDecide?: unexpected partially applied {n} got {reprStr args}"
            termTranslator args[0]!
       | _ => return none

    translateRelational? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      -- Vector `==` unfolds to Vector.isEqv/toArray upstream, so there's no BEq.beq node to intercept here; Vector equality is handled at the propositional `=` path (translateVectorEq?).
      match n with
       | ``BEq.beq
       | ``LE.le
       | ``LT.lt =>
            if (← isOpaqueRelational n args) then
              if args.size == 3 then
                throwEnvError "translateRelational?: unexpected partially applied {n} got {reprStr args}"
              if args.size == 2 then return (← termTranslator (← Optimize.etaExpand e))
              createAppN f (← Sum.inl <$> translateOpaqueFun f n args) args termTranslator
            else return none -- undefined fun class case
       | _ => return none

    genExistsTerm (lambdaE : Expr) : QuantifierEnvT SmtTerm := do
      Optimize.lambdaTelescope lambdaE fun fvars b => do
        for h : i in [:fvars.size] do
          let fv := fvars[i]
          let decl ← getFVarLocalDecl fv
          translateQuantifier fv decl.type termTranslator
        let env ← get
        let mut ebody ← termTranslator b
        let nbPremises := env.premises.size
        for i in [:nbPremises] do
          let idx := nbPremises - i - 1
          ebody := andSmt env.premises[idx]! ebody
        return (mkExistsTerm none env.quantifiers ebody none)

    translateExists? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Exists =>
          if args.size != 2 then
            throwEnvError "translateExists?: exactly two arguments expected but got {reprStr args}"
          let (t, _) ← genExistsTerm args[1]! |>.run (initialQuantifierEnv false)
          return t
      | _ => return none

    translateRecFun? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isOpaqueFun n args) then return none
      if !(← isRecursiveFun n) then return none
      let pInfo ← getFunEnvInfo f
      if pInfo.paramsInfo.size > args.size
      then termTranslator (← Optimize.etaExpand e) -- partially applied function
      else translateRecFun f args termTranslator

    translateAppliedCtor? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      let ConstantInfo.ctorInfo info ← getConstEnvInfo n | return none
      if args.size < info.numParams + info.numFields
      then termTranslator (← Optimize.etaExpand e) -- partially applied ctor case
      else
        let st ← translateType termTranslator (← inferTypeEnv e)
        if info.numFields == 0 then
          -- nullary polymorphic constructor case
           return (smtQualifiedVarId (nameToSmtSymbol n) st)
        else
          createAppN f (Sum.inl $ .QualifiedIdent (nameToSmtSymbol n) st) args termTranslator

    getUndeclFunAppInst (f : Expr) (params : ImplicitParameters) : TranslateEnvT Expr := do
      let instAux ← getInstApp f params
      let genericArgs ← retrieveGenericFVars params
      mkLambdaFVars genericArgs instAux (usedOnly := true)


    isOpaqueAxiomOrUndeclFun (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      match ← getFunBody f with
      | none =>
         match (← getConstEnvInfo n) with
         | ConstantInfo.axiomInfo _
         | ConstantInfo.opaqueInfo _ => return true
         | _ => return false

      | some fbody => isUndefinedClassFunApp (Expr.beta fbody args)

    translateAxiomOrUndeclFun? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isOpaqueFun n args) then return none
      if !(← isOpaqueAxiomOrUndeclFun f n args) then return none
      let pInfo ← getFunEnvInfo f
      if pInfo.paramsInfo.size > args.size then
        return ← termTranslator (← Optimize.etaExpand e) -- partially applied function
      -- get instance application
      let params ← getImplicitParameters f args
      let instApp ← getUndeclFunAppInst f params
      match (← get).smtEnv.funInstCache.get? instApp with
      | none =>
         let smtId ← generateFunInst f params
         let .SimpleIdent s := smtId
           | throwEnvError "translateUndeclaredFun?: SimpleIdent expected but got {smtId}"
         generateUndeclaredFun f s params termTranslator
         createAppN f (Sum.inl smtId) args termTranslator
      | some smtId =>
          createAppN f (Sum.inl smtId) args termTranslator

    translateFullyApplied? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if !(fullyAppliedConst.contains n) then return none
      let pInfo ← getFunEnvInfo f
      if pInfo.paramsInfo.size != args.size then
        throwEnvError "translateFullyApplied?: fully applied function expected for {reprStr f}"
      createAppN f (← Sum.inl <$> translateOpaqueFun f n args) args termTranslator

    translateBitVecShift? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``BitVec.shiftLeft   => return some (← translateBitVecShift n args bvshlSymbol  termTranslator)
      | ``BitVec.ushiftRight => return some (← translateBitVecShift n args bvlshrSymbol termTranslator)
      | ``BitVec.sshiftRight => return some (← translateBitVecShift n args bvashrSymbol termTranslator)
      | _ => return none

    translateBitVecIndexed? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``BitVec.extractLsb
      | ``BitVec.extractLsb'
      | ``BitVec.setWidth
      | ``BitVec.signExtend
      | ``BitVec.rotateLeft
      | ``BitVec.rotateRight => return some (← translateBitVecIndexed n args termTranslator)
      | _ => return none

    /-- UInt/Int family wrapper ctors/projections are identity at the SMT level —
        all 12 types translate to `(_ BitVec w)`, so their single-field constructors
        and projections are no-ops.

        - `UInt8.ofBitVec bv`         → translate bv  (identity)
        - `_private…Int8.ofUInt8 x`   → translate x   (identity; private ctor detected
                                         via ctorInfo.induct rather than a backtick literal)
        - `USize.ofBitVec (BitVec.ofNat <platform-w> v)` → `bitvecLitSmt (v%2^w) w`
          (platform width is opaque at compile time → read from usize-width option, default 64)
        - `ISize.ofUSize (USize.ofBitVec …)` → recurse twice; bottoms out at the USize arm.
    -/
    translateUIntOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      -- Only fires for single-field structure constructors whose parent is a UInt/Int family
      let ConstantInfo.ctorInfo ci ← getConstEnvInfo n | return none
      let isUSizeFamily := ci.induct == ``USize
      let isISizeFamily := ci.induct == ``ISize
      if !isUIntFamilyName ci.induct then return none
      -- The ctor has exactly one field (numParams=0, numFields=1); the field is the last arg.
      if args.isEmpty then return (← termTranslator (← Optimize.etaExpand e))
      let inner := args[args.size - 1]!
      -- USize/ISize special case: the inner arg may be `BitVec.ofNat <non-literal-w> v`
      -- because System.Platform.numBits is opaque (not a Nat literal) — isBitVecValue? would fail.
      -- Detect it here and emit the literal with the configured usize-width.
      if isUSizeFamily || isISizeFamily then
        if let some t ← translatePlatformBvLit? inner then return some t
      return some (← termTranslator inner)

    /-- Translate unsigned UInt/USize cross-width conversions (path B).

        These conversions all reduce to `a.toNat` internally (making them opaque is required to
        prevent the translator from seeing a bare `BitVec.toNat`).

        Supported conversions — all are unsigned (zero-extend on widen, extract on narrow):
          UInt{m}.toUInt{n}   for all m,n ∈ {8,16,32,64}
          UInt{m}.toUSize     for m ∈ {8,16,32}    (widen to usize-width, default 64)
          USize.toUInt64      / UInt64.toUSize      (same-width=64 identity)

        Int widen/narrow (BitVec.signExtend path) and same-width reinterprets (ctor/proj identity)
        are handled by paths A and B of `translateUIntOp?`/`translateBitVecIndexed` and do NOT
        appear here.

        `toNat`/`toInt` (unbounded) are explicitly rejected.

        Arg layout: `UInt{m}.toUInt{n} x` has exactly one explicit arg (x); the conversion
        functions are unary with no implicit type-width args that survive optimization.
    -/
    translateUIntConv? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      -- Parse "TypeName.toOtherTypeName" → (srcName, tgtName)
      let some (srcName, tgtName) := (match n with
        | .str p s =>
            if s.startsWith "to" then
              let t := s.drop 2
              if t.isEmpty then none
              else some (p, Name.mkSimple t)
            else none
        | _ => none)
        | return none
      -- Only fire for conversions within the UInt/Int family (both source and target).
      -- Reject toNat/toInt (target = Nat or Int, which are unbounded).
      if tgtName == ``Nat || tgtName == ``Int then
        return none
      -- Source must be in the UInt/Int family; target must too.
      if !isUIntFamilyName srcName then return none
      if !isUIntFamilyName tgtName then return none
      -- Exactly one explicit argument expected (the value to convert).
      if args.isEmpty then return none
      let inner := args[args.size - 1]!
      -- Resolve widths (USize/ISize → read from usize-width option).
      let usizeW ← getUsizeWidth
      let srcW := (uintWidth? srcName).getD usizeW
      let tgtW := (uintWidth? tgtName).getD usizeW
      let sx ← termTranslator inner
      if tgtW == srcW then
        -- Same-width → identity (these are already handled by ctor/proj for signed ones;
        -- we reach here only for USize.toUInt64 / UInt64.toUSize which are unsigned same-width).
        return some sx
      else if tgtW > srcW then
        -- Guard: signed sources must widen via BitVec.signExtend (path A), not zero_extend.
        -- If a signed-widening name were ever registered in opaqueFuns, it would silently
        -- produce an unsound zero-extension; this guard converts that silent bug into an error.
        if [``Int8, ``Int16, ``Int32, ``Int64, ``ISize].contains srcName then
          throwEnvError "translateUIntConv?: signed widening of {srcName} must sign-extend (path-A via BitVec.signExtend); not handled here"
        -- Widen — unsigned source → zero_extend
        return some (mkSimpleSmtAppN (bvzeroExtendSymbol (tgtW - srcW)) #[sx])
      else
        -- Narrow → extract low tgtW bits
        return some (mkSimpleSmtAppN (bvextractSymbol (tgtW - 1) 0) #[sx])

    /-- Detect `BitVec.ofNat <non-literal-width> (Expr.lit (natVal v))` as a USize/ISize literal.
        `System.Platform.numBits` reduces to `(System.Platform.getNumBits ()).val` which is an
        `Expr.proj` — never a Nat literal — so `isBitVecValue?` cannot fire.
        The width arg is ignored — this is only reached for USize/ISize ctor args whose
        underlying width is read from the usize-width option. -/
    translatePlatformBvLit? (bvExpr : Expr) : TranslateEnvT (Option SmtTerm) := do
      match bvExpr with
      | Expr.app (Expr.app (Expr.const ``BitVec.ofNat _) _wExpr)
          (Expr.lit (Literal.natVal v)) =>
          -- Width is read from the usize-width option (default 64).
          let w ← getUsizeWidth
          return some (bitvecLitSmt (v % (2 ^ w)) w)
      | _ => return none

    /-- Fin.val / Fin.mk are identity at SMT level (Fin_n aliases Int).
        `@Fin.val {n} x` → translate x (last arg, index args.size-1).
        `@Fin.mk {n} v proof` → translate v (index 1, proof dropped). -/
    translateFinOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Fin.val =>
          -- @Fin.val {n} x — explicit arg is the Fin value, at index args.size - 1
          if args.size ≥ 1 then return some (← termTranslator args[args.size - 1]!) else return none
      | ``Fin.mk =>
          -- @Fin.mk {n} v proof — value v is at index 1
          if args.size ≥ 2 then return some (← termTranslator args[1]!) else return none
      | _ => return none

    /-- Translate modular arithmetic on `Fin n` (opaque in the optimizer).

        Arg layout for all three ops: `@Fin.add {n} a b` → args := #[n, a, b]
        where n is the implicit bound (must be a Nat literal at translation time).

        - `Fin.add a b` → `(a + b) % n`   (matches Lean's `Fin.add`)
        - `Fin.mul a b` → `(a * b) % n`   (matches Lean's `Fin.mul`)
        - `Fin.sub a b` → `(n - b + a) % n` (matches Lean's `Fin.sub`: stays non-negative
            since `b < n`, so `n - b ≥ 1`; no Nat truncation mismatch in Int SMT) -/
    -- `SMTArray`'s structure constructor/projection (`SMTArray.ofArray`/`.toArray`)
    -- cross between the SMT array-theory sort `(Array Int σ)` and the opaque-datatype
    -- encoding of raw `Array α` — incompatible encodings, so they cannot be translated.
    -- Reject with a clean error (mirrors `translateFinType`'s treatment of unsupported
    -- Fin) rather than emitting an unknown SMT constant. Only symbolic `SMTArray`
    -- variables + `get`/`set` are supported.
    translateSMTArrayCtor? (n : Name) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Blaster.SMTArray.ofArray | ``Blaster.SMTArray.toArray =>
          throwEnvError "translateApp: concrete SMTArray construction/unwrapping ({n}) is not supported; use symbolic `SMTArray` variables with `.get`/`.set`"
      | _ => return none

    /-- Collect the elements of a literal `List` spine (`List.cons`/`List.nil`) as Exprs.
        The spine must be concrete; a symbolic tail (e.g. a `List` variable) is rejected. -/
    collectListElems (l : Expr) : TranslateEnvT (Array Expr) := do
      let mut cur := l
      let mut elems := #[]
      while true do
        match cur.getAppFnArgs with
        | (``List.cons, #[_, h, t]) => elems := elems.push h; cur := t
        | (``List.nil, _)           => break
        | _ => throwEnvError "translateArrayLit?: `Array.mk` requires a literal list spine; symbolic list argument {reprStr cur} is unsupported (use a symbolic `Array`/`SMTArray` variable with `.get`/`.set`/`.size`)"
      return elems

    /-- Translate a concrete array constructor `@Array.mk α [e₀, …, eₙ₋₁]` into the
        size-aware datatype-pair encoding (see `translateArrayType`): a `data` array
        built as a store-chain over the per-instance `@dflt` const, plus a literal `size`.
        Required because the `Array α` *type* is routed to the pair model, so a literal of
        that type must produce a pair term `(@mkSMTArray_v data size)`, not the raw
        `Array.mk` constructor (whose SMT symbol is never declared for the pair sort). -/
    translateArrayLit? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      unless n == ``Array.mk do return none
      if args.size != 2 then throwEnvError "translateArrayLit?: `Array.mk` expects 2 args (elemType, list), got {args.size}"
      let arrTy ← inferTypeEnv e
      let _ ← translateType termTranslator arrTy   -- idempotent: ensures pair datatype declared + names cached
      let some names := (← get).smtEnv.smtArrNamesCache.get? arrTy
        | throwEnvError "translateArrayLit?: SMTArray names not cached for {reprStr arrTy}"
      let elemSort ← translateType termTranslator args[0]!
      let dataSort := arraySort #[intSort, elemSort]
      let elems ← collectListElems args[1]!
      let mut data := constArraySmt dataSort (smtSimpleVarId names.dfltSym)
      for h : i in [0 : elems.size] do
        let v ← termTranslator elems[i]
        data := storeSmt data (natLitSmt i) v
      return some (smtArrCtorApp names.ctorSym data (natLitSmt elems.size))

    /-- Translate the SMTArray AND raw-`Array` ops against the size-aware
        datatype-pair encoding declared by `translateArrayType`.

        `SMTArray.get`/`set`/`size` are *definitionally* `Array.get!`/`set!`/`size`,
        so both families emit the same terms; raw `Array` shares this path (Spec 2).
        Handled: `SMTArray.get`/`set`/`size`, `Array.get!`/`getD`/`set!`/
        `setIfInBounds`/`size`.

        The pair is `(@mkSMTArray_v (data (Array Int σ)) (size Int))` with a
        per-instance out-of-bounds `default` constant `@dfltSMTArray_v`. The SMT
        terms below mirror the bounds-checked Lean semantics:
          - `get!/get a i` → `(ite (and (<= 0 i) (< i (size a))) (select (data a) i) dflt)`
          - `getD a i d`   → as above but the out-of-bounds branch is the EXPLICIT
                             default `d`, not `@dflt`
          - `set/set!/setIfInBounds a i v`
                           → `(@mkSMTArray_v (ite inB (store (data a) i v) (data a)) (size a))`
          - `size a`       → `(size a)`

        Arg layouts (all args incl. implicits). `get!`/`SMTArray.get` carry an
        `[Inhabited α]` instance (array at [2]); every other op has the array at [1]:
          - `@SMTArray.get α inst a i` / `@Array.get! α inst a i` → #[α, inst, a, i]
          - `@Array.getD α a i d`                                → #[α, a, i, d]
          - `@SMTArray.set/@Array.set!/@Array.setIfInBounds α a i v` → #[α, a, i, v]
          - `@SMTArray.size/@Array.size α a`                     → #[α, a]

        The names are looked up by `inferTypeEnv` of the ARRAY argument (its binder
        type is exactly the `SMTArray α`/`Array α` Expr used as the cache key in
        `translateArrayType`). `translateType` is called first (idempotent cache hit)
        to guarantee the datatype is declared and the names are cached; a miss is an
        internal error (we never silently re-declare). -/
    translateSMTArrayOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Blaster.SMTArray.get | ``Blaster.SMTArray.set | ``Blaster.SMTArray.size
      | ``Array.get! | ``Array.getD | ``Array.set! | ``Array.setIfInBounds | ``Array.size => do
        -- Array layout: `get!`/`SMTArray.get` carry `[Inhabited α]`, so the array
        -- arg is at index 2; all others have the array at index 1.
        let arrArgIdx :=
          if n == ``Blaster.SMTArray.get || n == ``Array.get! then 2 else 1
        let arrTy ← inferTypeEnv args[arrArgIdx]!     -- the (SMT)Array α binder type = the cache key
        let _ ← translateType termTranslator arrTy    -- idempotent: ensures datatype declared + names cached
        let some names := (← get).smtEnv.smtArrNamesCache.get? arrTy
          | throwEnvError "translateSMTArrayOp?: SMTArray names not cached for {reprStr arrTy}"
        -- 0 <= i < size: shared bounds guard used by both get and set arms.
        let inBounds := fun (a i : SmtTerm) =>
          andSmt (leqSmt (natLitSmt 0) i) (ltSmt i (smtSelectorApp names.sizeSel a))
        match n with
        | ``Blaster.SMTArray.get | ``Array.get! =>
            if args.size != 4 then throwEnvError "translateSMTArrayOp?: {n} expects 4 args, got {args.size}"
            let a ← termTranslator args[2]!
            let i ← termTranslator args[3]!
            let hit := selectSmt (smtSelectorApp names.dataSel a) #[i]
            return some (iteSmt (inBounds a i) hit (smtSimpleVarId names.dfltSym))
        | ``Array.getD =>
            -- `@Array.getD α a i d` → array@1, index@2, EXPLICIT default@3 (NOT @dflt).
            if args.size != 4 then throwEnvError "translateSMTArrayOp?: Array.getD expects 4 args, got {args.size}"
            let a ← termTranslator args[1]!
            let i ← termTranslator args[2]!
            let d ← termTranslator args[3]!
            let hit := selectSmt (smtSelectorApp names.dataSel a) #[i]
            return some (iteSmt (inBounds a i) hit d)
        | ``Blaster.SMTArray.set | ``Array.set! | ``Array.setIfInBounds =>
            if args.size != 4 then throwEnvError "translateSMTArrayOp?: {n} expects 4 args, got {args.size}"
            let a ← termTranslator args[1]!
            let i ← termTranslator args[2]!
            let v ← termTranslator args[3]!
            let newData := iteSmt (inBounds a i)
              (storeSmt (smtSelectorApp names.dataSel a) i v) (smtSelectorApp names.dataSel a)
            return some (smtArrCtorApp names.ctorSym newData (smtSelectorApp names.sizeSel a))
        | ``Blaster.SMTArray.size | ``Array.size =>
            if args.size != 2 then throwEnvError "translateSMTArrayOp?: {n} size expects 2 args, got {args.size}"
            let a ← termTranslator args[1]!
            return some (smtSelectorApp names.sizeSel a)
        | _ => return none
      | _ => return none

    /-- Reject unsupported Vector constructs with clean, actionable errors.

        `Vector.mk` and `Vector.toArray` cross between the SMT array-theory sort
        `(Array Int σ)` used for `Vector α n` and the opaque-datatype encoding of raw
        `Array α` — incompatible encodings. Phase 2 made raw `Array α` an opaque SMT
        datatype, so `Vector.mk`/`.toArray` cannot be identity as the spec originally
        planned.  Without this arm (and the companion guard in `translateProj`), these
        names silently produce invalid SMT (`unknown constant Vector.mk.0`) that Z3
        rejects with an unactionable error.

        Higher-order ops (`map`, `zipWith`, …) are Non-Goals and reach this path
        pre-unfolded by the optimizer, so their head constant is no longer `Vector.map`
        by the time translateApp runs; they hit the `Vector.mk` arm transitively.
        `foldl` unfolds through a different path (loop bound `<` leaks) and surfaces
        an internal `translateNonOpaqueType: inductive info expected for LT.lt` error.
        No separate arms are added for either group (arms would be dead code).

        NOTE: this arm sits AFTER `translateVectorOp?` so the supported ops
        (get/set/push/replicate) are already handled and never reach here.
    -/
    translateVectorUnsupported? (n : Name) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Vector.mk | ``Vector.toArray =>
          throwEnvError "translateApp: concrete Vector construction/unwrapping ({n}) is not supported (crosses the array-theory and opaque-Array encodings); use Vector get/set/push/replicate on symbolic Vector variables"
      | _ => return none

    /-- Translate Vector ops to SMT array theory.

        Arg layouts (all args after Expr.withApp, including implicit ones):
          - `@Vector.get {α} {n} v i`         → args[0]=α, args[1]=n, args[2]=v, args[3]=i
                 SMT: `(select v i)`
          - `@Vector.set {α} {n} v idx x h`   → args[0]=α, args[1]=n, args[2]=v,
                                                  args[3]=idx, args[4]=x, args[5]=h
                 SMT: `(store v idx x)`  (proof `h` is dropped)
          - `@Vector.push {α} {n} v x`        → args[0]=α, args[1]=n, args[2]=v, args[3]=x
                 SMT: `(store v n x)`  where `n` is the literal current length (from args[1])
          - `@Vector.replicate {α} n x`       → args[0]=α, args[1]=n, args[2]=x
                 SMT: `((as const (Array Int σ)) x)` where σ is the translated element sort

        `Vector.get` and `Vector.set` are also called with a `Fin n` index (for `get`) or a
        Nat literal (for `set`); both pass through `termTranslator` directly — `Fin.val`/`Fin.mk`
        are identity at SMT level (see `translateFinOp?`).
    -/
    translateVectorOp? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Vector.get =>
          -- @Vector.get {α} {n} v i — 4 args total, v at [2], i at [3]
          if args.size != 4 then
            throwEnvError "translateVectorOp?: fully applied Vector.get expected but got {args.size} args"
          let sv ← termTranslator args[2]!
          let si ← termTranslator args[3]!
          return some (selectSmt sv #[si])
      | ``Vector.set =>
          -- @Vector.set {α} {n} v idx x h — 6 args total, v at [2], idx at [3], x at [4], h at [5]
          if args.size != 6 then
            throwEnvError "translateVectorOp?: fully applied Vector.set expected but got {args.size} args"
          let sv  ← termTranslator args[2]!
          let si  ← termTranslator args[3]!
          let sx  ← termTranslator args[4]!
          return some (storeSmt sv si sx)
      | ``Vector.push =>
          -- @Vector.push {α} {n} v x — 4 args total, n at [1], v at [2], x at [3]
          if args.size != 4 then
            throwEnvError "translateVectorOp?: fully applied Vector.push expected but got {args.size} args"
          let some nVal := isNatValue? (← whnf args[1]!)
            | throwEnvError "translateVectorOp?: literal length expected for Vector.push but got {reprStr args[1]!}"
          let sv ← termTranslator args[2]!
          let sx ← termTranslator args[3]!
          return some (storeSmt sv (natLitSmt nVal) sx)
      | ``Vector.replicate =>
          -- @Vector.replicate {α} n x — 3 args total, α at [0], n at [1], x at [2]
          if args.size != 3 then
            throwEnvError "translateVectorOp?: fully applied Vector.replicate expected but got {args.size} args"
          -- The result sort is (Array Int σ); σ comes from the element type α (args[0])
          let elemSort ← translateType termTranslator args[0]!
          let arrSort  := arraySort #[intSort, elemSort]
          let sx ← termTranslator args[2]!
          return some (constArraySmt arrSort sx)
      | _ => return none

    /-- Reject BitVec-family conversion-out-of-fixed-width ops with an actionable error.
        `BitVec.toNat`, `BitVec.toInt`, and `BitVec.toFin` convert a fixed-width value
        to an unbounded type (Nat, Int, or Fin), which would require Z3-specific
        `bv2int`/`int2bv` extensions and is a declared Non-Goal.  Intercept here so the
        user sees a clear message instead of the raw `translateApp: unexpected application`
        dump produced by the fallthrough.

        NOTE: this arm must sit AFTER `translateBitVecShift?` in the dispatch chain.
        `translateBitVecShift` consumes `BitVec.toNat y` as a shift-amount sub-expression
        (via `isBitVecToNat?`) before the head `f` ever reaches `translateApp`.  Only a
        standalone `x.toNat`/`x.toInt`/`x.toFin` application whose head is one of these
        names arrives here, so there is no clash. -/
    translateUnsupportedConv? (n : Name) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``BitVec.toNat | ``BitVec.toInt | ``BitVec.toFin =>
          throwEnvError "translateApp: conversion out of the fixed-width domain ({n}) is not supported (see Non-Goals); reason over the fixed-width value directly"
      | _ => return none

    translateFinArith? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Fin.add | ``Fin.mul | ``Fin.sub =>
          if args.size != 3 then
            throwEnvError "translateFinArith?: fully applied {n} expected but got {args.size} arguments"
          -- WHNF-reduce the bound to normalize OfNat/proj forms, matching translateFinType.
          let some bound := isNatValue? (← whnf args[0]!)
            | throwEnvError "translateFinArith?: literal Fin bound expected for {n}"
          let ta ← termTranslator args[1]!
          let tb ← termTranslator args[2]!
          let modN := natLitSmt bound
          -- NOTE: bound 0 is unreachable for inhabited terms — `Fin 0` has no
          -- values, so any Fin.add/mul/sub term sits under the false Fin_0 guard.
          let body ← match n with
            | ``Fin.add => pure (addSmt ta tb)
            | ``Fin.mul => pure (mulSmt ta tb)
            | ``Fin.sub => pure (addSmt (subSmt modN tb) ta)
            | _ => throwEnvError "translateFinArith?: unexpected op {n}"
          return some (modSmt body modN)
      | _ => return none

    translateInductivePredicate? (f : Expr) (n : Name) (_args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isInductivePredicate n) then
        throwEnvError "translateApp: Inductive predicate not yet supported: {reprStr f}"
      return none

    translateTheorem (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if !(← isTheorem n) then return none
      let ConstantInfo.thmInfo info ← getConstEnvInfo n | return none
      -- check if e has sorry demonstration and trigger error if this is the case
      hasSorryTheorem e "translateApp: Theorem {n} has `sorry` demonstration"
      termTranslator (← optimizeExpr' (betaForAll info.type args))

/-- Given `e := λ (x₁ : t₁) → λ (xₙ : tₙ) => b`, perform the following:
     - let V := [ v | v ∈ getFVarsInExpr b ∧ ¬ isType v.type ∧ ¬ isClassConstraintExpr v.type ∧ ¬ isTopLevelFVar v ]
     - let A := [x₁, ..., xₙ]
     - let (x₁, st₁) ... (xₘ, stₘ) := [(A[i], translateFunLambdaParamType tᵢ termTranslator) | i ∈ [0..n] ∧ isExplicit A[i]]
     - let rt ← translateFunLambdaParamType (← inferTypEnv b) termTranslator
     - let n ← mkFreshId
     - let FunArrowType := ArrowTN st₁ ... stₘ rt
     - let decl ← generateFunInstDeclAux (← inferTypeEnv e) FunArrowType
     - let some @apply{k} := decl.applyInstName
     - let sb := termTranslator b
     - When V = ∅
        - declare smt function `(declare-const @lambda{n} FunArrowType)`
        - assert the following proposition to properly constrain @lambda{n}:
          `(assert (forall ((x₁ st₁) ... (xₘ stₘ))
             (! (= (@apply{k} @lambda{n} x₁ ... xₘ) sb)
               :pattern ((@apply{k} @lambda{n} x₁ ... xₘ))
               :qid @lambda{n]_def_cstr)))`
        - return `smtSimpleVarId @lambda{n}`
     - When V ≠ ∅
        - let (y₁, yt₁) ... (yₖ, ytₖ) := [(V[i], translateFunLambdaParamType V[i].type termTranslator) | i ∈ [0..V.size-1]]
        - let GlobalArrowType := ArrowTN yt₁ ... ytₖ FunArrowType
        - let [v₁, ..., vₖ] = V
        - let globalType ← ∀ v₁ → ... ∀ vₖ → outParam (← inferTypeEnv e)
        - let globalDecl ← generateFunInstDeclAux globalType GlobalArrowType
        - let some @apply{n} := globalDecl.applyInstName
        - declare smt function `(declare-const @global_lambda{n} GlobalArrowType)`
        - assert the following proposition to properly constrain @global_lambda{n}!
           - `(assert (forall ((y₁, yt₁) ... (yₖ, ytₖ) (x₁, st₁) ... (xₘ, stₘ))
               (! (= (@apply{k} (@apply{n} @global_lambda{n} y₁ ... yₖ) x₁ ... xₘ) sb)
                  :pattern ((@apply{k} (@apply{n} @global_lambda{n} y₁ ... yₖ) x₁ ... xₘ))
                  :qid @global_lambda{n}_def_cstr)))`
       - return `(@apply{n} @global_lambda{n} y₁ ... yₖ)`
-/
def translateLambda
  (e : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
 let pInfo ← getFunEnvInfo e
 Optimize.lambdaTelescope e fun fvars b => do
   let mut svars := (#[] : SortedVars)
   for h1 : i in [:fvars.size] do
     let fv := fvars[i]
     let decl ← getFVarLocalDecl fv
     updateQuantifiedFVarsCache fv.fvarId! false
     if pInfo.paramsInfo[i]!.isExplicit then
       let st ← translateFunLambdaParamType decl.type termTranslator
       svars := svars.push (← fvarIdToSmtSymbol fv.fvarId!, st)
   let bodyType ← inferTypeEnv b
   let rt ← translateFunLambdaParamType bodyType termTranslator
   let v ← mkFreshId
   let lambdaName := mkReservedSymbol s!"@lambda{v}"
   let lamType ← Optimize.mkForallFVars' fvars bodyType
   let arrowT ← declareArrowTypeSort (fvars.size + 1)
   let funArrowType := paramSort arrowT ((Array.map (λ s => s.2) svars).push rt)
   -- generate apply function with corresponding congruence assertions (or retrieving if already declared).
   let decl ← generateFunInstDeclAux lamType funArrowType
   let some applyName := decl.applyInstName
       | throwEnvError "translateLambda: @apply instance function expected !!!"
   let lvars ← retrieveLocalFVars (getLambdaBody e)
   let sb ← termTranslator b
   if lvars.isEmpty then
     -- declare lambda function
     declareConst lambdaName funArrowType
     -- asserting lambda definition
     let qidName := appendSymbol lambdaName "def_cstr"
     let lamId := smtSimpleVarId lambdaName
     let applyArgs := Array.foldl (λ acc s => acc.push (smtSimpleVarId s.1)) #[lamId] svars
     let applyTerm := mkSimpleSmtAppN applyName applyArgs
     let forallBody := eqSmt applyTerm sb
     assertTerm (mkForallTerm none svars forallBody (some #[mkPattern #[applyTerm], mkQid qidName]))
     return lamId
   else
    let mut gvars := (#[] : SortedVars)
    for h2 : i in [:lvars.size] do
     let fv := lvars[i]
     let decl ← getFVarLocalDecl fv
     let st ← translateFunLambdaParamType decl.type termTranslator
     gvars := gvars.push (← fvarIdToSmtSymbol fv.fvarId!, st)
    let arrowT ← declareArrowTypeSort (lvars.size + 1)
    let globalArrowType := paramSort arrowT ((Array.map (λ s => s.2) gvars).push funArrowType)
    -- wrapping lamType within `outParam` to properly generate function instance
    let globalType ← Optimize.mkForallFVars' lvars (mkApp (mkConst ``outParam) lamType)
    -- generate apply function with corresponding congruence assertions for global lambda
    let globalDecl ← generateFunInstDeclAux globalType globalArrowType
    -- declare global lambda function `(declare-const @global_lambda{n} GlobalArrowType)`
    let globalName := mkReservedSymbol s!"@global_lambda{v}"
    let globalId := smtSimpleVarId globalName
    declareConst globalName globalArrowType
    -- asserting global lambda definition
    let some globalApplyName := globalDecl.applyInstName
        | throwEnvError "translateLambda: @apply instance function expected !!!"
    let gArgs := Array.foldl (λ acc s => acc.push (smtSimpleVarId s.1)) #[globalId] gvars
    let globalAppTerm  := mkSimpleSmtAppN globalApplyName gArgs
    let applyArgs := Array.foldl (λ acc s => acc.push (smtSimpleVarId s.1)) #[globalAppTerm] svars
    let applyTerm := mkSimpleSmtAppN applyName applyArgs
    let qidName := appendSymbol globalName "def_cstr"
    let g_patterns := some #[mkPattern #[applyTerm], mkQid qidName]
    gvars := Array.foldl (λ acc s => acc.push s) gvars svars
    assertTerm (mkForallTerm none gvars (eqSmt applyTerm sb) g_patterns)
    return globalAppTerm

 where
   retrieveLocalFVars (b : Expr) : TranslateEnvT (Array Expr) := do
     -- Need to ensure that fvars are unique
     let (fvars, _) ← updateGenericArgs b #[] Std.HashSet.emptyWithCapacity
     let mut lvars := #[]
     for h : i in [:fvars.size] do
       let p := fvars[i]
       let decl ← getFVarLocalDecl p
       if !(← isTopLevelFVar p.fvarId!) && !(isTypeUniverse decl.type) && !(← isClassConstraintExpr decl.type) then
         lvars := lvars.push p
     return lvars

/-- Given `n` a projection name, `idx` a projection and `p` the projection application term,
    perform the following:
      - When `n` is not an inductive datatype (i.e., structure definition)
         - return ⊥
      - When `n` has more than one ctor `c` (i.e., structure only has one defined ctor with each field as arguments)
         - return ⊥
      - Otherwise:
          - return smt term application `(c.idx p)`
-/
def translateProj
  (n : Name) (idx : Nat) (p : Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
 -- UInt/Int family types are erased to their underlying `(_ BitVec w)` sort.
 -- Their projections (`.toBitVec` / `.toUInt8` etc.) are identity: translate the inner value.
 let isUIntFamilyProj := isUIntFamilyName n
 if isUIntFamilyProj then
   return (← termTranslator p)
 -- `Vector` structure projections (`.toArray`, `.size_toArray`) cross between the SMT
 -- array-theory sort `(Array Int σ)` and the opaque-datatype encoding of raw `Array α`.
 -- Without this guard the proj elaborates to selector symbol `Vector.mk.0` which Z3
 -- rejects with an unactionable `unknown constant` error.
 if n == ``Vector then
   throwEnvError "translateProj: Vector.toArray/size_toArray projection is not supported (crosses the array-theory and opaque-Array encodings); use Vector get/set/push/replicate on symbolic Vector variables"
 let selectorSym := mkCtorSelectorSymbol (← getProjectionCtor n) idx
 return (mkSimpleSmtAppN selectorSym #[← termTranslator p])

end Blaster.Smt
