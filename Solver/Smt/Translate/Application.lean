import Lean
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Optimize.Telescope
import Solver.Smt.Env
import Solver.Smt.Translate.Match
import Solver.Smt.Translate.Quantifier


open Lean Meta Solver.Optimize

namespace Solver.Smt

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
        - Solver.decide'
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
  | ``Solver.dite' => getOpaqueSmtEquivFun f iteSymbol
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
  | ``LE.le
  | ``Nat.ble => getOpaqueSmtEquivFun f leqSymbol
  | ``LT.lt =>
        if Nat.blt args.size 2 then throwEnvError "translateOpaqueFun: at least two arguments expected for Lt.lt"
        if isStringType args[0]!
        then return .SimpleIdent strLtSymbol
        else getOpaqueSmtEquivFun f ltSymbol
  | ``Nat.sub => translateNatSub f
  | ``String.append => getOpaqueSmtEquivFun f strAppendSymbol
  | ``String.length => getOpaqueSmtEquivFun f strLengthSymbol
  | ``String.replace => getOpaqueSmtEquivFun f strReplaceAllSymbol
  | _ => throwEnvError "translateOpaqueFun: unexpected opaque operator {n}"


/-- Helper function for createAppN -/
def createAppNAux (pInfo : FunEnvInfo) (s : Sum SmtQualifiedIdent SmtTerm)
  (args : Array Expr) (termTranslator : Expr → TranslateEnvT SmtTerm)
  (isHOF := false) : TranslateEnvT SmtTerm := do
  let mut genArgs := #[]
  let nbSize := if args.size < pInfo.paramsInfo.size then args.size else pInfo.paramsInfo.size
  for i in [:nbSize] do
    if pInfo.paramsInfo[i]!.isExplicit then
       genArgs := genArgs.push (← termTranslator args[i]!)
  if genArgs.size == 0
  then genUnapplied s
  else genApplied s genArgs

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

    genApplied (id : Sum SmtQualifiedIdent SmtTerm) (sargs : Array SmtTerm) : TranslateEnvT SmtTerm := do
      if isHOF then
        let applyInst ← getApplyInstName pInfo.type
        match id with
        | Sum.inl qi => return mkSimpleSmtAppN applyInst (#[(.SmtIdent qi)] ++ sargs)
        | Sum.inr st => return mkSimpleSmtAppN applyInst (#[st] ++ sargs)
           -- case when f corresponds to a function in a ctor argument.
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
                - return `asArraySmt s`
             - Otherwise (i.e., only a defined function expected)
                 - return ⊥
      - When `∃ i ∈ [0..n], isExplicit xᵢ,`
         let A := [x₀,..., xₙ]
         let B := [termTranslator A[i] | i ∈ [0..n] ∧ isExplicit A[i]]
           - When isHOF:
              - When `isSmtQualifiedIdent s`
                 - return `selectSmt (.SmtIdent s) B`
              - Otherwise (i;e., case when f corresponds to a function in a ctor argument)
                  - return `selectSmt s B`
           - Otherwise:
              - When `isSmtQualifiedIdent s`
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
     - return `translateType termTranslator t optionsForFunLambdaParam`
    An error is triggered if `t` corresponds to the type of an implicit argument.
-/
def translateFunLambdaParamType
  (t : Expr) (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SortExpr := do
  translateType termTranslator t optionsForFunLambdaParam

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

/-- Given `f` corresponding to either an undeclared class function or an axiom function,
    `params` its corresponding implicit/explicit parameters and `s` its corresponding smt symbol,
     perform the following:
       - Let `∀ α₀ → ∀ α₁ ... → αₙ` := inferUndecFunType (← getFunEnvInfo f).type params
       - declare smt function `declare-fun s ((st₀) .. (stₙ₋₁)) stₙ)`
     where ∀ i ∈ [0..n], αᵢ translates to Smt type stᵢ
-/
def generateUndeclaredFun
  (f : Expr) (s : SmtSymbol) (params : ImplicitParameters)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT Unit := do
  let pInfo ← getFunEnvInfo f
  -- infer fun type and removing implicit arguments (i.e., even class constraints)
  let funType := inferUndeclFunType pInfo.type params
  Optimize.forallTelescope funType fun fvars retType => do
    let mut pargs := (#[] : Array SortExpr)
    for h : i in [:fvars.size] do
      let decl ← getFVarLocalDecl fvars[i]
      let st ← translateFunLambdaParamType decl.type termTranslator
      pargs := pargs.push st
    let ret ← translateFunLambdaParamType retType termTranslator
    declareFun s pargs ret

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
     - When `isAxiom n`
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
    if (← isInductiveTypeExpr e) then
      throwEnvError "translateConst: unexpected inductive datatype {reprStr e}"
    if isForbiddenUnappliedConst n then
      throwEnvError "translateConst: unexpected name expression {reprStr e}"
    if (← isMatchExpr e) then
      throwEnvError "translateConst: unexpected match function passed as argument {n}"
    if let some r ← translateCtor n then return r
    if (← hasImplicitArgs e) then
      throwEnvError "translateConst: unexpected implicit arguments for function {reprStr e}"
    if let some r ← translateDefineFun? n then return r
    if let some r ← translateTheorem? n then return r
    if let some r ← translateAxiom? n then return r
    throwEnvError "translateConst: only opaque/recursive functions and theorems expected but got {reprStr e}"


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

    translateAxiom? (n : Name) : TranslateEnvT (Option SmtTerm) := do
       let ConstantInfo.axiomInfo info ← getConstEnvInfo n | return none
       if ← isPropEnv info.type then
         throwEnvError "translateConst: Unexpected Axiom of type Prop {n}"
       match (← get).smtEnv.options.axiomMap.get? n with
       | some s => return (smtSimpleVarId s)
       | none =>
           if ← isFunType info.type then
             termTranslator (← Optimize.etaExpand e)
           else
             let smtSym ← updateAxiomMap n
             let t' ← removeTypeAbbrev info.type
             let smtType ← translateTypeAux termTranslator t'
             -- declare free variable at top level
             declareConst smtSym smtType
             let pTerm ← createPredQualifierApp smtSym t'
             assertTerm pTerm
             return (smtSimpleVarId smtSym)

    isForbiddenUnappliedConst (n : Name) : Bool :=
      match n with
      | ``Exists
      | ``Solver.decide'
      | ``Solver.dite'
      | _ => isForbiddenConst n



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
         throwEnvError "translateApp: unexpected application {reprStr e}"

    | Expr.fvar _ => -- case for HOF
         let .SmtIdent smtId ← translateFreeVar f termTranslator
           | throwEnvError "translateApp: SmtIdent expected for {reprStr f}"
         createAppN f (Sum.inl smtId) args termTranslator (isHOF := true)

    | Expr.mdata .. => -- case when f is defined as a ctor argument and is used in a ctor proposition
        match toTaggedCtorSelector? f with
        | some (Expr.app (Expr.const s _) _) =>
            match (← get).smtEnv.funCtorCache.get? s with
            | none => throwEnvError "translateApp: FunEnvInfo expected for {reprStr s}"
            | some pInfo =>
               createAppNAux pInfo (← Sum.inr <$> termTranslator f) args termTranslator (isHOF := true)
        | _ => throwEnvError "translateApp: ctor selector tag expected but got {reprStr f}"

    | Expr.proj .. => -- case when f is a function within a ctor.
         createAppN f (← Sum.inr <$> termTranslator f) args termTranslator (isHOF := true)

    | _ => throwEnvError "translateApp: unexpected application {reprStr e}"

  where
    translateEq? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Eq =>
         if args.size == 2 then
           throwEnvError "translateEq?: unexpected partially applied Eq got {reprStr args}"
         if args.size == 1 then return (← termTranslator (← Optimize.etaExpand e))
         match args[1]! with
          | Expr.const ``true _ => termTranslator args[2]!
          | Expr.const ``false _ => termTranslator (mkApp (← mkBoolNotOp) args[2]!)
          | _ => createAppN f (← Sum.inl <$> translateOpaqueFun f n args) args termTranslator
       | _ => return none

    translateDITE? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Solver.dite' =>
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
       | ``Solver.decide' =>
            if args.size != 1 then
               throwEnvError "translateDecide?: unexpected partially applied {n} got {reprStr args}"
            termTranslator args[0]!
       | _ => return none

    translateRelational? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
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
        let ebody ← termTranslator b
        let env ← get
        if env.premises.size != 1 then
          throwEnvError "genExistsTerm: only one predicate qualifier premise expected but got {env.premises}"
        -- set patterns to none for now
        -- TODO: We need to check if e-pattern is necessary for existential
        return (mkExistsTerm none env.quantifiers (andSmt env.premises[0]! ebody) none)

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


    isAxiomOrUndeclFun (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT Bool := do
      match ← getFunBody f with
      | none => return (← getConstEnvInfo n).isAxiom
      | some fbody => isUndefinedClassFunApp (Expr.beta fbody args)

    translateAxiomOrUndeclFun? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isOpaqueFun n args) then return none
      if !(← isAxiomOrUndeclFun f n args) then return none
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
     - When V = ∅
        - declare smt function `(declare-const @lambda{n} FunArrowType)`

        - let sb := termTranslator b
        - assert the following proposition to properly constrain @lambda{n}:
          `(assert (forall ((x₁ st₁) ... (xₘ stₘ))
             (! (= (@apply{k} @lambda{n} x₁ ... xₘ) sb)
               :pattern ((@apply{k} @lambda{n} x₁ ... xₘ))
               :qid @lambda{n]_def_cstr)))`
        - return `smtSimpleVarId @lambda{n}`
     - When V ≠ ∅
        - let (y₁, yt₁) ... (yₖ, ytₖ) := [(V[i], translateFunLambdaParamType V[i].type termTranslator) | i ∈ [0..V.size-1]]
        - let GlobalArrowType := ArrowTN yt₁ ... ytₖ FunArrowType
        - declare smt function `(declare-const @global_lambda{n} GlobalArrowType)`
        - declare global apply function `(declare-fun @global_apply{n} (GlobalArrowType yt₁ ... ytₖ) FunArrowType)`
        - assert the following proposition to properly constrain @lambda{n} and @global_lambda{n}!
           - `(assert (forall ((y₁, yt₁) ... (yₖ, ytₖ) (x₁, st₁) ... (xₘ, stₘ))
               (! (= (@apply{k} (@global_apply{n} @global_lambda{n} y₁ ... yₖ) x₁ ... xₘ) sb)
                  :pattern ((@apply{k} (@global_apply{n} @global_lambda{n} y₁ ... yₖ) x₁ ... xₘ))
                  :qid @global_lambda{n}_def_cstr)))`
       - return `(@global_apply{n} @global_lambda{n} y₁ ... yₖ)`
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
   -- generate apply function with corresponding congruence assertions (or retriving if already declared).
   let decl ← generateFunInstDeclAux lamType funArrowType
   let some applyName := decl.applyInstName | throwEnvError "translateLambda: @apply instance function expected !!!"
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
    -- declare global lambda function `(declare-const @global_lambda{n} GlobalArrowType)`
    let globalName := mkReservedSymbol s!"@global_lambda{v}"
    let globalId := smtSimpleVarId globalName
    declareConst globalName globalArrowType
    -- declare global apply function `(declare-fun @global_apply{n} (GlobalArrowType yt₁ ... ytₖ) FunArrowType)`
    let globalApplyName := mkReservedSymbol s!"@global_apply{v}"
    let declArgs := Array.foldl (λ acc s => acc.push s.2) #[globalArrowType] gvars
    declareFun globalApplyName declArgs funArrowType
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
     let fvars ← getFVarsInExpr b
     let mut lvars := #[]
     for h : i in [:fvars.size] do
       let p := fvars[i]
       let decl ← getFVarLocalDecl p
       if !(← isTopLevelFVar p.fvarId!) && !decl.type.isType && !(← isClassConstraintExpr decl.type) then
         lvars := lvars.push p
     return lvars

/-- Given `n` a projection name, `idx` a projection and `p` the projection application term,
    perform the following:
      - When `n` is not an inductive datatype (i.e., structure definition)
         - return ⊥
      - When `n` has more than one ctor `c` (i.e., structure only has one defined ctor with each field as arguments)
         - return ⊥
      - Otherwise:
          - return smt term application `(c.idx+1 p)`
-/
def translateProj
  (n : Name) (idx : Nat) (p : Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let ConstantInfo.inductInfo indVal ← getConstEnvInfo n
    | throwEnvError "translateProj: induction info expected for {n}"
  match indVal.ctors with
  | [c] =>
      let selectorSym := mkCtorSelectorSymbol c (idx+1)
      return (mkSimpleSmtAppN selectorSym #[← termTranslator p])
  | _ => throwEnvError "translateProj: only one ctor expected for structure for {n}"

end Solver.Smt
