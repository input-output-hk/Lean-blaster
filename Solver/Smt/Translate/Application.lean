import Lean
import Solver.Optimize.Rewriting.OptimizeITE
import Solver.Smt.Env
import Solver.Smt.Translate.Quantifier


open Lean Meta Solver.Optimize

namespace Solver.Smt

/-- Generate an smt symbol from a given function  name. -/
def funNameToSmtSymbol (funName : Name) : SmtSymbol :=
  mkNormalSymbol s!"@{funName}"


/-- list of Lean operators that must have a defined Smt function during translation.
-/
def definedSmtOperators : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [ ``Int.ediv,
    ``Int.emod,
    ``Int.div,
    ``Int.mod,
    ``Int.fdiv,
    ``Int.fmod,
    ``Int.toNat,
    ``Nat.sub
  ]

/-- list of Lean operators expected to be fully applied at translation phase. -/
def fullyAppliedConst : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [ ``And,
    ``Or,
    ``Not,
    ``ite,
    ``Int.add,
    ``Int.neg,
    ``Int.mul,
    ``Int.toNat,
    ``Int.div,
    ``Int.mod,
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
    ``Nat.pow
  ]

/-- Return `true` if `n` must have a defined Smt function during translation. -/
def hasSmtDefinedOperator (n : Name) : Bool :=
  definedSmtOperators.contains n

/-- Same as `hasSmtDefinedOperator` but `f` is expected to be a name an expression. -/
def hasSmtDefinedOperatorExpr (f : Expr) : Bool :=
  match f with
  | Expr.const n _ => definedSmtOperators.contains n
  | _ => false

/-- Return `true` when `e` corresponds to one of the following:
     - `e := Prop`; or
     - `e := α₁ → ... → αₙ → Prop`;
    Assume that `e` does not contain any let expression.
-/
def isArrowPropType (e : Expr) : Bool :=
  (Expr.getForallBody e).isProp


/-- Return `true` when `indName` corresponds to an inductive predicate. -/
def isInductivePredicate (indName : Name) : MetaM Bool := do
  let ConstantInfo.inductInfo indVal ← getConstInfo indName | return false
  return isArrowPropType indVal.type


/-- Given `f x₁ ... xₙ` a function instance and `n` a unique smt identifier for `f x₁ ... xₙ`,
    add entry `f x₁ ... xₙ := n` to `funInstCache`.
-/
def updateFunInstCacheBase (f : Expr) (n : SmtQualifiedIdent) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := {env.smtEnv with funInstCache := env.smtEnv.funInstCache.insert f n}
  set {env with smtEnv := smtEnv}

/-- Same as `updateFunInstCacheBase` but accepts an SmtSymbol as argument and returns
    the SmtQualifiedIden instance added to `funInstCache`.
-/
def updateFunInstCache (f : Expr) (n : SmtSymbol) : TranslateEnvT SmtQualifiedIdent := do
  let smtId := .SimpleIdent n
  updateFunInstCacheBase f smtId
  return smtId

/-- Perform the following actions:
     - Return `SimpleIdent "Nat.sub"` when entry `n := SimpleIdent "Nat.sub"` exists in `funInstCache`
     - Otherwise:
        - define Nat.sub Smt function (i.e., see `defineNatSub`)
        - add entry `n := SimpleIdent "Nat.sub"` to `funInstCache`
        - return `SimpleIdent "Nat.sub"`
  Assume that `n := Expr.const ``Nat.sub []`.
-/
def translateNatSub (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineNatSub
    updateFunInstCache n natSubSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "Int.ediv"` when entry `f := SimpleIdent "Int.ediv"` exists in `funInstCache`
     - Otherwise:
        - define Int.ediv Smt function (i.e., see `defineIntEDiv`)
        - add entry `f := SimpleIdent "Int.ediv"` to `funInstCache`
        - add entry `f' := SimpleIdent "Int.ediv"` to `funInstCache` with:
              - f' := Expr.const `Nat.div _  if `f := Expr.const ``Int.ediv _`
              - f' := Expr.const `Int.ediv _ otherwise
        - return `SimpleIdent "Int.ediv"`
  Assume that `f := Expr.const ``Int.ediv []` or `f := Expr.const ``Nat.div []`.
-/
def translateIntEDiv (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? f with
 | none =>
    defineIntEDiv
    let smtId ← updateFunInstCache f edivSymbol
    updateFunInstCacheBase (← toEDivAlias f) smtId
    return smtId
 | some smtId => return smtId

 where
   toEDivAlias (f : Expr) : TranslateEnvT Expr := do
     let Expr.const n _ := f | throwEnvError f!"toEDivAlias: name expression expected but got {reprStr f}"
     match n with
     | ``Int.ediv => mkNatDivOp
     | ``Nat.div => mkIntEDivOp
     | _ => throwEnvError f!"toEDivAlias: unexpected div operator {n}"


/-- Perform the following actions:
     - Return `SimpleIdent "Int.emod"` when entry `f := SimpleIdent "Int.emod"` exists in `funInstCache`
     - Otherwise:
        - define Int.emod Smt function (i.e., see `defineIntEMod`)
        - add entry `f := SimpleIdent "Int.emod"` to `funInstCache`
        - add entry `f' := SimpleIdent "Int.emod"` to `funInstCache` with:
              - f' := Expr.const `Nat.mod _  if `f := Expr.const ``Int.emod _`
              - f' := Expr.const `Int.emod _ otherwise
        - return `SimpleIdent "Int.emod"`
  Assume that `f := Expr.const ``Int.emod []` or f := `Expr.const ``Nat.mod []`
-/
def translateIntEMod (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? f with
 | none =>
    defineIntEMod
    let smtId ← updateFunInstCache f emodSymbol
    updateFunInstCacheBase (← toEModAlias f) smtId
    return smtId
 | some smtId => return smtId

 where
   toEModAlias (f : Expr) : TranslateEnvT Expr := do
     let Expr.const n _ := f | throwEnvError f!"toEModAlias: name expression expected but got {reprStr f}"
     match n with
     | ``Int.emod => mkNatModOp
     | ``Nat.mod => mkIntEModOp
     | _ => throwEnvError f!"toEModAlias: unexpected mod operator {n}"


/-- Perform the following actions:
     - Return `SimpleIdent "Int.div"` when entry `n := SimpleIdent "Int.div"` exists in `funInstCache`
     - Otherwise:
        - define Int.div Smt function (i.e., see `defineIntDiv`)
        - add entry `n := SimpleIdent "Int.div"` to `funInstCache`
        - return `SimpleIdent "Int.div"`
  Assume that `n := Expr.const ``Int.div []`.
-/
def translateIntDiv (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineIntDiv
    updateFunInstCache n tdivSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "Int.mod"` when entry `n := SimpleIdent "Int.mod"` exists in `funInstCache`
     - Otherwise:
        - define Int.mod Smt function (i.e., see `defineIntMod`)
        - add entry `n := SimpleIdent "Int.mod"` to `funInstCache`
        - return `SimpleIdent "Int.mod"`
  Assume that `n := Expr.const ``Int.mod []`.
-/
def translateIntMod (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineIntMod
    updateFunInstCache n tmodSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "Int.fdiv"` when entry `n := SimpleIdent "Int.fdiv"` exists in `funInstCache`
     - Otherwise:
        - define Int.fdiv Smt function (i.e., see `defineIntFDiv`)
        - add entry `n := SimpleIdent "Int.fdiv"` to `funInstCache`
        - return `SimpleIdent "Int.fdiv"`
  Assume that `n := Expr.const ``Int.fdiv []`.
-/
def translateIntFDiv (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineIntFDiv
    updateFunInstCache n fdivSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "Int.fmod"` when entry `n := SimpleIdent "Int.fmod"` exists in `funInstCache`
     - Otherwise:
        - define Int.fmod Smt function (i.e., see `defineIntFMod`)
        - add entry `n := SimpleIdent "Int.fmod"` to `funInstCache`
        - return `SimpleIdent "Int.fmod"`
  Assume that `n := Expr.const ``Int.fmod []`.
-/
def translateIntFMod (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineIntFMod
    updateFunInstCache n fmodSymbol
 | some smtId => return smtId


/-- Perform the following actions:
     - Return `SimpleIdent "Int.pow"` when entry `f := SimpleIdent "Int.pow"` exists in `funInstCache`
     - Otherwise:
        - define Nat sort (if necessary)
        - define Int.pow Smt function (i.e., see `defineIntPow`)
        - add entry `f := SimpleIdent "Int.pow"` to `funInstCache`
        - add entry `f' := SimpleIdent "Int.pow"` to `funInstCache` with:
              - f' := Expr.const `Nat.pow _  if `f := Expr.const ``Int.pow _`
              - f' := Expr.const `Int.pow _ otherwise
        - return `SimpleIdent "Int.pow"`
  Assume that `f := Expr.const ``Int.pow []` or f := `Expr.const ``Nat.pow []`
-/
def translateIntPow (f : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? f with
 | none =>
    discard $ translateNatType (← mkNatType)
    defineIntPow
    let smtId ← updateFunInstCache f intPowSymbol
    updateFunInstCacheBase (← toPowAlias f) smtId
    return smtId
 | some smtId => return smtId

 where
   toPowAlias (f : Expr) : TranslateEnvT Expr := do
     let Expr.const n _ := f | throwEnvError f!"toPowAlias: name expression expected but got {reprStr f}"
     match n with
     | ``Int.pow => mkNatPowOp
     | ``Nat.pow => mkIntPowOp
     | _ => throwEnvError f!"toPowAlias: unexpected mod operator {n}"


/-- Perform the following actions:
     - Return `SimpleIdent "Int.toNat"` when entry `n := SimpleIdent "Int.toNat"` exists in `funInstCache`
     - Otherwise:
        - define Int.toNat Smt function (i.e., see `defineInttoNat`)
        - add entry `n := SimpleIdent "Int.toNat"` to `funInstCache`
        - return `SimpleIdent "Int.toNat"`
  Assume that `n := Expr.const ``Int.toNat []`.
-/
def translateInttoNat (n : Expr) : TranslateEnvT SmtQualifiedIdent := do
 match (← get).smtEnv.funInstCache.find? n with
 | none =>
    defineInttoNat
    updateFunInstCache n toNatSymbol
 | some smtId => return smtId


/-- Return `stₙ` when entry `f := stₙ` exists in `funInstCache`.
    Otherwise:
     - add entry `f := SimpleIdent s` to `funInstCache`
     - return `SimpleIdent s`
-/
def getOpaqueSmtEquivFun (f : Expr) (s : SmtSymbol) : TranslateEnvT SmtQualifiedIdent := do
  match (← get).smtEnv.funInstCache.find? f with
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
        - Decidable.decide
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
  | ``ite
  | ``dite => getOpaqueSmtEquivFun f iteSymbol
  | ``Int.add
  | ``Nat.add => getOpaqueSmtEquivFun f addSymbol
  | ``Int.neg => getOpaqueSmtEquivFun f subSymbol
  | ``Int.mul
  | ``Nat.mul => getOpaqueSmtEquivFun f mulSymbol
  | ``Int.toNat => translateInttoNat f
  | ``Int.div => translateIntDiv f
  | ``Int.mod => translateIntMod f
  | ``Int.fdiv => translateIntFDiv f
  | ``Int.fmod => translateIntFMod f
  | ``Int.ediv
  | ``Nat.div => translateIntEDiv f
  | ``Int.emod
  | ``Nat.mod => translateIntEMod f
  | ``Int.pow
  | ``Nat.pow => translateIntPow f
  | ``LE.le
  | ``Nat.ble => getOpaqueSmtEquivFun f leqSymbol
  | ``LT.lt =>
        if Nat.blt args.size 2 then throwEnvError "translateOpaqueFun: at least two arguments expected for Lt.lt"
        if isStringType args[0]!
        then getOpaqueSmtEquivFun f strLtSymbol
        else getOpaqueSmtEquivFun f ltSymbol
  | ``Nat.sub => translateNatSub f
  | ``String.append => getOpaqueSmtEquivFun f strAppendSymbol
  | ``String.length => getOpaqueSmtEquivFun f strLengthSymbol
  | ``String.replace => getOpaqueSmtEquivFun f strReplaceAllSymbol
  | _ => throwEnvError f!"translateOpaqueFun: unexpected opaque operator {n}"


/-- Given a function application `f x₀ ... xₙ` and `s` the corresponding generated
    smt identifier for `f`, perform the following:
      - When `n = 0 ∨ ∀ i ∈ [0..n], ¬ isExplicit xᵢ` (i.e., instantiated polymorphic function passed as argument):
         - When isHOF:
             - return `.SmtIdent s`
         - Otherwise:
             - return `asArraySmt s`
      - When `∃ i ∈ [0..n], isExplicit xᵢ,`
         let A := [x₀,..., xₙ]
         let B := [termTranslator A[i] | i ∈ [0..n] ∧ isExplicit A[i]]
           - When isHOF:
              - return `selectSmt s B`
           - Otherwise;
              - return `mkSmtAppN s B`
    NOTE: It is assumed that all implicit arguments appear first in sequence `x₀ ... xₙ`.
-/
def createAppN
  (f : Expr) (s : SmtQualifiedIdent) (args : Array Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) (isHOF := false) : TranslateEnvT SmtTerm := do
  let mut genArgs := #[]
  let fInfo ← getFunInfoNArgs f args.size
  for i in [:fInfo.paramInfo.size] do
    if fInfo.paramInfo[i]!.isExplicit then
       genArgs := genArgs.push (← termTranslator args[i]!)
  if genArgs.size == 0
  then return genUnapplied s
  else return genApplied s genArgs

  where
    genUnapplied (id : SmtQualifiedIdent) : SmtTerm :=
      if isHOF then .SmtIdent id else asArraySmt id

    genApplied (id : SmtQualifiedIdent) (sargs : Array SmtTerm) : SmtTerm :=
      if isHOF then selectSmt id sargs else mkSmtAppN s sargs

/-- Given `t` corresponding the type of a function/lambda parameter:
     - return `translateType optimizer termTranslator t (optionsForFunLambdaParam (← isInRecFunDefinition))`
    An error is triggered if `t` corresponds to the type of an implicit argument.
-/
def translateFunLambdaParamType
  (t : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SortExpr := do
  translateType optimizer termTranslator t (optionsForFunLambdaParam (← isInRecFunDefinition))

/-- Given `f := Expr.const n _` corresponding to a function name and
    `params` its implicit arguments, perform the following actions:
      - When params.instanceArgs.size = 0:
          - instName := funNameToSmtSymbol n
          - add entry `f := SimpleIdent instName` to `funInstCache`
          - return `SimpleIdent instName`
      - When params.instanceArgs.size > 0:
          - instName := funNameToSmtSymbol (n ++ (← mkFreshId))
          - instApp ← getInstApp f params
          - add entry `instApp := SimpleIdent instName` to `funInstCache`
          - return `SimpleIdent instName`
     An error is triggered when `f` is not a named expression.
-/
def generateFunInst (f : Expr) (params : ImplicitParameters) : TranslateEnvT SmtQualifiedIdent := do
   let Expr.const n _ := f | throwEnvError f!"generateFunInst: name expression expected but got {reprStr f}"
   -- get instance application
   if params.instanceArgs.isEmpty
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
  (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  -- get instance application
  let params ← getImplicitParameters f args
  let instApp ← getInstApp f params
  match (← get).smtEnv.funInstCache.find? instApp with
  | none =>
      let Expr.const n l := f
        | throwEnvError f!"translateRecFun: name expression expected but got {reprStr f}"
      let ConstantInfo.defnInfo dInfo ← getConstInfo n
        | throwEnvError f!"translateRecFun: no defnInfo for {n}"
      generateRecFunDefinitions dInfo.all l params
      let some smtId := (← get).smtEnv.funInstCache.find? instApp
        | throwEnvError f!"translateRecFun: instance function name expected for {reprStr instApp}"
      createAppN f smtId args termTranslator
  | some smtId => createAppN f smtId args termTranslator

  where
    updateFunDefinitions
      (f : Expr) (id : SmtQualifiedIdent) (fbody : Expr)
      (rt : Expr) (defs : FunctionDefinitions) : TranslateEnvT FunctionDefinitions := do
      let .SimpleIdent s := id
        | throwEnvError f!"updateFunDefinition: SimpleIdent expected but got {id}"
      let ret ← translateFunLambdaParamType rt optimizer termTranslator
      let fInfo ← getFunInfo f
      lambdaTelescope fbody fun xs b => do
        let mut params := (#[] : SortedVars)
        for i in [:xs.size] do
          let Expr.fvar v := xs[i]!
            | throwEnvError f!"updateFunDefinition: FVarExpr expected but got {reprStr xs[i]!}"
          updateQuantifiedFVarsCache v false
          if fInfo.paramInfo[i]!.isExplicit then
            let st ← translateFunLambdaParamType (← v.getType) optimizer termTranslator
            params := params.push (← fvarIdToSmtSymbol v, st)
        let funDecl := {name := s, params, ret}
        let sBody ← termTranslator b
        return { defs with funDecls := defs.funDecls.push funDecl, funBodies := defs.funBodies.push sBody }

    replaceGenericRecFun (f : Name) (us : List Level) (e : Expr) : Option Expr :=
      match e with
      | Expr.const n _ =>
          if n == internalRecFun
          then some (mkConst f us)
          else none
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
        finfos := finfos.push (f, auxApp, smtId)
      for i in [:finfos.size] do
        let f := finfos[i]!.1
        let auxApp := finfos[i]!.2.1
        let smtId := finfos[i]!.2.2
        let instApp ← getInstApp auxApp params
        let some fbody := env.optEnv.recFunInstCache.find? instApp
          | throwEnvError f!"translateRecFun: function body expected for {reprStr instApp}"
        let ConstantInfo.defnInfo dInfo ← getConstInfo f
          | throwEnvError f!"translateRecFun: no defnInfo for {f}"
        let fbody' := fbody.replace (replaceGenericRecFun f us)
        -- return type
        let ret := Expr.getForallBody dInfo.type
        funDefs ← withTranslateRecBody $ updateFunDefinitions auxApp smtId fbody' ret funDefs
      defineFunctions funDefs

/-- Return `true` only when `n` corresponds to a function/constructor name
    expected to be eliminated during optimization phase.
-/
def isForbiddenConst (n : Name) : Bool :=
  match n with
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

/-- Given `e := Expr.const n l`,
     - when `n := false`
        - return `BoolTerm false`
     - when `n := False`
        - return `BoolTerm false`
     - when `n := true`
        - return `BoolTerm true`
     - when `n := True`
         - return `BoolTerm true`
     - when `n := Int.ofNat`
         - return `termTranslator (← etaExpand e)`
     - when `isInductiveTypeExpr e`
         - return ⊥
     - when `isForbiddenUnappliedConst n`
         - return ⊥
     - when `isMatchExpr n`
         - return ⊥
     - when `n` is a constructor with implicit arguments
         - return ⊥
     - when `n` is a nullary constructor
        - return `SmtIdent (.QualifiedIdent n (translateType optimizer termTranslator Type(n)))`
     - When `n` is a parameterized constructor
        - return `termTranslator (← etaExpand e)`
     - when `hasImplicitArgs e`
         - return ⊥
     - when `n` ∈ opaqueFuns ∧ hasSmtDefinedOperator n
        - return `asArraySmt (← translateOpaqueFun n e)`
     - when `n ∈ opaqueFuns ∧ ¬ hasSmtDefinedOperator n
        - return `termTranslator (← etaExpand e)`
     - when `n ∉ opaqueFuns ∧ isRecursiveFun n`
         - return `translateRecFun e #[] optimizer termTranslator`
     - when n ∉ opaqueFuns ∧ ¬ isRecursiveFun n` (i.e., an undefined class function
       has at least one implicit argument)
         - return ⊥
    An error is triggered when `e` is not a name expression.

    NOTE: This function cannot be called on fun name expression
    (i.e., f x₁ ... xₙ, where `e := f` and `f` is a partially or totally applied function).
    It can only be applied on functions passed as arguments.
-/
def translateConst
  (e : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  let Expr.const n _ := e | throwEnvError f!"translateConst: name expression expected but got {reprStr e}"
  match n with
  | ``false
  | ``False => return falseSmt
  | ``true
  | ``True => return trueSmt
  | ``Int.ofNat => return (← termTranslator (← etaExpand e))
  | _ =>
    if (← isInductiveTypeExpr e) then
      throwEnvError f!"translateConst: unexpected inductive datatype {reprStr e}"
    if isForbiddenUnappliedConst n then
      throwEnvError f!"translateConst: unexpected name expression {reprStr e}"
    if (← isMatchExpr n) then
      throwEnvError f!"translateConst: unexpected match function passed as argument {n}"
    if let some r ← translateCtor n then return r
    if (← hasImplicitArgs e) then
      throwEnvError f!"translateConst: unexpected implicit arguments for function {reprStr e}"
    if let some r ← translateOpaque n then return r
    if (← isRecursiveFun n)
    then translateRecFun e #[] optimizer termTranslator
    else throwEnvError f!"translateConst: only opaque and recursive functions expected but got {reprStr e}"


  where
    translateCtor (c : Name) : TranslateEnvT (Option SmtTerm) := do
      let ConstantInfo.ctorInfo info ← getConstInfo c | return none
      if info.numParams != 0 then
        throwEnvError f!"translateConst: unexpected implicit arguments for ctor {c}"
      if info.numFields == 0 then
        -- nullary constructor case
        let st ← translateType optimizer termTranslator info.type
        return (smtQualifiedVarId (nameToSmtSymbol c) st)
      else termTranslator (← etaExpand e) -- parameterized constructor case

    translateOpaque (n : Name) : TranslateEnvT (Option SmtTerm) := do
      if !(opaqueFuns.contains n) then return none
      let smtSym ← translateOpaqueFun e n #[]
      if (hasSmtDefinedOperator n)
      then return (asArraySmt smtSym)
      else return (← termTranslator (← etaExpand e))

    isForbiddenUnappliedConst (n : Name) : Bool :=
      match n with
      | ``Exists
      | ``Decidable.decide
      | ``ite
      | ``dite => true
      | _ => isForbiddenConst n

/-- Translate Application
    TODO: UPDATE
    - Need to handle match expression

--  -- handle match expression and generate ite

-/
def translateApp
  (e : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
  if isForbiddenConstExpr e then throwEnvError f!"unexpected name expression {reprStr e}"
  Expr.withApp e fun f args => do
    match f with
    | Expr.const n _ =>
         if let some r ← translateFullyApplied? f n args then return r
         if let some r ← translateEq? f n args then return r
         if let some r ← translateRelational? f n args then return r
         if let some r ← translateDITE? f n args then return r
         if let some r ← translateOfNat? n args then return r
         if let some r ← translateDecide? n args then return r
         if let some r ← translateMatch? f n args then return r
         if let some r ← translateExists? n args then return r
         if let some r ← translateRecFun? f n args then return r
         if let some r ← translateAppliedCtor? f n args then return r
         if let some r ← translateUndeclaredFun? f n args then return r
         throwEnvError f!"translateApp: unexpected application {reprStr e}"

    | Expr.fvar _ => -- case for HOF
         let .SmtIdent smtId ← translateFreeVar f optimizer termTranslator
           | throwEnvError f!"translateApp: SmtIdent expected for {reprStr f}"
         createAppN f smtId args termTranslator (isHOF := true)

    | _ => throwEnvError f!"translateApp: unexpected application {reprStr e}"

  where
    translateEq? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Eq =>
         if args.size == 2 then
           throwEnvError f!"translateEq?: unexpected partially applied Eq got {reprStr args}"
         if args.size == 1 then return (← termTranslator (← etaExpand e))
         match args[1]! with
          | Expr.const ``true _ => termTranslator args[2]!
          | Expr.const ``false _ => termTranslator (mkApp (← mkBoolNotOp) args[2]!)
          | _ => createAppN f (← translateOpaqueFun f n args) args termTranslator
       | _ => return none

    translateDITE? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``dite =>
            if args.size != 5 then
               throwEnvError f!"translateDITE?: unexpected partially applied dite got {reprStr args}"
            let args := args.set! 3 (← Solver.Optimize.extractDependentITEExpr args[3]!)
            let args := args.set! 4 (← Solver.Optimize.extractDependentITEExpr args[4]!)
            createAppN f (← translateOpaqueFun f n args) args termTranslator
       | _ => return none

    translateOfNat? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Int.ofNat =>
            if args.size != 1 then
               throwEnvError f!"translateOfNat?: exaclty one argument expected"
            termTranslator args[0]!
       | _ => return none

    translateDecide? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``Decidable.decide =>
            if args.size != 2 then
               throwEnvError f!"translateDecide?: unexpected partially applied {n} got {reprStr args}"
            termTranslator args[0]!
       | _ => return none

    translateRelational? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
       | ``BEq.beq
       | ``LE.le
       | ``LT.lt =>
            if (← isOpaqueRelational n args) then
              if args.size == 3 then
                throwEnvError f!"translateRelational?: unexpected partially applied {n} got {reprStr args}"
              if args.size == 2 then return (← termTranslator (← etaExpand e))
              createAppN f (← translateOpaqueFun f n args) args termTranslator
            else return none -- undefined fun class case
       | _ => return none

    translateMatch? (_f : Expr) (n : Name) (_args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if !(← isMatchExpr n) then return none
      throwEnvError "translateMatch?: not yet implemented !!!"

    genExistsTerm (lambdaE : Expr) : QuantifierEnvT SmtTerm := do
      lambdaTelescope lambdaE fun xs b => do
        for i in [:xs.size] do
          let t ← inferType xs[i]!
          translateQuantifier xs[i]! t optimizer termTranslator
        let ebody ← termTranslator b
        let env ← get
        if env.premises.size != 1 then
          throwEnvError f!"genExistsTerm: only one predicate qualifier premise expected but got {env.premises}"
        -- set patterns to none for now
        -- TODO: We need to check if e-pattern is necessary for existential
        return (mkExistsTerm none env.quantifiers (andSmt env.premises[0]! ebody) none)

    translateExists? (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      match n with
      | ``Exists =>
          if args.size != 2 then
            throwEnvError f!"translateExists?: exactly two arguments expected but got {reprStr args}"
          let (t, _) ← genExistsTerm args[1]! |>.run (initialQuantifierEnv false)
          return t
      | _ => return none

    translateRecFun? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isOpaqueFun n args) then return none
      if !(← isRecursiveFun n) then return none
      translateRecFun f args optimizer termTranslator

    translateAppliedCtor? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      let ConstantInfo.ctorInfo info ← getConstInfo n | return none
      let st ← translateType optimizer termTranslator info.type
      createAppN f (.QualifiedIdent (nameToSmtSymbol n) st) args termTranslator

    translateUndeclaredFun? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if (← isOpaqueFun n args) then return none
      let some fbody ← getFunBody f | return none
      if !(← isUndefinedClassFunApp (Expr.beta fbody args)) then return none
      -- get instance application
      let params ← getImplicitParameters f args
      let instApp ← getInstApp f params
      match (← get).smtEnv.funInstCache.find? instApp with
      | none =>
         let smtId ← generateFunInst f params
         let .SimpleIdent s := smtId
           | throwEnvError f!"translateUndeclaredFun?: SimpleIdent expected but got {smtId}"
         let ConstantInfo.defnInfo dInfo ← getConstInfo n
           | throwEnvError f!"translateUndeclaredFun?: no defnInfo for {n}"
         let fInfo ← getFunInfo e
         withTranslateRecBody $ forallTelescope dInfo.type fun xs b => do
            let mut pargs := (#[] : Array SortExpr)
            for i in [:xs.size] do
              let Expr.fvar v := xs[i]!
                | throwEnvError f!"translateUndeclaredFun? FVarExpr expected but got {reprStr xs[i]!}"
              updateQuantifiedFVarsCache v false
              if fInfo.paramInfo[i]!.isExplicit then
                 let st ← translateFunLambdaParamType (← v.getType) optimizer termTranslator
                 pargs := pargs.push st
            let ret ← translateFunLambdaParamType b optimizer termTranslator
            declareFun s pargs ret
            createAppN f smtId args termTranslator
      | some smtId => createAppN f smtId args termTranslator

    translateFullyApplied? (f : Expr) (n : Name) (args : Array Expr) : TranslateEnvT (Option SmtTerm) := do
      if !(fullyAppliedConst.contains n) then return none
      let fInfo ← getFunInfo f
      if fInfo.paramInfo.size != args.size then
        throwEnvError f!"translateFullyApplied?: fully applied function expected for {reprStr f}"
      createAppN f (← translateOpaqueFun f n args) args termTranslator

/-- Given `e := λ (x₀ : t₁) → λ (xₙ : tₙ) => b`, create Smt term `(lambda (B) sb)`, where:
      - A := [x₁, ..., xₙ]
      - B := [(A[i], translateFunLambdaParamType tᵢ optimizer termTranslator) | i ∈ [0..n] ∧ isExplicit A[i]]
      - sb := termTranslator b
-/
def translateLambda
  (e : Expr) (optimizer : Expr → TranslateEnvT Expr)
  (termTranslator : Expr → TranslateEnvT SmtTerm) : TranslateEnvT SmtTerm := do
 let fInfo ← getFunInfo e
 lambdaTelescope e fun xs b => do
   let mut svars := (#[] : SortedVars)
   for i in [:xs.size] do
     let Expr.fvar v := xs[i]!
       | throwEnvError f!"translateLambda: FVarExpr expected but got {reprStr xs[i]!}"
     updateQuantifiedFVarsCache v false
     if fInfo.paramInfo[i]!.isExplicit then
       let st ← translateFunLambdaParamType (← v.getType) optimizer termTranslator
       svars := svars.push (← fvarIdToSmtSymbol v, st)
   return mkLambdaTerm svars (← termTranslator b)


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
  let ConstantInfo.inductInfo indVal ← getConstInfo n
    | throwEnvError "translateProj: induction info expected for {n}"
  match indVal.ctors with
  | [c] =>
      let selectorSym := mkNormalSymbol s!"{c}.{idx+1}"
      return (mkSimpleSmtAppN selectorSym #[← termTranslator p])
  | _ => throwEnvError "translateProj: only one ctor expected for structure for {n}"

end Solver.Smt
