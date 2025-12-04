import Lean
import Blaster.Optimize.Env.Types

open Lean Meta Blaster.Data.HashSet

namespace Blaster.Optimize

/-- Return `a'` if `a` is already in hash cons cache.
    Otherwise, the following actions are performed:
      - add `a` to hash cons cache
      - return `a`
-/
@[always_inline, inline]
def mkExpr (e : Expr) : TranslateEnvT Expr := do
  let cached := (← get).optEnv.hashConsCache.getD e instCacheMiss
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    updateHashConsCache e
    return e


/-- Internal generalized rec fun const expression to be used for in normalized recursive
    definition kept in `recFunMap`.
-/
def internalRecFunExpr : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.internalRecFun

/-- Tag expression as recursive call. This metadata is used when
    replacing a recursive call function with `internalRecfun`.
-/
@[always_inline, inline]
def tagAsRecursiveCall (e : Expr) : TranslateEnvT Expr :=
 mkExpr (mkAnnotation `_solver.recursivecall e)

/-- Return `some b` if `e := mkAnnotation `_solver.recursivecall b'`. -/
def toTaggedRecursiveCall? (e : Expr) : Option Expr :=
 match e with
 | Expr.mdata d b =>
      if d.size == 1 && d.getBool `_solver.recursivecall false
      then some b else none
 | _ => none

/-- Return `true` if `e := mkAnnotation `_solver.recursivecall b'`. -/
def isTaggedRecursiveCall (e : Expr) : Bool :=
 match e with
 | Expr.mdata d _ => d.size == 1 && d.getBool `_solver.recursivecall
 | _ => false


/-- Return cached `Bool` type. -/
def mkBoolType : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolType

/-- Return cached `true` boolean constructort. -/
def mkBoolTrue : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolTrue

/-- Return cached `false` boolean constructor. -/
def mkBoolFalse : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolFalse

/-- Given `b` a boolean value return the corresponding
    boolean constructor expression and cache result.
-/
def mkBoolLit (b : Bool) : TranslateEnvT Expr :=
  if b then mkBoolTrue else mkBoolFalse

/-- Return `not` boolean operator and cache result. -/
def mkBoolNotOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolNot

/-- Return `or` boolean operator and cache result. -/
def mkBoolOrOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolOr

/-- Return `and` boolean operator and cache result. -/
def mkBoolAndOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.boolAnd

/-- Return `Prop` type and cache result. -/
def mkPropType : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propType

/-- Return `True` Prop and cache result. -/
def mkPropTrue : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propTrue

/-- Return `False` Prop and cache result. -/
def mkPropFalse : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propFalse

/-- Given `b` a boolean value return the corresponding
    propositional expression and cache result.
-/
def mkPropLit (b : Bool) : TranslateEnvT Expr :=
  if b then mkPropTrue else mkPropFalse

/-- Return `Not` operator and cache result. -/
def mkPropNotOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propNot

/-- Return `Or` operator and cache result. -/
def mkPropOrOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propOr

/-- Return `And` operator and cache result. -/
def mkPropAndOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.propAnd


/-- Return `BEq.beq` operator and cache result. -/
def mkBeqOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.beq

/-- Return `Eq` operator and cache result. -/
def mkEqOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.eq

/-- Return `Blaster.dite'` operator and cache result. -/
def mkBlasterDIteOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.blasterDite


/-- Return `LE.le` operator and cache result. -/
def mkLeOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.le

/-- Return `LT` const expression and cache result. -/
def mkLTConst : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.ltCstr


/-- Return `LT.lt` operator and cache result. -/
def mkLtOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.lt

/-- Return `Decidable` const expression and cache result. -/
def mkDecidableConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable)

/-- Return `Decidable` const expression and cache result. -/
def mkDecidableEqConst : TranslateEnvT Expr := mkExpr (mkConst ``DecidableEq)

/-- Return `Blaster.decide'` const expression and cache result. -/
def mkBlasterDecideConst : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.blasterDecide

/-- Return `Inhabited` const expression and cache result. -/
def mkInhabitedConst : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.inhabited

/-- Return `LawfulBEq` const expression and cache result. -/
def mkLawfulBEqConst : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.lawfulBEq

/-- Return `True.intro` const expression and cache result. -/
def mkTrueIntro : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.trueIntro

/-- Return `not_false` const expression and cache result. -/
def mkNotFalse : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.notFalse

/-- Return `Decidable.decide` const expression and cache result. -/
def mkDecide : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.decide

/-- Return `of_decide_eq_true` const expression and cache result. -/
def mkOfDecideEqTrue : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.ofDecideEqTrue

/-- Return `of_decide_eq_false` const expression and cache result. -/
def mkOfDecideEqFalse : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.ofDecideEqFalse

/-- Return `Eq.refl` const expression and cache result. -/
def mkEqRefl (u : List Level) : TranslateEnvT Expr := mkExpr (mkConst ``Eq.refl u)

/-- Return `rfl` const expression and cache result. -/
def mkRfl (u : List Level) : TranslateEnvT Expr := mkExpr (mkConst ``rfl u)

/-- Return `Nat` Type and cache result. -/
def mkNatType : TranslateEnvT Expr :=
    return (← get).optEnv.memCache.commonExpr.natType

/-- Create a `Nat.add` operator expression and cache result. -/
def mkNatAddOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natAdd

/-- Create a `Nat.sub` operator expression and cache result. -/
def mkNatSubOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natSub

/-- Create a `Nat.mul` operator expression and cache result. -/
def mkNatMulOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natMul

/-- Creata a `Nat.div` operator expression and cache result. -/
def mkNatDivOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natDiv

/-- Create a `Nat.mod` operator expression and cache result. -/
def mkNatModOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natMod

/-- Create a `Nat.pow` operator expression and cache result. -/
def mkNatPowOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natPow

/-- Return cached `Nat.beq` operator -/
def natBeq : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natBeq

/-- Return cached `Nat.ble` operator -/
def natBle : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.natBle

/-- Return `Nat.blt` operator and cache result. -/
def mkNatBltOp : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.natBlt

/-- Return `Int` Type and cache result. -/
def mkIntType : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.intType

/-- Return `Int.add` operator and cache result. -/
def mkIntAddOp : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.intAdd

/-- Return `Int.mul` operator and cache result. -/
def mkIntMulOp : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.intMul


/-- Create an `Int.pow` operator expression and cache result. -/
def mkIntPowOp : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.intPow


/-- Create an `Int.ediv` operator expression and cache result. -/
def mkIntEDivOp : TranslateEnvT Expr :=
 return (← get).optEnv.memCache.commonExpr.intEDiv

/-- Create an `Int.emod` operator expression and cache result. -/
def mkIntEModOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intEMod

/-- Return `Int.fdiv` operator and cache result. -/
def mkIntFDivOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intFDiv

/-- Return `Int.fmod` operator and cache result. -/
def mkIntFModOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intFMod

/-- Return `Int.tdiv` operator and cache result. -/
def mkIntTDivOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intTDiv

/-- Return `Int.tmod` operator and cache result. -/
def mkIntTModOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intTMod

/-- Return `Int.neg` operator and cache result. -/
def mkIntNegOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intNeg

/-- Return `Int.ofNat` constructor and cache result. -/
def mkIntOfNat : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intOfNat

/-- Return `Int.negSucc` constructor and cache result. -/
def mkIntNegSucc : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intNegSucc

/-- Return `Int.toNat` operator and cache result. -/
def mkIntToNatOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intToNat

/-- Return "==" Nat operator and cache result. -/
def mkNatBEqOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natBEqInst

/-- Return the `<` Nat operator and cache result. -/
def mkNatLtOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.natLt

/-- Return the `<` Int operator and cache result. -/
def mkIntLtOp : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.intLt

/-- Return the `List.get?Internal` operator and cache result. -/
def mkListGetInternal : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.listGetInternal

/-- Return the `List.reverseAux` operator and cache result. -/
def mkListReverseAux : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.listReverseAux

/-- Return the `List.take` operator and cache result. -/
def mkListTake : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.listTake

/-- Return the `List.drop` operator and cache result. -/
def mkListDrop : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.listDrop

/-- Return the `List.length` operator and cache result. -/
def mkListLength : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.listLength


def assertShared (e : Expr) : TranslateEnvT Bool := do
  match (← get).optEnv.hashConsCache.get? e with
  | some r => return exprEq r.expr e
  | none => return false

/-- `mkAppExpr f a constructs the application `f a` and cache the result.
    The cache is probed from the components, so no node is allocated on a hit. -/
def mkAppExpr (f : Expr) (a : Expr) : TranslateEnvT Expr := do
  let cached := findSharedApp? (← get).optEnv.hashConsCache f a
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let e := Expr.app f a
    updateHashConsCache e
    return e

/-- `mkApp2Expr f a₁ a₂ constructs the application `f a₁ a₂` and cache the result. -/
def mkApp2Expr (f : Expr) (a1 a2 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkAppExpr f a1) a2

/-- `mkApp3Expr f a₁ a₂ a₃ constructs the application `f a₁ a₂ a₃` and cache the result. -/
def mkApp3Expr (f : Expr) (a1 a2 a3 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp2Expr f a1 a2) a3

/-- `mkApp4Expr f a₁ a₂ a₃ a₄ constructs the application `f a₁ a₂ a₃ a₄` and cache the result. -/
def mkApp4Expr (f : Expr) (a1 a2 a3 a4 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp3Expr f a1 a2 a3) a4

/-- `mkApp5Expr f a₁ a₂ a₃ a₄ a₅ constructs the application `f a₁ a₂ a₃ a₄ a₅` and cache the result. -/
def mkApp5Expr (f : Expr) (a1 a2 a3 a4 a5 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp4Expr f a1 a2 a3 a4) a5

/-- `mkApp6Expr f a₁ a₂ a₃ a₄ a₅ a₆ constructs the application `f a₁ a₂ a₃ a₄ a₅ a₆` and cache the result. -/
def mkApp6Expr (f : Expr) (a1 a2 a3 a4 a5 a6 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp5Expr f a1 a2 a3 a4 a5) a6

/-- `mkApp7Expr f a₁ a₂ a₃ a₄ a₅ a₆ a₇ constructs the application `f a₁ a₂ a₃ a₄ a₅ a₆ a₇` and cache the result. -/
def mkApp7Expr (f : Expr) (a1 a2 a3 a4 a5 a6 a7 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp6Expr f a1 a2 a3 a4 a5 a6) a7

/-- `mkApp8Expr f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ constructs the application `f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈` and cache the result. -/
def mkApp8Expr (f : Expr) (a1 a2 a3 a4 a5 a6 a7 a8 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp7Expr f a1 a2 a3 a4 a5 a6 a7) a8

/-- `mkApp9Expr f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ constructs the application `f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉` and cache the result. -/
def mkApp9Expr (f : Expr) (a1 a2 a3 a4 a5 a6 a7 a8 a9 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp8Expr f a1 a2 a3 a4 a5 a6 a7 a8) a9

/-- `mkApp10Expr f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ constructs the
    application `f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀` and cache the result.
-/
def mkApp10Expr (f : Expr) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkApp9Expr f a1 a2 a3 a4 a5 a6 a7 a8 a9) a10


/-- `mkAppRangeExpr f i j #[a₀, ..., aᵢ, ..., aⱼ, ...]` ==> `f aᵢ ... aⱼ₋₁` with max sharing. -/
@[always_inline, inline]
def mkAppRangeExpr (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : TranslateEnvT Expr :=
  go beginIdx endIdx f
where
  go (i : Nat) (stop : Nat) (b : Expr) : TranslateEnvT Expr := do
    if i ≥ stop then return b
    else go (i + 1) stop (← mkAppExpr b args[i]!)


/-- `mkAppNExpr f #[a₀, ..., aₙ]` constructs `f a₀ ... aₙ` with maximum sharing. -/
@[always_inline, inline]
def mkAppNExpr (f : Expr) (args : Array Expr) : TranslateEnvT Expr :=
  mkAppRangeExpr f 0 args.size args

@[always_inline, inline]
def mkSortExpr (u : Level) : TranslateEnvT Expr :=
  mkExpr (.sort u)

@[always_inline, inline]
def mkBVarExpr (idx : Nat) : TranslateEnvT Expr :=
  mkExpr (.bvar idx)

@[always_inline, inline]
def mkMDataExpr (d : MData) (e : Expr) : TranslateEnvT Expr := do
  let cached := findSharedMData? (← get).optEnv.hashConsCache d e
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let r := Expr.mdata d e
    updateHashConsCache r
    return r

@[always_inline, inline]
def mkProjExpr (n : Name) (i : Nat) (s : Expr) : TranslateEnvT Expr := do
  let cached := findSharedProj? (← get).optEnv.hashConsCache n i s
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let r := Expr.proj n i s
    updateHashConsCache r
    return r

@[always_inline, inline]
def mkLambdaExpr (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : TranslateEnvT Expr := do
  let cached := findSharedLambda? (← get).optEnv.hashConsCache t b
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let r := Expr.lam x t b bi
    updateHashConsCache r
    return r

@[always_inline, inline]
def mkForallExpr (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : TranslateEnvT Expr := do
  let cached := findSharedForall? (← get).optEnv.hashConsCache t b
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let r := Expr.forallE x t b bi
    updateHashConsCache r
    return r

@[always_inline, inline]
def mkLetExpr (x : Name) (t : Expr) (v : Expr) (b : Expr) (nondep : Bool := false) : TranslateEnvT Expr := do
  let cached := findSharedLet? (← get).optEnv.hashConsCache v b
  if !exprEq cached.expr instCacheMiss then return cached.expr
  else
    let r := Expr.letE x t v b nondep
    updateHashConsCache r
    return r

@[always_inline, inline]
def _root_.Lean.Expr.updateAppExpr! (e : Expr) (newFn : Expr) (newArg : Expr) : TranslateEnvT Expr := do
  let .app fn arg := e | panic! "application expected"
  if exprEq fn newFn && exprEq arg newArg then return e else mkAppExpr newFn newArg

@[always_inline, inline]
def _root_.Lean.Expr.updateMDataExpr! (e : Expr) (newExpr : Expr) : TranslateEnvT Expr := do
  let .mdata d a := e | panic! "mdata expected"
  if exprEq a newExpr then return e else mkMDataExpr d newExpr

@[always_inline, inline]
def _root_.Lean.Expr.updateProjExpr! (e : Expr) (newExpr : Expr) : TranslateEnvT Expr := do
  let .proj s i a := e | panic! "proj expected"
  if exprEq a newExpr then return e else mkProjExpr s i newExpr

@[always_inline, inline]
def _root_.Lean.Expr.updateForallExpr! (e : Expr) (newDomain : Expr) (newBody : Expr) : TranslateEnvT Expr := do
  let .forallE n d b bi := e | panic! "forall expected"
  if exprEq d newDomain && exprEq b newBody
  then return e
  else mkForallExpr n bi newDomain newBody

@[always_inline, inline]
def _root_.Lean.Expr.updateLambdaExpr! (e : Expr) (newDomain : Expr) (newBody : Expr) : TranslateEnvT Expr := do
  let .lam n d b bi := e | panic! "lambda expected"
  if exprEq d newDomain && exprEq b newBody
  then return e
  else mkLambdaExpr n bi newDomain newBody

@[always_inline, inline]
def _root_.Lean.Expr.updateLetExpr! (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) : TranslateEnvT Expr := do
  let .letE n t v b nondep := e | panic! "let expression expected"
  if exprEq t newType && exprEq v newVal && exprEq b newBody
  then return e
  else mkLetExpr n newType newVal newBody nondep

/--
`mkAppRangeExprWithSetAt f i j d #[a₀, ..., aₙ] k e` ==> `f aᵢ aₖ₋₁ e aₖ₊₁ ... aⱼ₋₁`.
-/
@[always_inline, inline]
def mkAppRangeExprWithSetAt (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) (idx : Nat) (e : Expr) : TranslateEnvT Expr :=
  go beginIdx endIdx f
where
  go (i : Nat) (stop : Nat) (b : Expr) : TranslateEnvT Expr := do
    if i ≥ stop then return b
    else if i == idx then go (i + 1) stop (← mkAppExpr b e)
    else go (i + 1) stop (← mkAppExpr b args[i]!)

/--
`mkAppNExprWithSetAt f #[a₀, ..., aₙ] k e` constructs the application `f a₀ a₁ aₖ₋₁ e aₖ₊₁ ... aₙ`.
-/
@[always_inline, inline]
def mkAppNExprWithSetAt (f : Expr) (args : Array Expr) (idx : Nat) (e : Expr) : TranslateEnvT Expr :=
  mkAppRangeExprWithSetAt f 0 args.size args idx e


/-- `mkNatLitExpr n` constructs `Expr.lit (Literal.natVal n)` and cache result. -/
def mkNatLitExpr (n : Nat) : TranslateEnvT Expr :=
  mkExpr (mkRawNatLit n)

/-- Return Nat `a = b`. -/
def mkNatEqExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkApp3Expr (← mkEqOp) (← mkNatType) a b

/-- Return Nat `a < b`. -/
def mkNatLtExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkApp2Expr (← mkNatLtOp) a b

/-- `evalBinNatOp f n1 n2 perform the following:
      -  let r := f n1 n2
      - construct nat literal for `r`
      - cache result and return r
-/
def evalBinNatOp (f: Nat -> Nat -> Nat) (n1 n2 : Nat) : TranslateEnvT Expr :=
  mkNatLitExpr (f n1 n2)

/-- `mkIntLitExpr n` constructs and cache an Int literal expression, i.e.,
     either `Int.ofNat (Expr.lit (Literal.natVal n)` or `Int.negSucc (Expr.lit (Literal.natVal n)`.
-/
def mkIntLitExpr (n : Int) : TranslateEnvT Expr := do
  match n with
  | Int.ofNat n => mkAppExpr (← mkIntOfNat) (← mkNatLitExpr n)
  | Int.negSucc n => mkAppExpr (← mkIntNegSucc) (← mkNatLitExpr n)

/-- Return Int `a = b`. -/
def mkIntEqExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkApp3Expr (← mkEqOp) (← mkIntType) a b

/-- Returns Int `a < b`. -/
def mkIntLtExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkApp2Expr (← mkIntLtOp) a b

/-- `mkNatNegExpr n` constructs and cache the negation of a Nat literal expression, i.e.,
     Int.negSucc (Expr.lit (Literal.natVal (n - 1))`.
-/
def mkNatNegExpr (n : Nat) : TranslateEnvT Expr := do
  mkAppExpr (← mkIntNegSucc) (← mkNatLitExpr (n - 1))

/- Given `e` of type `Bool`, return `b = e`.  -/
def mkEqBool (e : Expr) (b : Bool) : TranslateEnvT Expr := do
  mkApp3Expr (← mkEqOp) (← mkBoolType) (← mkBoolLit b) e

/-- `evalBinIntOp f n1 n2 perform the following:
      - let r := f n1 n2
      - construct int literal for `r`
      - cache result and return r
-/
@[always_inline, inline]
def evalBinIntOp (f: Int -> Int -> Int) (n1 n2 : Int) : TranslateEnvT Expr :=
  mkIntLitExpr (f n1 n2)

/-- `mkStrLitExpr s` constructs `Expr.lit (Literal.strVal s)` and cache result. -/
def mkStrLitExpr (s : String) : TranslateEnvT Expr :=
  mkExpr (mkStrLit s)

/-- `mkDecidableConstraint e` constructs constraint [Decidable e] and cache the result. -/
def mkDecidableConstraint (e : Expr) : TranslateEnvT Expr := do
  mkAppExpr (← mkDecidableConst) e

/-- Return cached `String.mk` const expression. -/
def mkStringMk : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.stringMk

/-- Return cached `String` type. -/
def mkStringType : TranslateEnvT Expr :=
  return (← get).optEnv.memCache.commonExpr.stringType

/-- Return `Char.ofNat` const expression and cache result. -/
def mkCharOfNat : TranslateEnvT Expr := mkExpr (mkConst ``Char.ofNat)

/-- Construct a Char expression from `c` and cache result. -/
def mkCharExpr (c : Char) : TranslateEnvT Expr := do
  mkAppExpr (← mkCharOfNat) (← mkNatLitExpr c.toNat)

/-- Return `Char` type expression and cache result. -/
def mkCharType : TranslateEnvT Expr := mkExpr (mkConst ``Char)

/-- Given `xs` a list of expression and `t` the list sort, generate the corresponding list expression. -/
@[always_inline, inline]
def listToExpr (xs : List Expr) (u : List Level) (t : Expr) : TranslateEnvT Expr := do
 let consExpr ← mkAppExpr (← mkExpr (mkConst ``List.cons u)) t
 let nilExpr ← mkAppExpr (← mkExpr (mkConst ``List.nil u)) t
 let rec go (xs : List Expr) : TranslateEnvT Expr := do
   match xs with
   | [] => return nilExpr
   | x :: xs' => mkApp2Expr consExpr x (← go xs')
 go xs

/-- Convert a string to a list of char expression. -/
def stringToCtor (s : String) : TranslateEnvT Expr := do
  let consExpr ← mkAppExpr (← mkExpr (mkConst ``List.cons [levelZero])) (← mkCharType)
  let nilExpr ← mkAppExpr (← mkExpr (mkConst ``List.nil [levelZero])) (← mkCharType)
  let rec go (xs : List Char) : TranslateEnvT Expr := do
    match xs with
    | [] => return nilExpr
    | x :: xs' => mkApp2Expr consExpr (← mkCharExpr x) (← go xs')
  mkAppExpr (← mkStringMk) (← go s.toList)


/-- Given `m` an Option value and `t` the option sort return an Option expression. -/
def mkOptionExpr (t : Expr) (u : List Level) (m : Option Expr) : TranslateEnvT Expr := do
  match m with
  | none => mkAppExpr (← mkExpr (mkConst ``Option.none u)) t
  | some r => mkApp2Expr (← mkExpr (mkConst ``Option.some u)) t r

end Blaster.Optimize
