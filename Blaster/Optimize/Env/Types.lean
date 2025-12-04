import Lean
import Blaster.Data.HashSet
import Blaster.Data.HashMap
import Blaster.Optimize.Expr
import Blaster.Optimize.Env.ContextMap
import Blaster.Optimize.MatchInfo
import Blaster.Smt.Term
import Blaster.Command.Options

open Lean Meta Blaster.Smt Blaster.Options
open Blaster.Data.HashSet Blaster.Data.HashMap

namespace Blaster.Optimize

/-- Type to cache inductive datatype instances and quantified functions
    that have already been translated.
-/
structure IndTypeDeclaration where
 /-- Unique name generated for datatype instance/quantified functions.
       - E.g., Given datatype instances `List T1` and `List T2`,
         names `List_<id1>` and `List_<id2>` will respectively be generated,

       - E.g., Given two quantified functions f1 : Int → Bool and f2 : Nat -> Bool,
         names `Fun_<id1>` and `Fun_<id2>` will respectively be generated.
     where `<idX>` is a Nat literal.

     This unique name is mainly used when generating the corresponding
     smt predicate qualifier for the datatype instance/quantified functions,
     that is required to specify the expected domain values for quantified variables.

     NOTE: Two (or more) polymorphic instances for an inductive datatype will generate
     the same name (see function `getIndInst` in `Translate.Qualifier`).
      - E.g., `List α` and `List β` will both have the same predicate qualifier name.

     NOTE: Two (or more) polymorphic quantified function will generate the same
     name (see function `getFunInstDecl` in `Translate.Qualifier`).
      - E.g., `f1 : α → Nat` and `f2 : β → Nat` will both have the same
        predicate qualifier name.

     NOTE: Polymorphic instances are detected transitively,
      - E.g., `List (Option α)` and `List (Option β)`
        will both generate the same predicate qualifier name.
      - E.g., `f1 : Term (List α) → Nat` and `f2 : Term (List β) → Nat`
        will both generate the same predicate qualifier name.
 -/
 instName : SmtSymbol
 /-- Corresponding Smt instantiated sort for the inductive datatype instance,
     E.g., `(List Int)` for instance List Int.
 -/
 instSort : SortExpr

 /-- unique @Instance_<UUID> sort generated for type universe. -/
 instInstanceSort : Option SortExpr

 /-- unique @apply function generated for each HOF/quantified function or lambda term. -/
 applyInstName : Option SmtSymbol

deriving Inhabited

instance : Repr IndTypeDeclaration where
  reprPrec _ _ := "<IndTypeDeclaration>"


structure ResetOptions where
  /-- Flag set to `true` only when optimizing a function argument. -/
  isAppArg : Bool := false

  /-- Flag set to `true` only when optimizing a ctor argument. -/
  isCtorArg : Bool := false

instance : Inhabited ResetOptions where
  default := {isAppArg := false, isCtorArg := false}


structure OptimizeOptions where
  /-- Flag to activate function normalization, e.g., `Nat.beq x y` to `BEq.beq Nat instBEqNat x y`.
      This flag is set to `false` when optimizing the recursive function body.
  -/
  normalizeFunCall : Bool := true

  /-- Flag set to `true` only when optimizing function name `f` in expression `f x₁ ... xₙ`.
      This is to avoid applying optimization twice on the body of non-recursive functions.
  -/
  inFunApp : Bool := false

  /-- Keep track of the analysis Step reached for bmc and k-induction. -/
  mcDepth : Nat

  /-- Options passed to the #solve command. -/
  solverOptions : BlasterOptions

  /-- The current (deepest) optimization context id. `0` = global/root. -/
  curCtx : CtxId := 0

  /-- Monotone allocator for fresh context ids. -/
  nextCtxId : CtxId := 1

  /-- Ids on the current root→current ancestor path. An `ContextMap` entry tagged `c`
      is visible iff `c ∈ active`. Size = current nesting depth (small). -/
  active : HashSet CtxId := HashSet.emptyWithCapacity 123

  resetOptions : ResetOptions

instance : Inhabited OptimizeOptions where
  default := { normalizeFunCall := true, inFunApp := false, mcDepth := 0, solverOptions := default, resetOptions := default }

structure BetaLambda where
  /-- beta reduced lambda expression with MVarId as applied arguments. -/
  betaReduced : Expr
  /-- MVarId expressions used as applied arguments -/
  mvarArgs : Array Expr

structure ForallMeta where
  /-- Given `e` of the form `forall xs, A`, `instExpr` corresponds to and
      instantiation of A with metavariables created for each `x` ∈ xs.
  -/
  instExpr : Expr
  /-- MVarId expressions used to instantiate the forall body -/
  mvarArgs : Array Expr

instance instBeqEnvExpr : BEq Expr where
  beq x y :=
    if exprEq x y then true
    else Expr.eqv x y

instance instBeqEnvName : BEq Name where
  beq x y :=
    if nameEq x y then true
    else Name.beq x y

abbrev HashConsSet := HashSet SharedExpr
abbrev RewriteCacheMap := HashMap CtxId (IO.Ref (HashMap PtrExpr Lean.Expr))
abbrev NotEqPatterns := HashSet PtrExpr -- an element corresponding to a match pattern
abbrev MatchNotEqPatternMap := ContextMap (IO.Ref NotEqPatterns)  -- with key corresponding to a match discriminator
abbrev BetaLambdaMap := HashMap InstKey BetaLambda -- with Nat corresponding to number of args applied to lambda expression.
abbrev ForallMetaMap := HashMap PtrExpr ForallMeta
abbrev MVarAssignments := HashMap PtrExpr Lean.Expr

/-- Type to keep hypothesis context -/
structure HypothesisContext where
  /-- Map keeping track of hypotheses introduced by implications/ite.
      Given an implication of the form `h : a → b`, the following entries are introduced in this map:
       - `a := h` ∈ hypothesisMap
       - When `a := e₁ ∧ e₂`
          - e₁ := Blaster.and_left e₁ e₂ h ∈ hypothesisMap
          - e₂ := Blaster.and_right e₁ e₂ h ∈ hypothesisMap
      The Map is populated only when Type(a) = Prop.
      The updated Map is considered only when optimizing `b`, which may also be an implication.
      (see `addHypotheses` function and `optimizeForall` rule).
  -/
  hypothesisMap : ContextMap Expr

  /-- Map keeping track of equality introduced by implications/ite/match.
      An entry in this map is expected to be one of the following forms:
        - fv := Expr
        - Expr := C
        - Expr := C x₁ ... xₙ
      Any occurrence of the key for a given context is replaced by the rhs value.
  -/
  equalityMap : ContextMap Expr

instance : Repr HypothesisMap where
  reprPrec _ _ := "<HypothesisMap>"

instance : Inhabited HypothesisContext where
  default := { hypothesisMap := ContextMap.empty
               equalityMap := ContextMap.empty
             }

/-- Type to keep parameter info for a given function -/
structure ParamInfo where
  /-- The binder annotation for the parameter. -/
  binderInfo : BinderInfo
  /-- Flag set to true when parameter type is a Prop -/
  isProp : Bool
deriving Inhabited, Repr

structure FunEnvInfo where
  /-- Parameters Info for current function -/
  paramsInfo : Array ParamInfo
  /-- Generic Function Type -/
  type : Expr
deriving Inhabited, Repr


structure CommonExpr where
  beq : Expr
  blasterDite : Expr
  blasterDecide : Expr
  boolType : Expr
  boolTrue : Expr
  boolFalse : Expr
  boolNot : Expr
  boolOr : Expr
  boolAnd : Expr
  eq : Expr
  inhabited : Expr
  instBEqNat : Expr
  instBEqOfDecEq : Expr
  instBEqOfDecEqNat : Expr
  instDecEqNat : Expr
  instIntLt : Expr
  instLTInt : Expr
  instLTNat : Expr
  instNatBeq : Expr
  instNatLt : Expr
  intType : Expr
  intAdd : Expr
  intEDiv : Expr
  intEMod : Expr
  intFDiv : Expr
  intFMod : Expr
  intLt : Expr
  intMul : Expr
  intNeg : Expr
  intNegSucc : Expr
  intOfNat : Expr
  intPow : Expr
  intSub : Expr
  intTDiv : Expr
  intTMod : Expr
  intToNat : Expr
  internalRecFun : Expr
  le : Expr
  lt : Expr
  ltCstr : Expr
  lawfulBEq : Expr
  natAdd : Expr
  natBeq : Expr
  natBEqInst : Expr
  natBle : Expr
  natBlt : Expr
  natDiv : Expr
  natLt : Expr
  natMod : Expr
  natMul : Expr
  natPow : Expr
  natSub : Expr
  natType : Expr
  notFalse : Expr
  propAnd : Expr
  propFalse : Expr
  propNot : Expr
  propOr : Expr
  propTrue : Expr
  propType : Expr
  stringMk : Expr
  stringType : Expr
  trueIntro : Expr

/-- A saved optimization-context scope: the parent context id to restore on exit
    and this context's own id. Carried on the optimize stack frames. -/
structure CtxScope where
  parent : CtxId
  /- current ctxId -/
  current : CtxId
deriving Inhabited, Repr

structure CtxReuseScope where
  /-- Context scope to be considered when restart is triggered for an ite/match expression -/
  scope : CtxScope
  /-- FVars to be reused when instantiating lambda terms for ite/match expression when restart is triggered -/
  fvars : Array Expr
deriving Inhabited, Repr

structure GenericMatchResult where
  /-- Generic match type used to perform match structural equality check -/
  appType : Expr
  /-- Generic parameters for polymorphic match (if any) -/
  genericFVars : Array Expr
deriving Inhabited, Repr

abbrev ContextReuseEntry := HashMap CtxId CtxReuseScope
abbrev ContextReuseMap := HashMap InstKey (IO.Ref ContextReuseEntry)

/-- Type defining the memoization cache for internally demanding functions. -/
structure MemoizeEnv where
  /-- Cache memoizing the isRecursiveFun result -/
  isRecFunCache : HashMap PtrName Bool

  /-- Cache memoizing the isInstance result -/
  isInstanceCache : HashMap PtrName Bool

  /-- Cache memoizing the isClassConstraint result -/
  isClassCache : HashMap PtrName Bool

  /-- Cache memoizing the getMatcherRecInfo? result -/
  getMatcherCache : HashMap PtrName (Option MatcherRecInfo)

  /-- Cache memoizing the getConstInfo result -/
  getConstInfoCache : HashMap PtrName ConstantInfo

  /-- Cache memoizing the inferType result -/
  inferTypeCache : HashMap PtrExpr Lean.Expr

  /-- Cache memoizing MatchInfo -/
  isMatcherCache : HashMap PtrName MatchInfo

  /-- Cache memoizing isPartialDef -/
  isPartialCache : HashMap PtrName Bool

  /-- Cache memoizing getFunEnvInfo result -/
  getFunEnvInfoCache : HashMap PtrExpr FunEnvInfo

  /-- Cache memoizing getFunBody result -/
  getFunBodyCache : HashMap PtrExpr (Option Lean.Expr)

  /-- Cache memoizing isProp result -/
  isPropCache : HashMap PtrExpr Bool

  /-- Cache memoizing match to ite normalization -/
  isMatchToIte : HashMap PtrName Bool

  /-- Cache memoizing isNotFun result -/
  isNotFunCache : HashMap PtrExpr Bool

  /-- Cache memoizing getMatchAlts result -/
  matchAltsCache : HashMap PtrExpr (Array Expr)

  /-- Cache memoizing betaLambda. -/
  betaLambdaCache : BetaLambdaMap

  /-- Cache memoizing forall meta telescope. -/
  forallMetaCache : ForallMetaMap

  /-- Commonly used expression -/
  commonExpr : CommonExpr

  /-- Cache memoizing genericMatchType result -/
  genericMatchCache : HashMap PtrExpr GenericMatchResult

  /-- Cache memoizing context reuse scope,
      with Nat corresponding to expression index in ite/match (e.g, 0 for first match rhs,
      1 for second match rhs, etc.
      Note that index 0 is used for both then/else expression.
  -/
  contextReuseCache : ContextReuseMap

  /-- Cache memoizing if an then/else/match rhs expression returns (even transitively) a ctor -/
  isCtorMatchPropCache : HashSet PtrExpr

private def mkCommonExpr : CommonExpr :=
  let le := mkConst ``LE.le [levelZero]
  let lt := mkConst ``LT.lt [levelZero]
  let intType := mkConst ``Int
  let instBEqOfDecEq := mkConst ``instBEqOfDecidableEq [levelZero]
  let instDecEqNat := mkConst ``instDecidableEqNat
  let instLTInt := mkConst ``Int.instLTInt
  let instIntLt := mkApp lt intType
  let beq := mkConst ``BEq.beq [levelZero]
  let natType := mkConst ``Nat
  let instBEqOfDecEqNat := mkApp instBEqOfDecEq natType
  let instBEqNat := mkApp instBEqOfDecEqNat instDecEqNat
  let instNatBeq := mkApp beq natType
  let instNatLt := mkApp lt natType
  let instLTNat := mkConst ``instLTNat
  { beq
  , blasterDite := mkConst ``Blaster.dite' [levelOne]
  , blasterDecide := mkConst ``Blaster.decide'
  , boolType := mkConst ``Bool
  , boolTrue := mkConst ``true
  , boolFalse := mkConst ``false
  , boolNot := mkConst ``not
  , boolOr := mkConst ``or
  , boolAnd := mkConst ``and
  , eq := mkConst ``Eq [levelOne]
  , inhabited := mkConst ``Inhabited [levelOne]
  , instBEqNat
  , instBEqOfDecEq
  , instBEqOfDecEqNat
  , instDecEqNat
  , instIntLt
  , instLTInt
  , instLTNat
  , instNatBeq
  , instNatLt
  , intType
  , intAdd := mkConst ``Int.add
  , intEDiv := mkConst ``Int.ediv
  , intEMod := mkConst ``Int.emod
  , intFDiv := mkConst ``Int.fdiv
  , intFMod := mkConst ``Int.fmod
  , intLt := mkApp instIntLt instLTInt
  , intMul := mkConst ``Int.mul
  , intNeg := mkConst ``Int.neg
  , intNegSucc := mkConst ``Int.negSucc
  , intOfNat := mkConst ``Int.ofNat
  , intPow := mkConst ``Int.pow
  , intSub := mkConst ``Int.sub
  , intTDiv := mkConst ``Int.tdiv
  , intTMod := mkConst ``Int.tmod
  , intToNat := mkConst ``Int.toNat
  , internalRecFun := mkConst `_recFun
  , le
  , lt
  , ltCstr := mkConst ``LT [levelZero]
  , lawfulBEq := mkConst ``LawfulBEq [levelZero]
  , natAdd := mkConst ``Nat.add
  , natBeq := mkConst ``Nat.beq
  , natBEqInst := mkApp instNatBeq instBEqNat
  , natBle := mkConst ``Nat.ble
  , natBlt := mkConst ``Nat.blt
  , natDiv := mkConst ``Nat.div
  , natLt := mkApp instNatLt instLTNat
  , natMod := mkConst ``Nat.mod
  , natMul := mkConst ``Nat.mul
  , natPow := mkConst ``Nat.pow
  , natSub := mkConst ``Nat.sub
  , natType
  , notFalse := mkConst ``not_false
  , propAnd := mkConst ``And
  , propFalse := mkConst ``False
  , propNot := mkConst ``Not
  , propOr := mkConst ``Or
  , propTrue := mkConst ``True
  , propType := mkSort levelZero
  , stringMk := mkConst ``String.mk
  , stringType := mkConst ``String
  , trueIntro := mkConst ``True.intro
  }

instance : Inhabited MemoizeEnv where
  default :=
  { isRecFunCache := HashMap.emptyWithCapacity 1024,
    isInstanceCache := HashMap.emptyWithCapacity 1024,
    isClassCache := HashMap.emptyWithCapacity 1024,
    getMatcherCache := HashMap.emptyWithCapacity 123,
    getConstInfoCache := HashMap.emptyWithCapacity 1024,
    inferTypeCache := HashMap.emptyWithCapacity 1024,
    isMatcherCache := HashMap.emptyWithCapacity 1024,
    isPartialCache := HashMap.emptyWithCapacity 1024,
    getFunEnvInfoCache := HashMap.emptyWithCapacity 1024,
    getFunBodyCache := HashMap.emptyWithCapacity 1024,
    isPropCache := HashMap.emptyWithCapacity 1024,
    isMatchToIte := HashMap.emptyWithCapacity 123,
    isNotFunCache := HashMap.emptyWithCapacity 1024,
    matchAltsCache := HashMap.emptyWithCapacity,
    betaLambdaCache := HashMap.emptyWithCapacity 1024,
    forallMetaCache := HashMap.emptyWithCapacity 1024,
    commonExpr := mkCommonExpr,
    genericMatchCache := HashMap.emptyWithCapacity 123,
    contextReuseCache := HashMap.emptyWithCapacity 1024,
    isCtorMatchPropCache := HashSet.emptyWithCapacity 1024
  }

structure LocalDeclContext where
  /-- local lean context updated when optimizing lambda and forall expression -/
  ctx : LocalContext

  /-- local instances  updated when optimizing lambda and forall expression -/
  localInsts : LocalInstances
deriving Inhabited

/-- Type defining the environment used when optimizing a lean theorem. -/
structure OptimizeEnv where
  /-- Cache use for hashconsing expressions -/
  hashConsCache : HashConsSet

  /-- Cache memoizing the normalization and rewriting performed on the lean theorem according
      to a given context.
  -/
  rewriteCache : RewriteCacheMap

  /-- Cache memoizing synthesized instances for Inhabited/LawfulBEq constraint. -/
  synthInstanceCache : HashMap PtrExpr (Option Lean.Expr)

  /-- Cache memoizing type for a match application of the form
       `f.match.n [p₁, ..., pₙ, d₁, ..., dₖ,, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`, s.t.:
      An entry in this map is expected to be of the form `Type(f.match.n [p₁, ..., pₙ])` := fun.match.n p₁ ... pₙ`
      where, `p₁, ..., pₙ` correspond to the arguments instantiating polymorphic params.
      This is used to determine equivalence between match functions (see function `structEqMatch?`).
  -/
  matchCache: HashMap PtrExpr Lean.Expr

  /-- Cache memoizing instances of recursive functions.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := fdef`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic parameters of `f` (if any).
        - fdef: correspond to the recursive function body.
      TODO: UPDATE SPEC
  -/
  recFunInstCache : HashMap PtrExpr Lean.Expr

  /-- Cache keeping track of visited recursive function.
      Note that we here keep track of each instantiated polymorphic function.
  -/
  recFunCache : HashSet PtrExpr

  /-- Map to keep the normalized definition for each recursive function,
      which is also used to determine structural equivalence between functions
      (see function `storeRecFunDef`).
  -/
  recFunMap : HashMap PtrExpr Lean.Expr

  /-- Hypothesis context that is populated whether an implication or ite is encountered.
      The context is used only when optimization the implication's body or the then/else term of an ite.
  -/
  hypothesisContext : HypothesisContext

  /-- Map keeping track of non pattern match for a discriminator when processing a match rhs.
      (see `optimizeMatchAlt` function).

      NOTE: The updated Map context is considered only when optimizing each `tᵢ`.
  -/
  matchInContext : MatchNotEqPatternMap

  /-- Memoization maps (see not on MemoizeEnv) -/
  memCache : MemoizeEnv

  /-- Optimization options (see note on OptimizeOptions) -/
  options : OptimizeOptions

  /-- Flag to be set to `true` when there is a need to apply optimization
      again on a given expression.
  -/
  restart : Bool

  /-- local declaration context -/
  ctx : LocalDeclContext

  /-- MVar assignment map using only during beta-reduction and unification. -/
  mAssignments : MVarAssignments


instance : Inhabited OptimizeEnv where
  default :=
   let memCache := default
   let hashConsCache : HashConsSet :=
     List.foldr (fun (c : Expr) s => s.insert c) (HashSet.emptyWithCapacity 4096)
     [ memCache.commonExpr.beq
     , memCache.commonExpr.blasterDite
     , memCache.commonExpr.blasterDecide
     , memCache.commonExpr.boolType
     , memCache.commonExpr.boolTrue
     , memCache.commonExpr.boolFalse
     , memCache.commonExpr.boolNot
     , memCache.commonExpr.boolOr
     , memCache.commonExpr.boolAnd
     , memCache.commonExpr.eq
     , memCache.commonExpr.inhabited
     , memCache.commonExpr.instBEqNat
     , memCache.commonExpr.instBEqOfDecEq
     , memCache.commonExpr.instBEqOfDecEqNat
     , memCache.commonExpr.instDecEqNat
     , memCache.commonExpr.instIntLt
     , memCache.commonExpr.instLTInt
     , memCache.commonExpr.instLTNat
     , memCache.commonExpr.instNatBeq
     , memCache.commonExpr.instNatLt
     , memCache.commonExpr.intType
     , memCache.commonExpr.intAdd
     , memCache.commonExpr.intEDiv
     , memCache.commonExpr.intEMod
     , memCache.commonExpr.intFDiv
     , memCache.commonExpr.intFMod
     , memCache.commonExpr.intLt
     , memCache.commonExpr.intMul
     , memCache.commonExpr.intNeg
     , memCache.commonExpr.intNegSucc
     , memCache.commonExpr.intOfNat
     , memCache.commonExpr.intPow
     , memCache.commonExpr.intSub
     , memCache.commonExpr.intTDiv
     , memCache.commonExpr.intTMod
     , memCache.commonExpr.intToNat
     , memCache.commonExpr.internalRecFun
     , memCache.commonExpr.le
     , memCache.commonExpr.lt
     , memCache.commonExpr.ltCstr
     , memCache.commonExpr.lawfulBEq
     , memCache.commonExpr.natAdd
     , memCache.commonExpr.natBeq
     , memCache.commonExpr.natBEqInst
     , memCache.commonExpr.natBle
     , memCache.commonExpr.natBlt
     , memCache.commonExpr.natDiv
     , memCache.commonExpr.natLt
     , memCache.commonExpr.natMod
     , memCache.commonExpr.natMul
     , memCache.commonExpr.natPow
     , memCache.commonExpr.natSub
     , memCache.commonExpr.natType
     , memCache.commonExpr.notFalse
     , memCache.commonExpr.propAnd
     , memCache.commonExpr.propFalse
     , memCache.commonExpr.propNot
     , memCache.commonExpr.propOr
     , memCache.commonExpr.propTrue
     , memCache.commonExpr.propType
     , memCache.commonExpr.stringMk
     , memCache.commonExpr.stringType
     , memCache.commonExpr.trueIntro
     ]
   { hashConsCache,
     rewriteCache := HashMap.emptyWithCapacity 1024
     synthInstanceCache := HashMap.emptyWithCapacity,
     matchCache := HashMap.emptyWithCapacity,
     recFunInstCache := HashMap.emptyWithCapacity,
     recFunCache := HashSet.emptyWithCapacity,
     recFunMap := HashMap.emptyWithCapacity,
     hypothesisContext := default,
     matchInContext := ContextMap.empty,
     memCache,
     options := default,
     restart := false,
     ctx := default,
     mAssignments := HashMap.emptyWithCapacity 1024
   }


structure TranslateOptions where
  /-- Cache keeping track of ArrowTN already declared in Smt instance,
      with `N` corresponding to the function arity.
  -/
  arrowTypeArities : HashMap Nat SmtSymbol

  /-- Set keeping track of all variables in matched terms, including named patterns.
      This set is provided only when translating matched terms and match rhs.
  -/
  inPatternMatching : HashSet FVarId

  /-- Map keeping track of axioms not of type Prop or opaque variables, encountered during translation.
      This set is used mainly to avoid multiple global declaration in the Smt instance.
  -/
  axiomMap : HashMap Name SmtSymbol

instance : Inhabited TranslateOptions where
  default := {arrowTypeArities := .emptyWithCapacity,
              inPatternMatching := .emptyWithCapacity,
              axiomMap := .emptyWithCapacity
             }

abbrev TopLevelVars := Array (List (SmtSymbol × Lean.Name))

abbrev ConversionFunCache := HashMap (SortExpr × SortExpr) SmtSymbol
abbrev AbstractTypeCache := HashMap PtrExpr SmtSymbol

/-- Type defining the environment used when translating to Smt-Lib. -/
structure SmtEnv where
  /-- Cache memoizing the translation to Smt-Lib term. -/
  translateCache : HashMap PtrExpr SmtTerm

  /-- Smt-Lib commands emitted to the backend solver. -/
  smtCommands : Array SmtCommand

  /-- Backend solver process. -/
  smtProc : Option (IO.Process.Child ⟨.piped, .piped, .piped⟩)

  /-- Cache keeping track of visited inductive datatype during translation. -/
  indTypeVisited : HashSet Lean.Name

  /-- Map to keep inductive datatype instances and quantified functions
      that has already been translated.
      An entry in this map may correspond to one of the following:
       - Given `d` the name of an inductive data type and `x₀ ... xₙ` its corresponding arguments (if any):
           - When `∀ i ∈ [0..n], ¬ isGenericParam xᵢ`,
              `d x₁ ... xₙ := {instName := n, instSort := (sd sx₀ .. sxₙ)}` ∈ indTypeInstCache
           - when `∃ i ∈ [0..n], isGenericParam xᵢ`,
              `λ b₀ → .. → bₘ → t x₀ ... xₙ` := {instName := n, instSort := (sd sx₀ .. sxₙ)}` ∈ indTypeInstCache
             with
               - `b₀ .. bₘ` corresponding to the polymorphic arguments (see `getIndInst`).

       - Given `f : α₀ → α₁ ... → αₙ` a quantified function:
           - When `∀ i ∈ [0..n], ¬ isGenericParam αᵢ`,
              `α₀ → α₁ ... → αₙ := {instName := n, instSort := (Array sα₀ sα₁ ... sαₙ)}` ∈ indTypeInstCache
           - When `∃ i ∈ [0..n], isGenericParam αᵢ`,
              `λ b₀ → .. → bₘ → α₀ → ... → α` := {instName := n, instSort := (Array sα₀ ... sαₙ)} ∈ indTypeInstCache
             with
               - `b₀ .. bₘ` corresponding to the polymorphic arguments (see `getFunInstDecl`).
       - Given a type universe t such that t.isProp:
            t := {instName := @isProp, instSort := Prop} ∈ indTypeInstCache
       - Given a type universe t such that ¬ t.isProp:
            t := {instName := @is{n}, instSort := n} ∈ indTypeInstCache
           with n corresponding to a unique smt symbol name.
     See note on `IndTypeDeclaration`.
  -/
  indTypeInstCache : HashMap PtrExpr IndTypeDeclaration

  /-- Cache keeping track of opaque functions, recursive function instances as well as undefined class functions
      that have already been translated.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := n`,
      where:
       - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic
          parameters of `f` (if any).
       - `n` corresponds an smt qualified identifier that is expected to be unique
          for each recursive function or undefined class function instances.
      TODO: UPDATE SPEC
  -/
  funInstCache : HashMap PtrExpr SmtQualifiedIdent

  /-- Hash keeping track of all translated fvars. (see function fvarIdToSmtSymbol)  -/
  fvarsCache : HashMap FVarId Nat

  /-- Hash keeping track of quantified fvars. This is essential
      to detect globally declared variables.
      The bool flag is set to `true` for globally declared variables or
      for top level forall quantifiers.
  -/
  quantifiedFVars : HashMap FVarId Bool

  /-- Array list keeping track of globally declared variables and the ones in
      the top level forall quantifier.
      This list is used exclusively when retrieving counterexample after a `sat` result
      is obtained from the backend smt solver.
      The Array index indicates the analysis step at which the variables where introduced.
  -/
  topLevelVars : TopLevelVars

  /-- Cache memoizing the string representation for an Smt Symbol -/
  symbolStrCache : HashMap SmtSymbol String

  /-- Hash Map keeping the FunEnvInfo for functions defined as Ctor arguments
      An entry in this Map will correspond to
        `{ctor}.{idx} := f ∈ funCtorCache`
      Where ctor is the name of the ctor and idx the index label generated at the smt level.
      Example, Given
        structure Ratio where
          numerator : Int
          denominator : Int
      The corresponding smt datatype declaration will be:
       - (declare-datatype @Tests.Uplc.Onchain.Ratio
           ( (Tests.Uplc.Onchain.Ratio.mk
              (Tests.Uplc.Onchain.Ratio.mk.1 Int)
              (Tests.Uplc.Onchain.Ratio.mk.2 Int)) ) )
      where
        - {ctor} = Tests.Uplc.Onchain.Ratio.mk
        - {idx} ∈ [1, 2]
  -/
  funCtorCache : HashMap Name FunEnvInfo

  /-- Hash Map keeping track of declared smt conversion functions
      from polymorphic to concrete datatype instances and vice-versa.
  -/
  coerceCache : ConversionFunCache

  /-- Set keeping track of Lean4 datatypes for which a corresponding abstract smt datatype has been defined -/
  abstractTypeCache : AbstractTypeCache

  /-- Translation options (see note on TranslateOptions) -/
  options: TranslateOptions

instance : Inhabited SmtEnv where
  default :=
   { translateCache := HashMap.emptyWithCapacity,
     smtCommands := Array.mkEmpty 1023,
     smtProc := default,
     indTypeVisited := HashSet.emptyWithCapacity,
     indTypeInstCache := HashMap.emptyWithCapacity,
     funInstCache := HashMap.emptyWithCapacity,
     fvarsCache := HashMap.emptyWithCapacity,
     quantifiedFVars := HashMap.emptyWithCapacity,
     topLevelVars := Array.mkEmpty 17,
     symbolStrCache := HashMap.emptyWithCapacity,
     funCtorCache := HashMap.emptyWithCapacity,
     coerceCache := HashMap.emptyWithCapacity,
     abstractTypeCache := HashMap.emptyWithCapacity,
     options := default
   }

/-- Type defining the environment used when optimizing a lean theorem and translating to Smt-lib. -/

structure TranslateEnv where
  /-- Environment used when translating to Smt-ling. -/
  smtEnv : SmtEnv
  /-- Environment used when optimization a lean expression. -/
  optEnv : OptimizeEnv

instance : Inhabited TranslateEnv where
  default :=
    { smtEnv := default,
      optEnv := default
    }

abbrev TranslateEnvT := StateRefT TranslateEnv MetaM

/-- Type to represent the parameters instantiating the implicit arguments for a given function.
    (see function `getImplicitParameters`)
-/
structure ImplicitInfo where
  /-- Corresponds to an effective parameter for a given function (implicit or not). -/
  effectiveArg : Expr

  /-- Flag set to `true` when the effective parameter instantiates an implicit parameter. -/
  isInstance : Bool

  /-- Flag set to `true` when the effective parameter instantiates an implicit parameter
      but is still polymorphic, i.e., predicate `isGenericParam` is satisfied.
  -/
  isGeneric : Bool

deriving Repr, Inhabited

abbrev ImplicitParameters := Array ImplicitInfo


def getMCtx' : MetaM MetavarContext := do
  return (← get).mctx

def modifyMCtx' (f : MetavarContext → MetavarContext) : MetaM Unit := modifyMCtx f

instance : MonadMCtx TranslateEnvT where
  getMCtx := getMCtx'
  modifyMCtx f := modifyMCtx' f

protected def throwEnvError (msg : MessageData) : TranslateEnvT α := do
  if let some p := (← get).smtEnv.smtProc then
    p.kill
    discard $ p.wait
  throwError msg

/-- macro `throwEnvError` to avoid applying format on msg before throwEnvError is called -/
syntax "throwEnvError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwEnvError $msg:interpolatedStr) => `(Blaster.Optimize.throwEnvError (m! $msg))
  | `(throwEnvError $msg:term)            => `(Blaster.Optimize.throwEnvError $msg)

@[inline] def modifyOptEnv (f : OptimizeEnv → OptimizeEnv) : TranslateEnvT Unit :=
  modify fun ⟨s, o⟩ => ⟨s, f o⟩

/-- Update global rewrite cache with `a := b`. -/
@[inline] def updateHashConsCache (a : SharedExpr) : TranslateEnvT Unit := do
  modifyOptEnv fun ⟨hashConsCache, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨hashConsCache.insert a, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩


/-- Update rewrite cache at CtxId 0 with `a := b`. -/
@[always_inline, inline]
def updateGlobalRewriteCache (a : Expr) (b : Expr) (insertIfNew := false) : TranslateEnvT Unit := do
  match (← get).optEnv.rewriteCache.get? 0 with
  | none =>
      let refEntry ← IO.mkRef $ (HashMap.emptyWithCapacity 2048 : HashMap PtrExpr Expr).insert a b
      modifyOptEnv
        fun ⟨o1, rewriteCache, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
            ⟨o1, rewriteCache.insert 0 refEntry, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩
  | some refEntry => refEntry.modify (λ h => if insertIfNew then h.insertIfNew a b else h.insert a b)


/-- Update rewrite cache at curCtx with `a := b`. -/
@[always_inline, inline]
def updateLocalRewriteCache (a : Expr) (b : Expr) (insertIfNew := false) : TranslateEnvT Unit := do
  let ⟨_, rewriteCache, _, _, _, _, _, _, _, _, ⟨_, _, _, _, curCtx, _, _, _⟩, _, _, _⟩ := (← get).optEnv
  match rewriteCache.get? curCtx with
  | none =>
       let refEntry ← IO.mkRef $ (HashMap.emptyWithCapacity 256 : HashMap PtrExpr Expr).insert a b
       modifyOptEnv
         fun ⟨o1, rewriteCache, o3, o4, o5, o6, o7, o8, o9, o10, options, o12, o13, o14⟩ =>
             ⟨o1, rewriteCache.insert options.curCtx refEntry, o3, o4, o5, o6, o7, o8, o9, o10, options, o12, o13, o14⟩
  | some refEntry => refEntry.modify (λ h => if insertIfNew then h.insertIfNew a b else h.insert a b)

/-- Update synthesize decidable instance cache with `a := b`. -/
@[always_inline, inline]
def updateSynthCache (a : Expr) (b : Option Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, synthInstanceCache, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨o1, o2, synthInstanceCache.insert a b, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

/-- remove `a` from hash cons cache. -/
@[always_inline, inline]
def removeFromHashConsCache (a : SharedExpr) : TranslateEnvT Unit := do
  modifyOptEnv fun ⟨hashConsCache, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨hashConsCache.erase a, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

@[always_inline, inline]
def updateEqualityMap (lhs : Expr) (rhs : Expr) (ctxId : CtxId) : TranslateEnvT Unit := do
  match (← get).optEnv.hypothesisContext.equalityMap.get? lhs with
  | none =>
       let refEntry ← IO.mkRef [(ctxId, rhs)]
       modifyOptEnv
         fun ⟨o1, o2, o3, o4, o5, o6, o7, ⟨hypothesisMap, equalityMap⟩, o9, o10, o11, o12, o13, o14⟩ =>
             ⟨o1, o2, o3, o4, o5, o6, o7, ⟨hypothesisMap, equalityMap.insert lhs refEntry⟩, o9, o10, o11, o12, o13, o14⟩
  | some refEntry => refEntry.modify (λ l => (ctxId, rhs) :: l)

/-- Look up `lhs` in the context-aware equality map, returning the rhs of the
    newest entry visible in the current context (tag ∈ active). -/
@[always_inline, inline]
def eqMapFind? (lhs : Expr) : TranslateEnvT (Option Expr) := do
  let ⟨_, _, _, _, _, _, _, ⟨_, equalityMap⟩, _, _, ⟨_, _, _, _, _, _, active, _⟩, _, _, _⟩ := (← get).optEnv
  if equalityMap.size == 0
  then return none
  else ContextMap.findRaw equalityMap active lhs


/-- Context-aware lookup in the (now context-id-tagged) hypothesis map: returns the
    proof of the newest entry for `e` whose tag is active in the current context. -/
@[always_inline, inline]
def hypMapFind? (e : Expr) : TranslateEnvT (Option Expr) := do
  let ⟨_, _, _, _, _, _, _, ⟨hypothesisMap, _⟩, _, _, ⟨_, _, _, _, _, _, active, _⟩, _, _, _⟩ := (← get).optEnv
  if hypothesisMap.size == 0
  then return none
  else ContextMap.findRaw hypothesisMap active e

/-- `true` iff `e` is present (and active) in the hypothesis map. -/
@[always_inline, inline]
def hypMapContains (e : Expr) : TranslateEnvT Bool :=
 if e.hasMVar then return false
 else  return (← hypMapFind? e).isSome

/-- Allocate a fresh context id and make it current. -/
@[always_inline, inline]
def newCtx : TranslateEnvT CtxScope := do
 modifyGet fun env =>
   let current := env.optEnv.options.nextCtxId
   let parent := env.optEnv.options.curCtx
   (⟨parent, current⟩, {env with optEnv.options.nextCtxId := current + 1, optEnv.options.curCtx := current
                                 optEnv.options.active := env.optEnv.options.active.insert current })

@[always_inline, inline]
def setAndCommitCtx (s : CtxScope) : TranslateEnvT Unit :=
  modify fun env => { env with optEnv.options.curCtx := s.current,
                               optEnv.options.active := env.optEnv.options.active.insert s.current }

/-- Leave a committed scope: deactivate its id, restore the parent and delete the corresponding rewrite cache.
    Its entries remain in the map (tagged, now invisible).
-/
@[always_inline, inline]
def endCtx (s : CtxScope) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, rewrite, o3, o4, o5, o6, o7, o8, o9, o10, ⟨s1, s2, s3, s4, _, s6, active, s7⟩, o12, o13, o14⟩ =>
                   ⟨o1, rewrite.erase s.current, o3, o4, o5, o6, o7, o8, o9, o10,
                   ⟨s1, s2, s3, s4, s.parent, s6, active.erase s.current, s7⟩, o12, o13, o14⟩



/-- Look up function for Context reuse cache, returning the entry for which the parent correspond to the
    current CtxId (if exists).
-/
@[always_inline, inline]
def ContextReuseMap.findRaw (m : ContextReuseMap) (e : Expr) (idx : USize) (curCtx : CtxId) : IO (Option CtxReuseScope) := do
  match m.get? (mkInstKey e idx) with
  | none => return none
  | some refEntry => return (← refEntry.get).get? curCtx


@[always_inline, inline]
def reuseContext? (e : Expr) (idx : USize) : TranslateEnvT (Option CtxReuseScope) := do
  let ⟨_, _, _, _, _, _, _, _, _, memCache, ⟨_, _, _, _, curCtx, _, _, _⟩, _, _, _⟩ := (← get).optEnv
  memCache.contextReuseCache.findRaw e idx curCtx

@[always_inline, inline]
def withParentHyps (s : CtxScope) (k : TranslateEnvT α) : TranslateEnvT α := do
  modify fun env => {env with optEnv.options.active := env.optEnv.options.active.erase s.current}
  let r ← k
  modify fun env => {env with optEnv.options.active := env.optEnv.options.active.insert s.current}
  return r

@[always_inline, inline]
def updateLocalContext (h : LocalDeclContext) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, _, o14⟩ =>
                   ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, h, o14⟩

@[always_inline, inline]
def assignMVar (mvar : Expr) (val : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun optEnv => {optEnv with mAssignments := optEnv.mAssignments.insert mvar val}

@[inline] def updateMatchCache (t : Expr) (res : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, matchCache, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨o1, o2, o3, matchCache.insert t res, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

/-- Add an instance recursive application (see function `getInstApp`) to
    the visited recursive function cache.
-/
@[inline] def cacheFunName (f : Expr) : TranslateEnvT Unit :=
 modifyOptEnv fun ⟨o1, o2, o3, o4, o5, recFunCache, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                  ⟨o1, o2, o3, o4, o5, recFunCache.insert f, o7, o8, o9, o10, o11, o12, o13, o14⟩

/-- Remove an instance recursive application (see function `getInstApp`) from
    the visited recursive function cache.
-/
@[inline] def uncacheFunName (f : Expr) : TranslateEnvT Unit :=
 modifyOptEnv fun ⟨o1, o2, o3, o4, o5, recFunCache, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                  ⟨o1, o2, o3, o4, o5, recFunCache.erase f, o7, o8, o9, o10, o11, o12, o13, o14⟩

/-- Given `f` which is either a function name expression or a fully/partially instantiated polymorphic function (see `getInstApp`),
    and `fbody` corresponding to `f`'s definition, update the recursive instance cache (i.e., `recFunInstCache`),
-/
@[inline] def updateRecFunInst (f : Expr) (fbody : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, o4, recFunInstCache, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨o1, o2, o3, o4, recFunInstCache.insert f fbody, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

@[inline] def updateRecFunMap (body : Expr) (f : Expr) : TranslateEnvT Unit :=
  modifyOptEnv fun ⟨o1, o2, o3, o4, o5, o6, recFunMap, o8, o9, o10, o11, o12, o13, o14⟩ =>
                   ⟨o1, o2, o3, o4, o5, o6, recFunMap.insert body f, o8, o9, o10, o11, o12, o13, o14⟩

/-- Return the current analysis Step -/
@[always_inline, inline]
def getCurrentDepth : TranslateEnvT Nat :=
  return (← get).optEnv.options.mcDepth

/-- set restart flag to `true`. -/
@[always_inline, inline]
def setRestart : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.restart := true })

/-- reset restart flag to `false`. -/
@[always_inline, inline]
def resetRestart : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.restart := false })

/-- Return the restart flag. -/
@[always_inline, inline]
def isRestart : TranslateEnvT Bool :=
  return (← get).optEnv.restart

/-- set optimize option `normalizeFunCall` to `b`. -/
@[always_inline, inline]
def setNormalizeFunCall (b : Bool) : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.options.normalizeFunCall := b })

/-- set optimize option `inFunApp` to `b`. -/
@[always_inline, inline]
def setInFunApp (b : Bool) : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.options.inFunApp := b })

/-- Return `true` if optimize option `inFunApp` is set to `true`. -/
@[always_inline, inline]
def isInFunApp : TranslateEnvT Bool :=
  return (← get).optEnv.options.inFunApp


/-- set optimize option `isAppArg` to `b`. -/
@[always_inline, inline]
def setIsAppArg (b : Bool) : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.options.resetOptions.isAppArg := b })

/-- Return `true` if optimize option `isAppArg` is set to `true`. -/
@[always_inline, inline]
def isAppArg : TranslateEnvT Bool :=
  return (← get).optEnv.options.resetOptions.isAppArg

/-- set optimize option `isCtorArg` to `b`. -/
@[always_inline, inline]
def setIsCtorArg (b : Bool) : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.options.resetOptions.isCtorArg := b })

/-- Return `true` if optimize option `isCtorArg` is set to `true`. -/
@[always_inline, inline]
def isCtorArg : TranslateEnvT Bool :=
  return (← get).optEnv.options.resetOptions.isCtorArg

/-- set optimize option `resetOptions` to `r`. -/
@[always_inline, inline]
def setResetOptions (r : ResetOptions) : TranslateEnvT Unit :=
  modify (fun env => { env with optEnv.options.resetOptions := r})

@[always_inline, inline]
def getMatchContext : TranslateEnvT MatchNotEqPatternMap :=
  return (← get).optEnv.matchInContext


/--
  Return the local declaration for the given free variable.
  Throw an exception if local declaration is not in the current local context.
-/
@[always_inline, inline]
def _root_.Lean.FVarId.getEnvDecl (fvarId : FVarId) : TranslateEnvT LocalDecl := do
  match (← get).optEnv.ctx.ctx.find? fvarId with
  | some d => return d
  | none   => throwEnvError "unknown fvar {reprStr fvarId}"

def _root_.Lean.FVarId.getEnvValue? (fvarId : FVarId) : TranslateEnvT (Option Expr) :=
  return (← fvarId.getEnvDecl).value?

def _root_.Lean.FVarId.getEnvType (fvarId : FVarId) : TranslateEnvT Expr :=
  return (← fvarId.getEnvDecl).type

def _root_.Lean.FVarId.getEnvUserName (fvarId : FVarId) : TranslateEnvT Name :=
  return (← fvarId.getEnvDecl).userName

/-- Return `true` only when e is a FVar of type `∀ α₀ → ... → αₙ`. -/
@[always_inline, inline]
def isQuantifiedFun (e : Expr) : TranslateEnvT Bool :=
  match e with
  | Expr.fvar v => return (← v.getEnvType).isForall
  | _ => return false

@[always_inline, inline]
def mkLocalContext : MetaM LocalDeclContext :=
  return { ctx := ← getLCtx, localInsts := ← getLocalInstances }

@[always_inline, inline]
def withLocalContext (f : TranslateEnvT α) : TranslateEnvT α := do
  let ctx := (← get).optEnv.ctx
  withLCtx ctx.ctx ctx.localInsts $ do f

@[inline] def modifyMemCache (f : MemoizeEnv → MemoizeEnv) : TranslateEnvT Unit :=
  modify fun ⟨s, ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩⟩ =>
             ⟨s, ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, f o10, o11, o12, o13, o14⟩⟩

@[inline] def updateConstInfoCache (n : Name) (info : ConstantInfo) : TranslateEnvT Unit :=
  modifyMemCache fun ⟨m1, m2, m3, m4, getConstInfoCache, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, getConstInfoCache.insert n info, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateBetaLambdaCache (key : InstKey) (decl : BetaLambda) : TranslateEnvT Unit := do
  unsafe modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, betaLambdaCache, m16, m17, m18, m19, m20⟩ =>
                            ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14,
                             betaLambdaCache.insert key decl, m16, m17, m18, m19, m20⟩

@[inline] def updateForallMetaCache (t : Expr) (inst : ForallMeta) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, forallMetaCache, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, forallMetaCache.insert t inst, m17, m18, m19, m20⟩

@[inline] def updateInstanceCache (f : Name) (b : Bool) : TranslateEnvT Unit :=
  modifyMemCache fun ⟨m1, isInstanceCache, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, isInstanceCache.insert f b, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateIsRecFunCache (f : Name) (b : Bool) : TranslateEnvT Unit :=
  modifyMemCache fun ⟨isRecFunCache, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨isRecFunCache.insert f b, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateIsClassCache (n : Name) (b : Bool) : TranslateEnvT Unit :=
  modifyMemCache fun ⟨m1, m2, isClassCache, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, isClassCache.insert n b, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateMatcherCache (n : Name) (m : Option MatcherRecInfo) : TranslateEnvT Unit :=
  modifyMemCache fun ⟨m1, m2, m3, getMatcherCache, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, getMatcherCache.insert n m, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateIsMatcherCache (n : Name) (mInfo : MatchInfo) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, isMatcherCache, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, isMatcherCache.insert n mInfo, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateIsPartialCache (n : Name) (b : Bool) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, isPartialCache, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, isPartialCache.insert n b, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateInferTypeCache (e : Expr) (t : Expr) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, inferTypeCache, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, inferTypeCache.insert e t, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updatePropCache (e : Expr) (b : Bool) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, isPropCache, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, isPropCache.insert e b, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateFunInfoCache (f : Expr) (info : FunEnvInfo) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, getFunEnvInfoCache, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, getFunEnvInfoCache.insert f info, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateFunBodyCache (f : Expr) (body : Option Expr) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, getFunBodyCache, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, getFunBodyCache.insert f body, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateIsNotFunCache (e : Expr) (b : Bool) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, isNotFunCache, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, isNotFunCache.insert e b, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateMatchAltsCache (genApp : Expr) (alts : Array Expr) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, matchAltsCache, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, matchAltsCache.insert genApp alts, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateMatchToIteCache (n : Name) (b : Bool) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, isMatchToIte, m13, m14, m15, m16, m17, m18, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, isMatchToIte.insert n b, m13, m14, m15, m16, m17, m18, m19, m20⟩

@[inline] def updateGenericMatchCache (genType : Expr) (g : GenericMatchResult) : TranslateEnvT Unit := do
  modifyMemCache fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, genericMatchCache, m19, m20⟩ =>
                     ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, genericMatchCache.insert genType g, m19, m20⟩

@[inline] def updateCtorMatchPropCache (e : Expr) : TranslateEnvT Unit :=
  modifyMemCache fun
    ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, isCtorMatchPropCache⟩ =>
    ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, isCtorMatchPropCache.insert e⟩

@[always_inline, inline]
def updateContextReuseCache (e : Expr) (idx : USize) (s : CtxReuseScope) : TranslateEnvT Unit := do
  let key := mkInstKey e idx
  match (← get).optEnv.memCache.contextReuseCache.get? key with
  | none =>
      let refEntry ← IO.mkRef (HashMap.emptyWithCapacity.insert s.scope.parent s)
      modifyMemCache
        fun ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, contextReuseCache, m20⟩ =>
            ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16,
             m17, m18, contextReuseCache.insert key refEntry, m20⟩
  | some refEntry => refEntry.modify (λ h => h.insert s.scope.parent s)


@[inline] def propagateReuseContext (current : Expr) (next : Expr) (idx : USize) : TranslateEnvT Unit := do
  let ⟨_, _, _, _, _, _, _, _, _, memCache, ⟨_, _, _, _, curCtx, _, _, _⟩, _, _, _⟩ := (← get).optEnv
  match ← memCache.contextReuseCache.findRaw current idx curCtx with
  | some reuse => updateContextReuseCache next idx reuse
  | none => return ()

@[inline] partial def freeRewriteCacheRange (startCtxId : CtxId) (endCtxId : CtxId) : TranslateEnvT Unit := do
  let rec eraseUnusedCtx (idx : CtxId) (rewrite : RewriteCacheMap) : RewriteCacheMap :=
    if idx ≥ endCtxId then rewrite
    else eraseUnusedCtx (idx + 1) (rewrite.erase idx)
  modifyOptEnv fun ⟨o1, rewrite, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
                    let rewrite := eraseUnusedCtx startCtxId rewrite
                    ⟨o1, rewrite, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

@[inline] def freeRewriteCacheReuse (e : Expr) (idx : USize) : TranslateEnvT Unit := do
  let ⟨_, _, _, _, _, _, _, _, _, memCache, ⟨_, _, _, _, curCtx, _, _, _⟩, _, _, _⟩ := (← get).optEnv
  match ← memCache.contextReuseCache.findRaw e idx curCtx with
  | some reuse =>
      modifyOptEnv
        fun ⟨o1, rewrite, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩ =>
            ⟨o1, rewrite.erase reuse.scope.current, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14⟩

  | none => return ()

/-- Return `true` if optimize option `normalizeFunCall` is set to `true`. -/
def isOptimizeRecCall : TranslateEnvT Bool :=
  return (← get).optEnv.options.normalizeFunCall

@[always_inline, inline]
def findGlobalCache (a : Expr) (env : TranslateEnv) : IO Expr :=
  match env.optEnv.rewriteCache.get? 0 with
  | none => return instCacheMiss
  | some refEntry => return (← refEntry.get).getD a instCacheMiss

@[always_inline, inline]
def findLocalCache (a : Expr) (env : TranslateEnv) : IO Expr :=
  match env.optEnv.rewriteCache.get? env.optEnv.options.curCtx with
  | none => return instCacheMiss
  | some refEntry => return (← refEntry.get).getD a instCacheMiss

end Blaster.Optimize

