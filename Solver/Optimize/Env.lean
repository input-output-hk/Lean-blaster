import Lean
import Solver.Optimize.Opaque
import Solver.Smt.Term
import Solver.Command.Options

open Lean Meta Solver.Smt Solver.Options

namespace Solver.Optimize


/-- Type to cache inductive datatype instances that have already been translated.
    TODO: UPDATE
-/
structure IndTypeDeclaration where
 instName : SmtSymbol -- name for instance predicate qualifier
 instSort : SortExpr
deriving Inhabited

structure OptimizeOptions where
  /-- Flag to activate const normalization, especially when function
      are passed as arguments.
      This flag is set to `false` when optimization a function application,
      i.e., Given application `f x₁ ... xₙ` optimization on `f` is performed with
      `normalizeConst` set to `false`.
  -/
  normalizeConst : Bool := true
  /-- Flag to activate function normalization, e.g., `Nat.beq x y` to `BEq.beq Nat instBEqNat x y`.
      This flag is set to `false` when optimizing the recursive function body
      of an opaque function f ∈ recFunsToNormalize`.
  -/
  normalizeFunCall : Bool := true

  /-- Options passed to the #solve command. -/
  solverOptions : SolverOptions

instance : Inhabited OptimizeOptions where
  default := {normalizeConst := true, normalizeFunCall := true, solverOptions := default}

/-- Type defining the environment used when optimizing a lean theorem. -/
structure OptimizeEnv where
  /-- Cache memoizing the normalization and rewriting performed on the lean theorem. -/
  rewriteCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing synthesized instances for Decidable/Inhabited constraint. -/
  synthInstanceCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing the whnf result. -/
  whnfCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing type for a match application of the form
       `f.match.n [p₁, ..., pₙ, d₁, ..., dₖ,, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`, s.t.:
      An entry in this map is expected to be of the form `Type(f.match.n [p₁, ..., pₙ])` := fun.match.n p₁ ... pₙ`
      where, `p₁, ..., pₙ` correspond to the arguments instantiating polymorphic params.
      This is used to determine equivalence between match functions (see function `structEqMatch?`).
  -/
  matchCache: HashMap Lean.Expr Lean.Expr

  /-- Cache memoizing instances of recursive functions.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := fdef`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic parameters of `f` (if any).
        - fdef: correspond to the recursive function body.
      TODO: UPDATE
  -/
  recFunInstCache : HashMap Lean.Expr Lean.Expr
  /-- Cache keeping track of visited recursive function.
      Note that we here keep track of each instantiated polymorphic function.
  -/
  recFunCache: HashSet Lean.Expr
  /-- Map to keep the normalized definition for each recursive function,
      which is also used to determine structural equivalence between functions
      (see function `storeRecFunDef`).
  -/
  recFunMap: HashMap Lean.Expr Lean.Expr

  /-- Optimization options (see note on OptimizeOptions) -/
  options : OptimizeOptions

 deriving Inhabited

/-- Type defining the environment used when translating to Smt-Lib. -/
structure SmtEnv where
  /-- Cache memoizing the translation to Smt-Lib term. -/
  translateCache : HashMap Lean.Expr SmtTerm

  /-- Smt-Lib commands emitted to the backend solver. -/
  smtCommands : Array SmtCommand

  /-- Backend solver process. -/
  smtProc : Option (IO.Process.Child ⟨.piped, .piped, .piped⟩)

  /-- Cache keeping track of visited inductive datatype during translation. -/
  indTypeVisited : HashSet Lean.Name

  /-- Map to keep instances of inductive datatypes that has already been
      translated.
      An entry in this map is expected to be of the form `d x₁ ... xₙ := n`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic
          parameters of `d` (if any).
        - `n` corresponds to a unique name generated for the inductive instance.
      TODO: UPDATE
  -/
  indTypeInstCache : HashMap Lean.Expr IndTypeDeclaration

  /-- Cache keeping track of opaque functions, recursive function instances as well as undefined class functions
      that have already been translated.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := n`,
      where:
       - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic
          parameters of `f` (if any).
       - `n` corresponds an smt qualified identifier that is expected to be unique
          for each recursive function or undefined class function instances.
      TODO UPDATE
  -/
  funInstCache : HashMap Lean.Expr SmtQualifiedIdent

  /-- Cache keeping track of sort that have already been declared. -/
  sortCache : HashMap FVarId SmtSymbol

  /-- Set keeping track of quantified fvars. This is essential
      to detect globally declared variables. -/
  quantifiedFVars : HashSet FVarId

  /-- Set keeping track of globally declared variables and the ones in
      the top level forall quantifier.
      This set is used exclusived when retrieving counterexample after a `sat` result
      is obtained from the backend smt solver.
  -/
  topLevelVars : HashSet SmtSymbol

  /-- Flag set when universe @Type has already been declared Smt instance. -/
  typeUniverse : Bool := false

  /-- This flag is set to `true` only when translating recursive function definition. -/
  inFunRecDefinition : Bool := false

  deriving Inhabited


/-- list of recursive functions to be normalized (see note in `OptimizeOptions`). -/
def recFunsToNormalize : NameHashSet :=
  List.foldr (fun c s => s.insert c) HashSet.empty
  [ ``Nat.beq,
    ``Nat.ble
  ]

/-- Type defining the environment used when optimizing a lean theorem and translating to Smt-lib. -/
structure TranslateEnv where
  /-- Environment used when translating to Smt-ling. -/
  smtEnv : SmtEnv
  /-- Environment used when optimization a lean expression. -/
  optEnv : OptimizeEnv
deriving Inhabited

abbrev TranslateEnvT := StateRefT TranslateEnv MetaM

def throwEnvError (msg : MessageData) : TranslateEnvT α := do
  if let some p := (← get).smtEnv.smtProc then
    p.kill
    discard $ p.wait
  throwError msg

/-- Return `true` if `op1` and `op2` are physically equivalent, i.e., points to same memory address.
-/
@[inline] private unsafe def exprEqUnsafe (op1 : Expr) (op2 : Expr) : MetaM Bool :=
  pure (ptrEq op1 op2)

/-- Safe implementation of physically equivalence for Expr.
-/
@[implemented_by exprEqUnsafe]
def exprEq (op1 : Expr) (op2 : Expr) : MetaM Bool := isDefEqGuarded op1 op2

/-- set optimize option `normalizeConst` to `b`. -/
def setNormalizeConst (b : Bool) : TranslateEnvT Unit := do
  let env ← get
  let options := env.optEnv.options
  let optEnv := {env.optEnv with options := {options with normalizeConst := b}}
  set {env with optEnv := optEnv }

/-- set optimize option `normalizeFunCall` to `b`. -/
def setNormalizeFunCall (b : Bool) : TranslateEnvT Unit := do
  let env ← get
  let options := env.optEnv.options
  let optEnv := {env.optEnv with options := {options with normalizeFunCall := b}}
  set {env with optEnv := optEnv }

/-- Perform the following actions:
     - set normalizeConst to `false`
     - execute `f`
     - set normalizeConst to `true`
-/
def withOptimizeFunApp (f: TranslateEnvT Expr) : TranslateEnvT Expr := do
  setNormalizeConst false
  let e ← f
  setNormalizeConst true
  return e

/-- Perform the following actions:
     - set normalizeFunCall to `false`
     - execute `f`
     - set normalizeFunCall to `true`
-/
def withOptimizeRecBody (f: TranslateEnvT Expr) : TranslateEnvT Expr := do
  setNormalizeFunCall false
  let e ← f
  setNormalizeFunCall true
  return e

/-- Perform the following actions:
     - let b := (← get).optEnv.options.normalizeFunCall
     - set normalizeFunCall to `true`
     - execute `f`
     - set normalizeFunCall to `b`
-/
def withRestoreRecBody (f: TranslateEnvT Expr) : TranslateEnvT Expr := do
  let b := (← get).optEnv.options.normalizeFunCall
  setNormalizeFunCall true
  let e ← f
  setNormalizeFunCall b
  return e


/-- set optimize option `inFunRecDefinition` to `b`. -/
def setInFunRecDefinition (b : Bool) : TranslateEnvT Unit := do
  let env ← get
  let smtEnv := {env.smtEnv with inFunRecDefinition := b}
  set {env with smtEnv := smtEnv }

/-- Perform the following actions:
     - set inFunRecDefinition to `true`
     - execute `f`
     - set inFunRecDefinition to `false`
-/
def withTranslateRecBody (f: TranslateEnvT α) : TranslateEnvT α := do
  setInFunRecDefinition true
  let t ← f
  setInFunRecDefinition true
  return t


/-- Return `true` if optimize option `normalizeConst` is set to `true`. -/
def isOptimizeConst : TranslateEnvT Bool :=
  return (← get).optEnv.options.normalizeConst

/-- Return `true` if optimize option `normalizeFunCall` is set to `true`. -/
def isOptimizeRecCall : TranslateEnvT Bool :=
  return (← get).optEnv.options.normalizeFunCall

/-- Return `true` if optimize option `inFunRecDefinition` is set to `true`. -/
def isInRecFunDefinition : TranslateEnvT Bool :=
  return (← get).smtEnv.inFunRecDefinition

/-- Update rewrite cache with `a := b`.
-/
def updateRewriteCache (a : Expr) (b : Expr) : TranslateEnvT Unit := do
  let env ← get
  let optEnv := {env.optEnv with rewriteCache := env.optEnv.rewriteCache.insert a b}
  set {env with optEnv := optEnv }

/-- Update synthesize decidable instance cache with `a := b`.
-/
def updateSynthCache (a : Expr) (b : Expr) : TranslateEnvT Unit := do
  let env ← get
  let optEnv := {env.optEnv with synthInstanceCache := env.optEnv.synthInstanceCache.insert a b}
  set {env with optEnv := optEnv }

/-- Return `a'` if `a := a'` is already in optimization cache.
    Otherwise, the following actions are performed:
      - add `a := a` in cache only when cacheResult is set to true
      - return `a`
-/
def mkExpr (a : Expr) (cacheResult := true) : TranslateEnvT Expr := do
  match (← get).optEnv.rewriteCache.find? a with
  | some a' => return a'
  | none => do
     if cacheResult then updateRewriteCache a a
     return a

/-- Return `b` if `a := b` is already in the optimization cache.
    Otherwise, the following actions are performed:
      - execute `b ← f ()`
      - update cache with `a := b`
      - return `b`
 NOTE: A call to `mkExpr` must be done whenever any new Expr is created during normalization and rewriting.
 This is so to ensure maximum sharing of expression.
 Moreover, this also ensure that we can direcly use pointer equality during simplification
 instead of the costly isDefEq function.
-/
def withOptimizeEnvCache (a : Expr) (f: Unit → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let env := (← get).optEnv
  match env.rewriteCache.find? a with
  | some b => return b
  | none => do
     let b ← f ()
     updateRewriteCache a b
     return b

/-- Add a recursive function (i.e., function name expression or an instantiated polymorphic function)
    to the visited recursive function cache.
-/
def cacheFunName (f : Expr) : TranslateEnvT Unit := do
 let env ← get
 let optEnv := {env.optEnv with recFunCache := env.optEnv.recFunCache.insert f}
 set {env with optEnv := optEnv }

/-- Remove a recursive function (i.e., function name expression or an instantiated polymorphic function)
    from the visited recursive function cache.
-/
def uncacheFunName (f : Expr) : TranslateEnvT Unit := do
 let env ← get
 let optEnv := {env.optEnv with recFunCache := env.optEnv.recFunCache.erase f}
 set {env with optEnv := optEnv }


/-- Internal genralized rec fun const to be used for in normalized recursive
    definition kept in `recFunMap`.
-/
def internalRecFun : Name := `_recFun


/-- Tag expression as recursive call. This metadata is used when
    replacing a recursive call function with `internalRecfun`.
-/
def tagAsRecursiveCall (e : Expr) : Expr :=
 mkAnnotation `_solver.recursivecall e

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


/-- Return `true` if `f` is already in the recursive function cache. -/
def isVisitedRecFun (f : Expr) : TranslateEnvT Bool :=
 return (← get).optEnv.recFunCache.contains f

/-- Given `f x₁ ... xₙ`, return `true` only when one of the following conditions is satisfied:
     - `f := BEq.beq` with sort parameter in `relationalCompatibleTypes`
     - `f := LT.lt` with sort parameter in `relationalCompatibleTypes`
     - `f : LE.le` with sort parameter in `relationalCompatibleTypes`

In fact, we can't assume that `BEq.beq`, `LT.lt` and `LE.le` will properly be defined
for any user-defined types or parametric inductive types (e.g., List, Option, etc).
-/
def isOpaqueRelational (f : Name) (args : Array Expr) : TranslateEnvT Bool := do
  match f with
  | `BEq.beq
  | `LT.lt
  | `LE.le =>
      if args.size < 1 then throwEnvError "isOpaqueRelational: implicit arguments"
      return (isCompatibleRelationalType args[0]!)
  | _ => return false


/-- Return `true` if function name `f` is tagged as an opaque definition. -/
def isOpaqueFun (f : Name) (args: Array Expr) : TranslateEnvT Bool :=
  return (opaqueFuns.contains f || (← isOpaqueRelational f args))

/-- Same as `isOpaqueFun` expect that `f` is an expression. -/
def isOpaqueFunExpr (f : Expr) (args: Array Expr) : TranslateEnvT Bool :=
  match f with
  | Expr.const n _ => isOpaqueFun n args
  | _ => return false

/-- Return `true` if `f` corresponds to a theorem name. -/
def isTheorem (f : Name) : MetaM Bool := do
  match (← getConstInfo f) with
  | ConstantInfo.thmInfo _ => pure true
  | _ => pure false


/-- Return `true` if `f` corresponds to a recursive function. -/
def isRecursiveFun (f : Name) : MetaM Bool := do
  if (← isTheorem f) then return false
  isRecursiveDefinition f

/-- Return `Bool` type and cache result. -/
def mkBoolType : TranslateEnvT Expr := mkExpr (mkConst ``Bool)

/-- Return `true` boolean constructor and cache result. -/
def mkBoolTrue : TranslateEnvT Expr := mkExpr (mkConst ``true)

/-- Return `false` boolean constructor and cache result. -/
def mkBoolFalse : TranslateEnvT Expr := mkExpr (mkConst ``false)

/-- Given `b` a boolean value return the corresponding
    boolean constructor expression and cache result.
-/
def mkBoolLit (b : Bool) : TranslateEnvT Expr :=
  if b then mkBoolTrue else mkBoolFalse

/-- Return `not` boolean operator and cache result. -/
def mkBoolNotOp : TranslateEnvT Expr := mkExpr (mkConst ``not)

/-- Return `or` boolean operator and cache result. -/
def mkBoolOrOp : TranslateEnvT Expr := mkExpr (mkConst ``or)

/-- Return `and` boolean operator and cache result. -/
def mkBoolAndOp : TranslateEnvT Expr := mkExpr (mkConst ``and)

/-- Return `Prop` type and cache result. -/
def mkPropType : TranslateEnvT Expr := mkExpr (mkSort levelZero)

/-- Return `True` Prop and cache result. -/
def mkPropTrue : TranslateEnvT Expr := mkExpr (mkConst ``True)

/-- Return `False` Prop and cache result. -/
def mkPropFalse : TranslateEnvT Expr := mkExpr (mkConst ``False)

/-- Given `b` a boolean value return the corresponding
    propositional expression and cache result.
-/
def mkPropLit (b : Bool) : TranslateEnvT Expr :=
  if b then mkPropTrue else mkPropFalse

/-- Return `Not` operator and cache result. -/
def mkPropNotOp : TranslateEnvT Expr := mkExpr (mkConst ``Not)

/-- Return `Or` operator and cache result. -/
def mkPropOrOp : TranslateEnvT Expr := mkExpr (mkConst ``Or)

/-- Return `And` operator and cache result. -/
def mkPropAndOp : TranslateEnvT Expr := mkExpr (mkConst ``And)

/-- Return `BEq.beq` operator and cache result. -/
def mkBeqOp : TranslateEnvT Expr := mkExpr (mkConst ``BEq.beq [levelZero])

/-- Return `Eq` operator and cache result. -/
def mkEqOp : TranslateEnvT Expr := mkExpr (mkConst ``Eq [levelOne])

/-- Return `ite` operator and cache result. -/
def mkIteOp : TranslateEnvT Expr := mkExpr (mkConst ``ite [levelOne])

/-- Return `LE.le` operator and cache result. -/
def mkLeOp : TranslateEnvT Expr := mkExpr (mkConst ``LE.le [levelZero])

/-- Return `LT.lt` operator and cache result. -/
def mkLtOp : TranslateEnvT Expr := mkExpr (mkConst ``LT.lt [levelZero])

/-- Return `Decidable` const expression and cache result. -/
def mkDecidableConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable)

/-- Return `decide` const expression and cache result. -/
def mkDecideConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable.decide)

/-- Return `Inhabited` const expression and cache result. -/
def mkInhabitedConst : TranslateEnvT Expr := mkExpr (mkConst ``Inhabited [levelOne])

/-- Return `BEq` const expression and cache result. -/
def mkBEqConst : TranslateEnvT Expr := mkExpr (mkConst ``BEq [levelZero])

/-- Return `Nat` Type and cache result. -/
def mkNatType : TranslateEnvT Expr := mkExpr (mkConst ``Nat)

/-- Return `Nat.add` operator -/
def natAdd : Expr := mkConst ``Nat.add

/-- Create a `Nat.add` operator expression and cache result. -/
def mkNatAddOp : TranslateEnvT Expr :=  mkExpr natAdd

/-- Return `Nat.sub` operator -/
def natSub : Expr := mkConst ``Nat.sub

/-- Create a `Nat.sub` operator expression and cache result. -/
def mkNatSubOp : TranslateEnvT Expr := mkExpr natSub

/-- Return `Nat.mul` operator -/
def natMul : Expr := mkConst ``Nat.mul

/-- Create a `Nat.mul` operator expression and cache result. -/
def mkNatMulOp : TranslateEnvT Expr := mkExpr natMul

/-- Return `Nat.div` operator -/
def natDiv : Expr := mkConst ``Nat.div

/-- Creata a `Nat.div` operator expression and cache result. -/
def mkNatDivOp : TranslateEnvT Expr := mkExpr natDiv

/-- Return `Nat.mod` operator -/
def natMod : Expr := mkConst ``Nat.mod

/-- Create a `Nat.mod` operator expression and cache result. -/
def mkNatModOp : TranslateEnvT Expr := mkExpr natMod

/-- Return `Nat.pow` operator -/
def natPow : Expr := mkConst ``Nat.pow

/-- Create a `Nat.pow` operator expression and cache result. -/
def mkNatPowOp : TranslateEnvT Expr := mkExpr natPow

/-- Return `Nat.beq` operator -/
def natBeq : Expr := mkConst ``Nat.beq

/-- Create a `Nat.beq` operator expression and cache result. -/
def mkNatBeqOp : TranslateEnvT Expr := mkExpr natBeq

/-- Return `Nat.ble` operator -/
def natBle : Expr := mkConst ``Nat.ble

/-- Create a `Nat.ble` operator expression and cache result. -/
def mkNatBleOp : TranslateEnvT Expr := mkExpr natBle

/-- Return `Nat.blt` operator and cache result. -/
def mkNatBltOp : TranslateEnvT Expr := mkExpr (mkConst ``Nat.blt)

/-- Return `Int` Type and cache result. -/
def mkIntType : TranslateEnvT Expr := mkExpr (mkConst ``Int)

/-- Return `Int.add` operator and cache result. -/
def mkIntAddOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.add)

/-- Return `Int.mul` operator and cache result. -/
def mkIntMulOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.mul)

/-- Return `Int.pow` operator -/
def intPow : Expr := mkConst ``Int.pow

/-- Create an `Int.pow` operator expression and cache result. -/
def mkIntPowOp : TranslateEnvT Expr := mkExpr intPow

/-- Return `Int.ediv` operator -/
def intEDiv : Expr := mkConst ``Int.ediv

/-- Create an `Int.ediv` operator expression and cache result. -/
def mkIntEDivOp : TranslateEnvT Expr := mkExpr intEDiv

/-- Return `Int.emod` operator -/
def intEMod : Expr := mkConst ``Int.emod

/-- Create an `Int.emod` operator expression and cache result. -/
def mkIntEModOp : TranslateEnvT Expr := mkExpr intEMod

/-- Return `Int.fdiv` operator and cache result. -/
def mkIntFDivOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.fdiv)

/-- Return `Int.fmod` operator and cache result. -/
def mkIntFModOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.fmod)

/-- Return `Int.div` operator and cache result. -/
def mkIntDivOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.div)

/-- Return `Int.mod` operator and cache result. -/
def mkIntModOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.mod)

/-- Return `Int.neg` operator and cache result. -/
def mkIntNegOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.neg)

/-- Return `Int.ofNat` constructor and cache result. -/
def mkIntOfNat : TranslateEnvT Expr := mkExpr (mkConst ``Int.ofNat)

/-- Return `Int.toNat` operator and cache result. -/
def mkIntToNatOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.toNat)

/-- `mkAppExpr f #[a₀, ..., aₙ]` constructs the application `f a₀ ... aₙ` and cache the result.
-/
def mkAppExpr (f : Expr) (args: Array Expr) : TranslateEnvT Expr :=
  mkExpr (mkAppN f args)

/-- Return "==" Nat operator and cache result. -/
def mkNatEqOp : TranslateEnvT Expr := do
  let beqNat ← mkExpr (mkApp (← mkBeqOp) (← mkNatType))
  mkExpr (mkApp beqNat (← mkExpr (mkConst ``instBEqNat)))

/-- Return the `≤` Nat operator and cache result. -/
def mkNatLeOp : TranslateEnvT Expr := do
  let leExpr ← mkExpr (mkApp (← mkLeOp) (← mkNatType))
  mkExpr (mkApp leExpr (← mkExpr (mkConst ``instLENat)))

/-- Return the `<` Nat operator and cache result. -/
def mkNatLtOp : TranslateEnvT Expr := do
  let ltExpr ← mkExpr (mkApp (← mkLtOp) (← mkNatType))
  mkExpr (mkApp ltExpr (← mkExpr (mkConst ``instLTNat)))

/-- Return the `≤` Int operator and cache result. -/
def mkIntLeOp : TranslateEnvT Expr := do
  let leExpr ← mkExpr (mkApp (← mkLeOp) (← mkIntType))
  mkExpr (mkApp leExpr (← mkExpr (mkConst ``Int.instLEInt)))

/-- Return the `<` Int operator and cache result. -/
def mkIntLtOp : TranslateEnvT Expr := do
  let ltExpr ← mkExpr (mkApp (← mkLtOp) (← mkIntType))
  mkExpr (mkApp ltExpr (← mkExpr (mkConst ``Int.instLTInt)))


/-- `mkForallExpr n b` constructs `∀ n, b` and cache result.
-/
def mkForallExpr (n : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (← mkForallFVars #[n] b)

/-- `mkLambdaExpr n b` constructs `fun n => b` and cache result.
-/
def mkLambdaExpr (n : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (← mkLambdaFVars #[n] b)

/-- `mkNatLitExpr n` constructs `Expr.lit (Literal.natVal n)` and cache result.
-/
def mkNatLitExpr (n : Nat) : TranslateEnvT Expr :=
  mkExpr (mkRawNatLit n)

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
  | Int.ofNat n => mkExpr (mkApp (← mkIntOfNat) (← mkNatLitExpr n))
  | Int.negSucc n => mkExpr (mkApp (← mkExpr (mkConst ``Int.negSucc)) (← mkNatLitExpr n))

/-- `mkNatNegExpr n` constructs and cache the negation of a Nat literal expression, i.e.,
     Int.negSucc (Expr.lit (Literal.natVal (n - 1))`.
-/
def mkNatNegExpr (n : Nat) : TranslateEnvT Expr := do
  mkExpr (mkApp (← mkExpr (mkConst ``Int.negSucc)) (← mkNatLitExpr (n - 1)))


/-- `evalBinIntOp f n1 n2 perform the following:
      - let r := f n1 n2
      - construct int literal for `r`
      - cache result and return r
-/
def evalBinIntOp (f: Int -> Int -> Int) (n1 n2 : Int) : TranslateEnvT Expr :=
  mkIntLitExpr (f n1 n2)


/-- `mkDecidableConstraint e` constructs constraint [Decidable e] and cache the result.
-/
def mkDecidableConstraint (e : Expr) (cacheDecidableCst := true) : TranslateEnvT Expr := do
  let decideCstr := mkApp (← mkDecidableConst) e
  if cacheDecidableCst then mkExpr decideCstr else return decideCstr

/-- Return `d` if there is already a synthesize instance for `cstr` in the synthesize cache.
    Otherwise, the following actions are performed:
     - execute `LOption.some d ← trySynthInstance cstr`
     - add cstr := d to synthesize cache
     - return d
    Return `none` when `trySynthInstance` does not return `LOption.some`
-/
def trySynthConstraintInstance? (cstr : Expr) : TranslateEnvT (Option Expr) := do
  let env ← get
  match env.optEnv.synthInstanceCache.find? cstr with
  | some d => return d
  | none => do
     let LOption.some d ← trySynthInstance cstr | return none
     updateSynthCache cstr d
     return d

/-- Try to find an instance for `[Decidable e]`. -/
def trySynthDecidableInstance? (e : Expr) (cacheDecidableCst := true) : TranslateEnvT (Option Expr) := do
  let dCstr ← mkDecidableConstraint e cacheDecidableCst
  trySynthConstraintInstance? dCstr

/-- Same as `trySynthDecidableInstance` but throws an error when a decidable instance cannot be found. -/
def synthDecidableInstance! (e : Expr) : TranslateEnvT Expr := do
  let some d ← trySynthDecidableInstance? e
    | throwEnvError f!"synthesize instance for [Decidable {reprStr e}] cannot be found"
  return d


/-- Return `true` only when an instance for `[Inhabited n]` can be found. -/
def hasInhabitedInstance (n : Expr) : TranslateEnvT Bool := do
  let inhCstr ← mkExpr (mkApp (← mkInhabitedConst) n)
  let some _d ← trySynthConstraintInstance? inhCstr | return false
  return true


/-- Try to find an instance for `[BEq e]`.
    An error is triggered if no instance cannot be found.
-/
def synthBEqInstance! (e : Expr) : TranslateEnvT Expr := do
  let beqCstr ← mkExpr (mkApp (← mkBEqConst) e)
  let some d ← trySynthConstraintInstance? beqCstr
    | throwEnvError f!"synthesize instance for [BEq {reprStr e}] cannot be found"
  return d

/-- Return "==" operator for the given type `t`.
    An error is triggered when no BEq instance can be found for `t`.
-/
def mkTypeBeqOp (t : Expr) : TranslateEnvT Expr := do
  let beqType ← mkExpr (mkApp (← mkBeqOp) t)
  mkExpr (mkApp beqType (← synthBEqInstance! t))


/-- Return `b` if `a := b` is already in the weak head cache.
    Otherwise, the following actions are performed:
      - execute `b ← whnf a`
      - update cache with `a := b`
      - return `b'`
-/
def whnfExpr (a : Expr) : TranslateEnvT Expr := do
  let env ← get
  match env.optEnv.whnfCache.find? a with
  | some b => return b
  | none => do
     let b ← withReducible $ whnf a
     let optEnv := {env.optEnv with whnfCache := env.optEnv.whnfCache.insert a b}
     set {env with optEnv := optEnv}
     return b

/-- Given a `f : Expr.const n l` a function name expression,
    return `true` if `f` has at least one implicit argument.
-/
def hasImplicitArgs (f : Expr) : MetaM Bool := do
  let fInfo ← getFunInfo f
  for i in [:fInfo.paramInfo.size] do
    if !fInfo.paramInfo[i]!.isExplicit then return true
  return false


/-- Return the body in a sequence of forall / lambda. -/
def getForallLambdaBody (e : Expr) : Expr :=
 match e with
 | Expr.lam _ _ b _ => getForallLambdaBody b
 | Expr.forallE _ _ b .. => getForallLambdaBody b
 | _ => e

/-- Return `true` if `n` corresponds to a class or is an abbrevation to a class definition
    (e.g., DecidableEq, DecidableRel, etc).
-/
def isClassConstraint (n : Name) : MetaM Bool := do
 if isClass (← getEnv) n then return true
 let ConstantInfo.defnInfo defnInfo ← getConstInfo n | return false
 match (getForallLambdaBody defnInfo.value).getAppFn' with
 | Expr.const c _ => return (isClass (← getEnv) c)
 | _ => return false


/-- Return `true` if `e` corresponds to a class constraint expression (see function `isClassConstraint`).
-/
def isClassConstraintExpr (e : Expr) : MetaM Bool := do
 match e.getAppFn' with
 | Expr.const n _ => isClassConstraint n
 | _ => return false

/-- Return `true` if `f` corresponds to an inductive type or is an
    abbrevation to an inductive type.
-/
partial def isInductiveType (f : Name) (us : List Level) : MetaM Bool := do
 match (← getConstInfo f) with
 | ConstantInfo.inductInfo _ => return true
 | dInfo@(ConstantInfo.defnInfo _) =>
      -- check for type abbreviation
      let Expr.const n l := (← instantiateValueLevelParams dInfo us).getAppFn | return false
      isInductiveType n l
 | _ => return false

/-- Return `true` if `e` corresponds to an inductive type or is an abbreviation to an inductive type.
-/
def isInductiveTypeExpr (e : Expr) : MetaM Bool := do
 match e.getAppFn' with
 | Expr.const n l => isInductiveType n l
 | _ => return false


/-- Return all fvar expressions in `e`. The return array preserved dependencies between fvars,
    i.e., child fvars appear first.
-/
@[inline] partial def getFVarsInExpr (e : Expr) : MetaM (Array Expr) :=
 let rec @[specialize] visit (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  if !e.hasFVar then return acc else
    match e with
    | Expr.forallE _ d b _   => visit b (← visit d acc)
    | Expr.lam _ d b _       => visit d (← visit b acc)
    | Expr.mdata _ e         => visit e acc
    | Expr.letE _ t v b _    => visit t (← visit v (← visit b acc))
    | Expr.app f a           => visit f (← visit a acc)
    | Expr.proj _ _ e        => visit e acc
    | Expr.fvar v            => return (← visit (← v.getType) acc).push e
    | _                      => return acc
 visit e #[]

/-- Return `true` whenever `e` satisfies one of the following:
    - `e` is a sort type;
    - `e` is a const or variable of sort type;
    - `e` is an application that is not an instance of inductive datatype and
          that has at least one argument of sort type.
    NOTE: parameter skipInductiveCheck will be removed when specializing rec function.
    NOTE: The inductive datatype instance check will also be removed.
-/
partial def isGenericParam (e : Expr) (skipInductiveCheck := false) : TranslateEnvT Bool := do
 match e with
 | Expr.sort .zero -- prop type
 | Expr.lit ..
 | Expr.lam ..
 | Expr.proj ..
 | Expr.forallE ..
 | Expr.letE .. => return false
 | Expr.sort .. => return true
 | Expr.mdata _ e  => isGenericParam e
 | Expr.const n _ =>
     if (← isInstance n) then return false
     if isClass (← getEnv) n then return false
     if let ConstantInfo.inductInfo _ ← getConstInfo n then return false
     isGenericParam (← inferType e)
 | Expr.fvar v => isGenericParam (← v.getType)
 | Expr.app f arg =>
     if (!skipInductiveCheck) && !(← isClassConstraintExpr f) && (← isInductiveTypeExpr f) then return false
     isGenericParam arg
 | Expr.bvar _ => throwEnvError f!"isGenericParam: unexpected bound variable {reprStr e}"
 | Expr.mvar .. => throwEnvError f!"isGenericParam: unexpected meta variable {reprStr e}"

/-- Type to represent the parameters instantiating the implicit arguments for a given function.
    (see function `getImplicitParameters`)
-/

structure ImplicitParameters where
  /-- Corresponds to parameters that instantiate implicit arguments for a given function but
      that are still polymorphic, i.e., they satisfy predicate `isGenericParam`.
  -/
  genericArgs : Array Expr
  /-- Corresponds to parameters instantiating all the implicit arguments for a given function.
      NOTE: `genericArgs` is a subset of `instanceArgs`
  -/
  instanceArgs : Array Expr
 deriving Repr

/-- Given application `f x₀ ... xₙ`, perform the following:
     - When `∀ i ∈ [0..n], isExplicit xᵢ`,
           - return `{instanceArgs := #[], genericArgs := #[]}`
     - When `∃ i ∈ [0..n], ¬ isExplicit xᵢ`,
         let A := [x₀ ... xₙ]
         let instanceArgs := [A[i] | i ∈ [0..n] ∧ ¬ isExplicit A[i]]
         let genericArgs := [A[i] | i ∈ [0..n]  isGenericParam A[i] ∧ ¬ isExplicit A[i]]
           - return {instanceArgs, genericArgs}
    NOTE: It is assumed that all implicit arguments appear first in sequence `x₁ ... xₙ`.
    NOTE: It is also assumed that args does not contain any meta or bounded variables.
-/
def getImplicitParameters (f : Expr) (args : Array Expr) : TranslateEnvT ImplicitParameters := do
 let mut instanceArgs := #[]
 let mut genericArgs := #[]
 let fInfo ← getFunInfoNArgs f args.size
 for i in [:fInfo.paramInfo.size] do
   let aInfo := fInfo.paramInfo[i]!
   if !aInfo.isExplicit then
     instanceArgs := instanceArgs.push args[i]!
     if (← isGenericParam args[i]!) then
       genericArgs := genericArgs.push args[i]!
 return {instanceArgs, genericArgs}

/-- Given function `f` and its implicit arguments `params`, perform the following:
      - When params.instanceArgs.size == 0
          - return `f`
      - When params.instanceArgs.size > 0 ∧ params.genericArgs.size == 0
          - return `mkAppExpr f params.instanceArgs`
      - Otherwise:
          - return `mkLambdaFVars params.genericArgs (mkAppExpr f params.instanceArgs)`
    See function `getImplicitParameters`.
-/
def getInstApp (f : Expr) (params: ImplicitParameters) : TranslateEnvT Expr := do
 if params.instanceArgs.isEmpty then return f
 let auxApp ← mkAppExpr f params.instanceArgs
 if params.genericArgs.isEmpty then return auxApp
 mkExpr (← mkLambdaFVars params.genericArgs auxApp)


/-- Given application `f` a function name expression, `params` the implicit parameters (if any) for `f`
    (i.e., obtained via function `getImplicitParameters`), and `fbody` corresponding the recursive definition for `f`,
    perform the following actions:
      - Annotate the recurisve call in `fbody` with `_solver.recursivecall`
      - return `fbody` only when `params.instanceArgs.isEmpty`.
      - return `Expr.beta fbody params.instanceArgs` only when `params.genericArgs.isEmpty`
      - return `λ (α₁ : Type₁) → λ (αₘ : Typeₘ) → Expr.beta fbody params.instanceArgs`, s.t.:
          - α₁ : Type₁, ..., αₘ : Typeₘ = params.genericArgs
    An error is triggered when f is not a name expression.
-/
def generalizeRecCall (f : Expr) (params: ImplicitParameters) (fbody : Expr) : TranslateEnvT Expr := do
 let Expr.const n _ := f | throwEnvError f!"generalizeRecCall: name expression expected but got {reprStr f}"
 let fbody' := fbody.replace (replacePred n)
 if params.instanceArgs.isEmpty then return fbody'
 let betaExpr := Expr.beta fbody' params.instanceArgs
 if params.genericArgs.isEmpty then return betaExpr
 mkLambdaFVars params.genericArgs betaExpr

where
  replacePred (n : Name) (e : Expr) : Option Expr := do
   match e.getAppFn with
   | Expr.const rn _ =>
      if rn == n
      then some (tagAsRecursiveCall e)
      else none
   | _ => none


/-- Given `f` which is either a function name expression or a fully/partially instantiated polymorphic function (see `getInstApp`),
    and `fbody` corresponding to `f`'s definition, update the recursive instance cache (i.e., `recFunInstCache`),
-/
def updateRecFunInst (f : Expr) (fbody : Expr) : TranslateEnvT Unit := do
  let env ← get
  let optEnv := { env.optEnv with recFunInstCache := env.optEnv.recFunInstCache.insert f fbody }
  set {env with optEnv := optEnv}


/-- Given application `f x₁ ... xₙ`, return `some fbody` when `getInstApp f (← getImplicitParameters f args) := fbody` is in cache.
    Otherwise return `none`.
-/
def getRecFunInstBody? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let env ← get
  return (env.optEnv.recFunInstCache.find? (← getInstApp f (← getImplicitParameters f args)))


/-- Return `fₙ` if `body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ] := fₙ` is already
    in the recursive function map.
    Otherwise,
       - update recursive function map with `body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ] := f`
       - return `f`.
     where:
       - α₁ ... αₖ` correspond to the implicit arguments of `f` that are still polymorphic (if any).
       - `x₁ ... xₙ` correspond to the effective parameters of the recursive call (excluding implicit arguments).
    NOTE:
      - `f` is also removed from the visiting cache.
      - The polymorphic instance cache is updated with `f := body[mkAnnotation `_solver.recursivecall _'/_recFun α₁ ... αₖ x₁ ... xₙ]`
        (if required) for all cases. This is essential to avoid performing structural equivalence check again on an
        already handled recursive function.
    Assumes that:
      - `f` is either a function name expression or a fully/partially instantiated polymorphic function (see `getInstApp`)
      - any entry exists for each opaque recursive function in `recFunMap` before optimization is performed
        (see function `cacheOpaqueRecFun`).
-/
partial def storeRecFunDef (f : Expr) (body : Expr) : TranslateEnvT Expr := do
  -- remove from visiting cache
  uncacheFunName f
  let body' ← replaceRecCall body
  -- update polymorphic instance cache
  updateRecFunInst f body'
  let env ← get
  match env.optEnv.recFunMap.find? body' with
  | some fb => return fb
  | none =>
     let optEnv := {env.optEnv with recFunMap := env.optEnv.recFunMap.insert body' f}
     set {env with optEnv := optEnv}
     return f

where
  replacePred (params : ImplicitParameters) (recFun : Expr) (e : Expr) : Option Expr := do
   match toTaggedRecursiveCall? e with
   | some b =>
        let mut margs := b.getAppArgs
        -- replace any occurrence in args first
        for i in [:margs.size] do
           margs := margs.modify i (.replace (replacePred params recFun))
        some (mkAppN recFun (params.genericArgs ++ margs[params.instanceArgs.size : margs.size]))
   | _ => none

  replaceRecCall (fbody : Expr) : TranslateEnvT Expr := do
    lambdaTelescope fbody fun xs body => do
     let some recCall := body.find? isTaggedRecursiveCall
       | throwEnvError f!"storeRecFunDef: annotated recursive call expected in {reprStr body}"
     -- retrieve implicit arguments
     let params ← getImplicitParameters recCall.getAppFn' recCall.mdataExpr!.getAppArgs
     let body' := body.replace (replacePred params (← mkExpr (mkConst internalRecFun)))
     let e ← mkLambdaFVars xs body'
     return e

/-- Given `instApp` corresponding either to a function name expression or
    to a fully/partially instantiated polymorphic function (see function `getInstApp`),
    determine if `instApp` has already a mapping in `recFunInstCache`. If so then retrieve the correponding
    function application in `recFunMap`. Otherwise return `none`.
    An error is triggered if no corresponding entry can be found in `recFunMap`.
-/
def hasRecFunInst? (instApp : Expr) : TranslateEnvT (Option Expr) := do
  let env ← get
  match env.optEnv.recFunInstCache.find? instApp with
  | some fbody =>
     -- retrieve function application from recFunMap
     match env.optEnv.recFunMap.find? fbody with
     | none => throwEnvError f!"hasRecFunInst: expecting entry for {reprStr fbody} in recFunMap"
     | res => return res
  | none => return none

end Solver.Optimize
