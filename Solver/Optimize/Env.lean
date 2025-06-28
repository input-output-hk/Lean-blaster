import Lean
import Solver.Optimize.Opaque
import Solver.Smt.Term
import Solver.Command.Options

open Lean Meta Solver.Smt Solver.Options

namespace Solver.Optimize

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
deriving Inhabited

structure OptimizeOptions where
  /-- Flag to activate function normalization, e.g., `Nat.beq x y` to `BEq.beq Nat instBEqNat x y`.
      This flag is set to `false` when optimizing the recursive function body
      of an opaque function f ∈ recFunsToNormalize`.
  -/
  normalizeFunCall : Bool := true

  /-- Flag set to `true` only when optimizing function name `f` in expression `f x₁ ... xₙ`.
      This is to avoid applying optimization twice on the body of non-recursive functions.
  -/
  inFunApp : Bool := false

  /-- Keep track of the analysis Step reached for bmc and k-induction. -/
  mcDepth : Nat

  /-- Options passed to the #solve command. -/
  solverOptions : SolverOptions


instance : Inhabited OptimizeOptions where
  default := { normalizeFunCall := true, inFunApp := false, mcDepth := 0, solverOptions := default }

inductive MatchEntry where
  | EqPattern ( altArgs : Array Lean.Expr)
    /-- instanitated alternative arguments for current match pattern when discriminator matches pattern -/
  | NotEqPattern
   /-- Constructor used when discriminator does not match current pattern in match context -/

abbrev HypothesisMap := Std.HashMap Lean.Expr (Option Lean.Expr)
abbrev RewriteCacheMap := Std.HashMap Lean.Expr Lean.Expr
abbrev MatchEntryMap := Std.HashMap Lean.Expr MatchEntry -- with key corresponding to a match pattern
abbrev MatchContextMap := Std.HashMap Lean.Expr MatchEntryMap  -- with key corresponding to a match discriminator

/-- Type defining the memoization cache for internally demanding functions. -/
structure MemoizeEnv where
  /-- Cache memoizing the isRecursiveFun result -/
  isRecFunCache : Std.HashMap Lean.Name Bool

  /-- Cache memoizing the isInstance result -/
  isInstanceCache : Std.HashMap Lean.Name Bool

  /-- Cache memoizing the isClassConstraint result -/
  isClassCache : Std.HashMap Lean.Name Bool

  /-- Cache memoizing the isInductiveType result -/
  isInductiveCache : Std.HashMap Lean.Name Bool

  /-- Cache memoizing the isResolvableType result -/
  isResolvableCache : Std.HashMap Lean.Expr Bool

  /-- Cache memoizing the getMatcherRecInfo? result -/
  getMatcherCache : Std.HashMap Lean.Name (Option MatcherInfo)

  /-- Cache memoizing the getConstInfo result -/
  getConstInfoCache : Std.HashMap Lean.Name ConstantInfo

instance : Inhabited MemoizeEnv where
  default :=
  { isRecFunCache := Std.HashMap.emptyWithCapacity,
    isInstanceCache := Std.HashMap.emptyWithCapacity,
    isClassCache := Std.HashMap.emptyWithCapacity,
    isInductiveCache := Std.HashMap.emptyWithCapacity,
    isResolvableCache := Std.HashMap.emptyWithCapacity,
    getMatcherCache := Std.HashMap.emptyWithCapacity
    getConstInfoCache := Std.HashMap.emptyWithCapacity
  }

/-- Type defining the environment used when optimizing a lean theorem. -/
structure OptimizeEnv where
  /-- Cache memoizing the normalization and rewriting performed on the lean theorem according
      to a given context.
  -/
  globalRewriteCache : RewriteCacheMap

  /- Same cache as globalRewriteCache but is used only within a specific hypothesis context.
     (see functions `withOptimizeEnvCache` and `withHypothesis`).
  -/
  localRewriteCache : RewriteCacheMap

  /-- Cache memoizing synthesized instances for Decidable/Inhabited/LawfulBEq constraint. -/
  synthInstanceCache : Std.HashMap Lean.Expr (Option Lean.Expr)

  /-- Cache memoizing the whnf result. -/
  whnfCache : Std.HashMap Lean.Expr (Option Lean.Expr)

  /-- Cache memoizing type for a match application of the form
       `f.match.n [p₁, ..., pₙ, d₁, ..., dₖ,, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`, s.t.:
      An entry in this map is expected to be of the form `Type(f.match.n [p₁, ..., pₙ])` := fun.match.n p₁ ... pₙ`
      where, `p₁, ..., pₙ` correspond to the arguments instantiating polymorphic params.
      This is used to determine equivalence between match functions (see function `structEqMatch?`).
  -/
  matchCache: Std.HashMap Lean.Expr Lean.Expr

  /-- Cache memoizing instances of recursive functions.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := fdef`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic parameters of `f` (if any).
        - fdef: correspond to the recursive function body.
      TODO: UPDATE SPEC
  -/
  recFunInstCache : Std.HashMap Lean.Expr Lean.Expr

  /-- Cache keeping track of visited recursive function.
      Note that we here keep track of each instantiated polymorphic function.
  -/
  recFunCache: Std.HashSet Lean.Expr

  /-- Map to keep the normalized definition for each recursive function,
      which is also used to determine structural equivalence between functions
      (see function `storeRecFunDef`).
  -/
  recFunMap: Std.HashMap Lean.Expr Lean.Expr

  /-- Map keeping track of hypotheses introduced by implications.
      Given an implication of the form `h : a → b`, the following entries are introduced in this map:
       - `a := some h` ∈ hypsInContext
       - When `a := e₁ ∧ ... ∧ eₙ`
          - ∀ i ∈ [1..n], e₁ := none ∈ hypsInContext
      The Map is populated only when Type(a) = Prop.
      The updated Map is considered only when optimizing `b`, which may also be an implication.
      Keeping FVar expression `h` is necessary, especially when `h` is referenced in `b`.
      (see `addHypotheses` function and `optimizeForall` rule).
  -/
  hypsInContext : HypothesisMap

  /-- Map keeping track of match patterns when optimizing a match rhs.
      Given a match expression of the form:
        match₁ e₁, ..., eₙ with
        | p₍₁₎₍₁₎, ..., p₍₁₎₍ₙ₎ => t₁ x₁ ... xₙ
          ...
        | p₍ₘ₎₍₁₎, ..., p₍ₘ₎₍ₙ₎ => tₘ x₁ ... xₙ
      The following entries are introduced in this map context for each tᵢ:
        -  ∀ j ∈ [1..n], p₍ᵢ₎₍ⱼ₎ = eⱼ := (← retrieveAltsArgs #[p₍ᵢ₎₍ⱼ₎]).altArgs ∈ matchInContext
      (see `optimizeMatchAlt` function).

      NOTE: The updated Map context is considered only when optimizing each `tᵢ`.
  -/
  matchInContext : MatchContextMap

  /-- Memoization maps (see not on MemoizeEnv) -/
  memCache : MemoizeEnv

  /-- Optimization options (see note on OptimizeOptions) -/
  options : OptimizeOptions


instance : Inhabited OptimizeEnv where
  default :=
   { globalRewriteCache := Std.HashMap.emptyWithCapacity,
     localRewriteCache := Std.HashMap.emptyWithCapacity,
     synthInstanceCache := Std.HashMap.emptyWithCapacity,
     whnfCache := Std.HashMap.emptyWithCapacity,
     matchCache := Std.HashMap.emptyWithCapacity,
     recFunInstCache := Std.HashMap.emptyWithCapacity,
     recFunCache := Std.HashSet.emptyWithCapacity,
     recFunMap := Std.HashMap.emptyWithCapacity,
     hypsInContext := Std.HashMap.emptyWithCapacity,
     matchInContext := Std.HashMap.emptyWithCapacity,
     memCache := default,
     options := default,
   }


structure TranslateOptions where
  /-- Flag set when universe @Type has already been declared Smt instance. -/
  typeUniverse : Bool := false

  /-- This flag is set to `true` only when translating recursive function definition. -/
  inFunRecDefinition : Bool := false

  /-- Set keeping track of all variables in matched terms, including named patterns.
      This set is provided only when translating matched terms and match rhs.
  -/
  inPatternMatching : Std.HashSet FVarId

instance : Inhabited TranslateOptions where
  default := {typeUniverse := false, inFunRecDefinition := false, inPatternMatching := .emptyWithCapacity}


/-- Type defining the environment used when translating to Smt-Lib. -/
structure SmtEnv where
  /-- Cache memoizing the translation to Smt-Lib term. -/
  translateCache : Std.HashMap Lean.Expr SmtTerm

  /-- Smt-Lib commands emitted to the backend solver. -/
  smtCommands : Array SmtCommand

  /-- Backend solver process. -/
  smtProc : Option (IO.Process.Child ⟨.piped, .piped, .piped⟩)

  /-- Cache keeping track of visited inductive datatype during translation. -/
  indTypeVisited : Std.HashSet Lean.Name

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
     See note on `IndTypeDeclaration`.
  -/
  indTypeInstCache : Std.HashMap Lean.Expr IndTypeDeclaration

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
  funInstCache : Std.HashMap Lean.Expr SmtQualifiedIdent

  /-- Cache keeping track of sort that have already been declared. -/
  sortCache : Std.HashMap FVarId SmtSymbol

  /-- Set keeping track of all translated fvars. (see function fvarIdToSmtSymbol)  -/
  fvarsCache : Std.HashMap FVarId Nat

  /-- Set keeping track of quantified fvars. This is essential
      to detect globally declared variables. -/
  quantifiedFVars : Std.HashSet FVarId

  /-- Hash Map keeping track of globally declared variables and the ones in
      the top level forall quantifier.
      This set is used exclusively when retrieving counterexample after a `sat` result
      is obtained from the backend smt solver.
  -/
  topLevelVars : Std.HashMap SmtSymbol Lean.Name

  /-- Cache memoizing the string representation for an Smt Symbol -/
  symbolStrCache : Std.HashMap SmtSymbol String

  /-- Translation options (see note on TranslateOptions) -/
  options: TranslateOptions

instance : Inhabited SmtEnv where
  default :=
   { translateCache := Std.HashMap.emptyWithCapacity,
     smtCommands := Array.mkEmpty 1023,
     smtProc := default,
     indTypeVisited := Std.HashSet.emptyWithCapacity,
     indTypeInstCache := Std.HashMap.emptyWithCapacity,
     funInstCache := Std.HashMap.emptyWithCapacity,
     sortCache := Std.HashMap.emptyWithCapacity,
     fvarsCache := Std.HashMap.emptyWithCapacity,
     quantifiedFVars := Std.HashSet.emptyWithCapacity,
     topLevelVars := Std.HashMap.emptyWithCapacity,
     symbolStrCache := Std.HashMap.emptyWithCapacity,
     options := default
   }


/-- list of recursive functions to be normalized (see note in `OptimizeOptions`). -/
def recFunsToNormalize : NameHashSet :=
  List.foldr (fun c s => s.insert c) Std.HashSet.emptyWithCapacity
  [ ``Nat.beq,
    ``Nat.ble
  ]

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

def throwEnvError (msg : MessageData) : TranslateEnvT α := do
  if let some p := (← get).smtEnv.smtProc then
    p.kill
    discard $ p.wait
  throwError msg

def getAppFnWithArgsAux : Expr → Array Expr → Nat → (Expr × Array Expr)
  | Expr.app f a, as, i => getAppFnWithArgsAux f (as.set! i a) (i-1)
  | f,       as, _ => (f, as)

/-- Return a function and its arguments -/
@[inline] def getAppFnWithArgs (e : Expr) : (Expr × Array Expr) :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppFnWithArgsAux e (Array.replicate nargs dummy) (nargs-1)

/-- Return `true` if `op1` and `op2` are physically equivalent, i.e., points to same memory address.
-/
@[inline] private unsafe def exprEqUnsafe (op1 : Expr) (op2 : Expr) : MetaM Bool :=
  pure (ptrEq op1 op2)

/-- Safe implementation of physically equivalence for Expr.
-/
@[implemented_by exprEqUnsafe]
def exprEq (op1 : Expr) (op2 : Expr) : MetaM Bool := isDefEqGuarded op1 op2

/-- set optimize option `normalizeFunCall` to `b`. -/
def setNormalizeFunCall (b : Bool) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.options.normalizeFunCall := b })

/-- Perform the following actions:
     - set `normalizeFunCall` to `false`
     - execute `f`
     - set `normalizeFunCall` to `true`
-/
@[always_inline, inline]
def withOptimizeRecBody (f: TranslateEnvT Expr) : TranslateEnvT Expr := do
  setNormalizeFunCall false
  let e ← f
  setNormalizeFunCall true
  return e

/-- set optimize option `inFunApp` to `b`. -/
def setInFunApp (b : Bool) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.options.inFunApp := b })

/-- Perform the following actions:
     - set `inFunApp` to `true`
     - execute `f`
     - set `inFunApp` to `false`
-/
@[always_inline, inline]
def withInFunApp (f: TranslateEnvT Expr) : TranslateEnvT Expr := do
  setInFunApp true
  let e ← f
  setInFunApp false
  return e

@[always_inline, inline]
def updateHypothesis (h : HypothesisMap) (localCache : RewriteCacheMap) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.hypsInContext := h, optEnv.localRewriteCache := localCache})

@[always_inline, inline]
def updateMatchContext (h : MatchContextMap) (localCache : RewriteCacheMap) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.matchInContext := h, optEnv.localRewriteCache := localCache})


/-- Perform the following actions:
     let h := (← get).optEnv.options.hypsInContext
      - When Type(e) = Prop:
         - let h' := h ∪ [ e := fvar | ¬ ∃ e := some v ∈ h ] ∪ [ e₁ := none | i ∈ [1..n], e := e₁ ∧ ... ∧ eₙ ]
         - return (h' ≠ h, h')
     Otherwise:
       - return (false, h)
-/
@[inline] partial def addHypotheses
  (e : Expr) (fvar : Option Expr) : TranslateEnvT (Bool × HypothesisMap) := do
  let hyps := (← get).optEnv.hypsInContext
  if (← isProp e) then
    return (visit [e] (updateMap (false, hyps) e fvar))
  else return (false, hyps)

  where
    updateMap
      (h : Bool × HypothesisMap) (e : Expr)
      (fvar : Option Expr) : Bool × HypothesisMap :=
        match h.2.get? e with
        | none => (true, h.2.insert e fvar)
        | some none =>
            if Option.isNone fvar
            then h
            else (true, h.2.insert e fvar)
        | some (some _) => h

    visit (es : List Expr) (h : Bool × HypothesisMap) : Bool × HypothesisMap :=
      match es with
      | [] => h
      | e :: xs =>
        match (e.and?) with
        | some (a, b) =>
             visit (a :: b :: xs) ((updateMap (updateMap h a none) b none))
        | none => visit xs h


/-- Perform the following actions:
     let prev_env ← get
     - When h.1 (i.e., new entries added in `hypsInContext` (see function `addHypotheses`))
        - set `hypsInContext` to `h.2`
        - set `localRewriteCache` to empty
        - execute `f`
        - reset `hypsInContext` to `prev_env.optEnv.hypsInContext`
        - reset `localRewriteCache` to `prev_env.optEnv.localRewriteCache`
     - Otherwise:
         - execute `f`
    Assume that `h` is obtained using `addHypotheses`.
-/
@[always_inline, inline]
def withHypothesis (h : Bool × HypothesisMap) (f : TranslateEnvT α) : TranslateEnvT α := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, hypsInContext, _, _, _⟩⟩ ← get
  if h.1 then updateHypothesis h.2 Std.HashMap.emptyWithCapacity
  try
    f
  finally
    if h.1 then updateHypothesis hypsInContext localRewriteCache

/-- Perform the following actions:
     let prev_env ← get
     - set `matchInContext` to `h`
     - set `localRewriteCache` to empty
     - execute `f`
     - reset `matchInContext` to `prev_env.optEnv.matchInContext`
     - reset `localRewriteCache` to `prev_env.optEnv.localRewriteCache`
    Assume that `h` is populated as described by `optimizeMatchAlt`.
-/
@[always_inline, inline]
def withMatchContext (h : MatchContextMap) (f : TranslateEnvT α) : TranslateEnvT α := do
  let ⟨_, ⟨_, localRewriteCache, _, _, _, _, _, _, _, matchInContext, _, _⟩⟩ ← get
  updateMatchContext h Std.HashMap.emptyWithCapacity
  try
    f
  finally
    updateMatchContext matchInContext localRewriteCache


/-- set optimize option `inFunRecDefinition` to `b`. -/
def setInFunRecDefinition (b : Bool) : TranslateEnvT Unit := do
  modify (fun env => { env with smtEnv.options.inFunRecDefinition := b })

/-- Perform the following actions:
     - set `inFunRecDefinition` to `true`
     - execute `f`
     - set `inFunRecDefinition` to `false`
-/
@[always_inline, inline]
def withTranslateRecBody (f: TranslateEnvT α) : TranslateEnvT α := do
  setInFunRecDefinition true
  let t ← f
  setInFunRecDefinition false
  return t

/-- set optimize option `inPatternMatchin` to `h`. -/
def setInPatternMatching (h : Std.HashSet FVarId) : TranslateEnvT Unit := do
  modify (fun env => {env with smtEnv.options.inPatternMatching := h })

/-- Perform the following actions:
     - let s := (← get).smtEnv.options.inPatternMatching
     - set `inPatternMatching` to `s ∪ h`
     - execute `f`
     - set `inPatternMatching` to s
-/
@[always_inline, inline]
def withTranslatePattern (h : Std.HashSet FVarId) (f: TranslateEnvT α) : TranslateEnvT α := do
  let s := (← get).smtEnv.options.inPatternMatching
  setInPatternMatching (s.union h)
  let t ← f
  setInPatternMatching s
  return t

/-- Return `true` if optimize option `normalizeFunCall` is set to `true`. -/
def isOptimizeRecCall : TranslateEnvT Bool :=
  return (← get).optEnv.options.normalizeFunCall

/-- Return `true` if optimize option `inFunApp` is set to `true`. -/
def isInFunApp : TranslateEnvT Bool :=
  return (← get).optEnv.options.inFunApp

/-- Return `true` if optimize option `inFunRecDefinition` is set to `true`. -/
def isInRecFunDefinition : TranslateEnvT Bool :=
  return (← get).smtEnv.options.inFunRecDefinition

@[always_inline, inline]
def findGlobalCache (a : Expr) : TranslateEnvT (Option Expr) := do
 return (← get).optEnv.globalRewriteCache.get? a

@[always_inline, inline]
def findLocalCache (a : Expr) : TranslateEnvT (Option Expr) := do
 return (← get).optEnv.localRewriteCache.get? a

/-- Update global rewrite cache with `a := b`. -/
def updateGlobalRewriteCache (a : Expr) (b : Expr) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.globalRewriteCache := env.optEnv.globalRewriteCache.insert a b })

/-- Update local rewrite cache with `a := b`. -/
def updateLocalRewriteCache (a : Expr) (b : Expr) : TranslateEnvT Unit := do
  modify (fun env => { env with optEnv.localRewriteCache := env.optEnv.localRewriteCache.insert a b })

/-- Update synthesize decidable instance cache with `a := b`. -/
@[always_inline, inline]
def updateSynthCache (a : Expr) (b : Option Expr) : TranslateEnvT Unit := do
  modify (fun env => {env with optEnv.synthInstanceCache := env.optEnv.synthInstanceCache.insert a b})

/-- Return `b` if `a := b` is already in the synthesize cache
    Otherwise, the following actions are performed:
      - execute `b ← f ()`
      - update cache with `a := b`
      - return `b`
-/
@[always_inline, inline]
def withSynthInstanceCache (a : Expr) (f: Unit → TranslateEnvT (Option Expr)) : TranslateEnvT (Option Expr) := do
  match (← get).optEnv.synthInstanceCache.get? a with
  | some b => return b
  | none =>
      let b ← f ()
      updateSynthCache a b
      return b

/-- Return `a'` if `a := a'` is already in optimization cache.
    Otherwise, the following actions are performed:
      - add `a := a` in cache only when cacheResult is set to true
      - return `a`
-/
@[always_inline, inline]
def mkExpr (a : Expr) (cacheResult := true) : TranslateEnvT Expr := do
   match (← findGlobalCache a) with
   | some a' => return a'
   | none => do
       if cacheResult then updateGlobalRewriteCache a a
       return a

/-- Perform the following actions:
     - When `hypsInContext.size == 0 ∧ matchInContext == 0` (global context)
        - When `a := b ∈ globalRewriteCache`:
           - return `b`
        - Otherwise:
           - execute `b ← f()`
           - add entry `a := b` to `globalRewriteCache`
     - Otherwise:
         - When `a := b ∈ localRewriteCache`:
             - return `b`
         - Otherwise:
             - execute `b ← f()`
             - add entry `a := b` to `localRewriteCache`

 NOTE: A call to `mkExpr` must be done whenever any new Expr is created during normalization and rewriting.
 This is so to ensure maximum sharing of expression.
 Moreover, this also ensure that we can direcly use pointer equality during simplification
 instead of the costly isDefEq function.
-/
@[always_inline, inline]
def withOptimizeEnvCache (a : Expr) (f: Unit → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let isGlobal ← isGlobalContext
  match (← isInCache? a isGlobal) with
  | some b => return b
  | none =>
     let b ← f ()
     trace[Optimize.cacheExpr] "cacheExpr {← ppExpr a} ===> {← ppExpr b}"
     updateCache a b isGlobal
     return b

  where
    @[always_inline, inline]
    isInCache? (a : Expr) (isGlobal : Bool) : TranslateEnvT (Option Expr) := do
      if isGlobal
      then findGlobalCache a
      else findLocalCache a

    @[always_inline, inline]
    updateCache (a : Expr) (b : Expr) (isGlobal : Bool) : TranslateEnvT Unit :=
      if isGlobal
      then updateGlobalRewriteCache a b
      else updateLocalRewriteCache a b

    @[always_inline, inline]
    isGlobalContext : TranslateEnvT Bool := do
      let ⟨_, ⟨_, _, _, _, _, _, _, _, hypsInContext, matchInContext, _, _⟩⟩ ← get
      return hypsInContext.size == 0 && matchInContext.size == 0

/-- Add an instance recursive application (see function `getInstApp`) to
    the visited recursive function cache.
-/
def cacheFunName (f : Expr) : TranslateEnvT Unit := do
 modify (fun env => {env with optEnv.recFunCache := env.optEnv.recFunCache.insert f})

/-- Remove an instance recursive application (see function `getInstApp`) from
    the visited recursive function cache.
-/
def uncacheFunName (f : Expr) : TranslateEnvT Unit := do
 modify (fun env => { env with optEnv.recFunCache := env.optEnv.recFunCache.erase f})


/-- Internal generalized rec fun const to be used for in normalized recursive
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

/-- Same as the default `getConstInfo` but cache result. -/
def getConstEnvInfo (n : Name) : TranslateEnvT ConstantInfo := do
  match (← get).optEnv.memCache.getConstInfoCache.get? n with
  | some info => return info
  | none =>
      let info ← getConstInfo n
      modify (fun env => { env with
                               optEnv.memCache.getConstInfoCache :=
                               env.optEnv.memCache.getConstInfoCache.insert n info })
      return info

/-- Return `true` if `f` corresponds to a theorem name. -/
def isTheorem (f : Name) : TranslateEnvT Bool := do
  match (← getConstEnvInfo f) with
  | ConstantInfo.thmInfo _ => pure true
  | _ => pure false


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

/-- Return `dite` operator and cache result. -/
def mkDIteOp : TranslateEnvT Expr := mkExpr (mkConst ``dite [levelOne])

/-- Return `LE.le` operator and cache result. -/
def mkLeOp : TranslateEnvT Expr := mkExpr (mkConst ``LE.le [levelZero])

/-- Return `LE` const expression and cache result. -/
def mkLEConst : TranslateEnvT Expr := mkExpr (mkConst ``LE [levelZero])

/-- Return `LT.lt` operator and cache result. -/
def mkLtOp : TranslateEnvT Expr := mkExpr (mkConst ``LT.lt [levelZero])

/-- Return `LT` const expression and cache result. -/
def mkLTConst : TranslateEnvT Expr := mkExpr (mkConst ``LT [levelZero])

/-- Return `Decidable` const expression and cache result. -/
def mkDecidableConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable)

/-- Return `Decidable` const expression and cache result. -/
def mkDecidableEqConst : TranslateEnvT Expr := mkExpr (mkConst ``DecidableEq)

/-- Return `decide` const expression and cache result. -/
def mkDecideConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable.decide)

/-- Return `Inhabited` const expression and cache result. -/
def mkInhabitedConst : TranslateEnvT Expr := mkExpr (mkConst ``Inhabited [levelOne])

/-- Return `BEq` const expression and cache result. -/
def mkBEqConst : TranslateEnvT Expr := mkExpr (mkConst ``BEq [levelZero])

/-- Return `LawfulBEq` const expression and cache result. -/
def mkLawfulBEqConst : TranslateEnvT Expr := mkExpr (mkConst ``LawfulBEq [levelZero])

/-- Return `instBEqOfDecidableEq` const expression and cache result. -/
def mkInstBEqOfDecidableEq : TranslateEnvT Expr := mkExpr (mkConst ``instBEqOfDecidableEq [levelZero])

/-- Return `instDecidableEqNat` const expression and cache result. -/
def mkInstDecidableEqNat : TranslateEnvT Expr := mkExpr (mkConst ``instDecidableEqNat)

/-- Return `True.intro` const expression and cache result. -/
def mkTrueIntro : TranslateEnvT Expr := mkExpr (mkConst ``True.intro)

/-- Return `not_false` const expression and cache result. -/
def mkNotFalse : TranslateEnvT Expr := mkExpr (mkConst ``not_false)

/-- Return `of_decide_eq_true` const expression and cache result. -/
def mkOfDecideEqTrue : TranslateEnvT Expr := mkExpr (mkConst ``of_decide_eq_true)

/-- Return `of_decide_eq_false` const expression and cache result. -/
def mkOfDecideEqFalse : TranslateEnvT Expr := mkExpr (mkConst ``of_decide_eq_false)

/-- Return `Eq.refl` const expression and cache result. -/
def mkEqRefl : TranslateEnvT Expr := mkExpr (mkConst ``Eq.refl [levelOne])

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

/-- Return `Int.tdiv` operator and cache result. -/
def mkIntTDivOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.tdiv)

/-- Return `Int.tmod` operator and cache result. -/
def mkIntTModOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.tmod)

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
def mkNatBEqOp : TranslateEnvT Expr := do
  let decEq ← mkExpr (mkAppN (← mkInstBEqOfDecidableEq) #[← mkNatType, ← mkInstDecidableEqNat])
  mkExpr (mkAppN (← mkBeqOp) #[← mkNatType, decEq])

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

/-- `mkNatLitExpr n` constructs `Expr.lit (Literal.natVal n)` and cache result. -/
def mkNatLitExpr (n : Nat) : TranslateEnvT Expr :=
  mkExpr (mkRawNatLit n)

/-- Returns Nat `a = b` and cache result. -/
def mkNatEqExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr $ mkApp3 (← mkEqOp) (← mkNatType) a b

/-- Returns Nat `a < b` and cache result. -/
def mkNatLtExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (mkApp2 (← mkNatLtOp) a b)

/-- Returns Nat `a ≤ b` and cache result. -/
def mkNatLeExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (mkApp2 (← mkNatLeOp) a b)

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

/-- Returns Int `a = b` and cache result. -/
def mkIntEqExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr $ mkApp3 (← mkEqOp) (← mkIntType) a b

/-- Returns Int `a < b` and cache result. -/
def mkIntLtExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (mkApp2 (← mkIntLtOp) a b)

/-- Returns Int `a ≤ b` and cache result. -/
def mkIntLeExpr (a : Expr) (b : Expr) : TranslateEnvT Expr := do
  mkExpr (mkApp2 (← mkIntLeOp) a b)

/-- `mkNatNegExpr n` constructs and cache the negation of a Nat literal expression, i.e.,
     Int.negSucc (Expr.lit (Literal.natVal (n - 1))`.
-/
def mkNatNegExpr (n : Nat) : TranslateEnvT Expr := do
  mkExpr (mkApp (← mkExpr (mkConst ``Int.negSucc)) (← mkNatLitExpr (n - 1)))

/- Given `e` of type `Bool`, return `b = e` and cache result.  -/
def mkEqBool (e : Expr) (b : Bool) : TranslateEnvT Expr := do
  mkExpr $ mkApp3 (← mkEqOp) (← mkBoolType) (← mkBoolLit b) e

/-- `evalBinIntOp f n1 n2 perform the following:
      - let r := f n1 n2
      - construct int literal for `r`
      - cache result and return r
-/
def evalBinIntOp (f: Int -> Int -> Int) (n1 n2 : Int) : TranslateEnvT Expr :=
  mkIntLitExpr (f n1 n2)

/-- `mkStrLitExpr s` constructs `Expr.lit (Literal.strVal s)` and cache result. -/
def mkStrLitExpr (s : String) : TranslateEnvT Expr :=
  mkExpr (mkStrLit s)

/-- `mkDecidableConstraint e` constructs constraint [Decidable e] and cache the result.
-/
def mkDecidableConstraint (e : Expr) (cacheDecidableCst := true) : TranslateEnvT Expr := do
  let decideCstr := mkApp (← mkDecidableConst) e
  if cacheDecidableCst then mkExpr decideCstr else return decideCstr

/-- Return `d` if there is already a synthesize instance for `cstr` in the synthesize cache.
    Otherwise, the following actions are performed:
     - When `LOption.some d ← trySynthInstance cstr`
         - add `cstr := some d` to synthesize cache
         - return `some d`
    - When `trySynthInstance` does not return `LOption.some`:
         - add `cstr := none` to synthesize cache
         - return `none`
-/
def trySynthConstraintInstance? (cstr : Expr) : TranslateEnvT (Option Expr) := do
  withSynthInstanceCache cstr $ fun _ =>
    try
      match (← withConfig (λ c => {c with iota := false, proj := .no}) $ trySynthInstance cstr) with
      | LOption.some d => return (some d)
      | _ => return none
    catch _ =>
      -- catch typeCheck error due to unfolding
      return none

/-- Try to find an instance for `[Decidable e]`. -/
def trySynthDecidableInstance? (e : Expr) (cacheDecidableCst := true) : TranslateEnvT (Option Expr) := do
  let dCstr ← mkDecidableConstraint e cacheDecidableCst
  trySynthConstraintInstance? dCstr

/-- Same as `trySynthDecidableInstance` but throws an error when a decidable instance cannot be found. -/
def synthDecidableInstance! (e : Expr) : TranslateEnvT Expr := do
  let some d ← trySynthDecidableInstance? e
    | throwEnvError f!"synthesize instance for [Decidable {reprStr e}] cannot be found"
  return d

/-- Same as `trySynthDecidableInstance` but cache and return the queried decidable
    constraint when no decidable instance cannot be found.
    In fact, after definitions have been unfolded, it can sometimes be the case
    that Lean can't infer the proper Decidable instance. In this case, we return the queried decidable
    instance.
-/
def synthDecidableWithNotFound! (e : Expr) : TranslateEnvT Expr := do
  match (← trySynthDecidableInstance? e) with
  | none =>
      let cstr ← mkDecidableConstraint e
      updateSynthCache cstr cstr
      return cstr
  | some d => return d

/-- Return `true` only when an instance for `[Inhabited n]` can be found.
    Assume that `n` is a name expression for an inductive datatype.
-/
def hasInhabitedInstance (n : Expr) : TranslateEnvT Bool := do
  let inhCstr ← mkExpr (mkApp (← mkInhabitedConst) n)
  let some _d ← trySynthConstraintInstance? inhCstr | return false
  return true


/-- Return `true` only when an instance for `[LawfulBEq t beqInst]` can be found. -/
def hasLawfulBEqInstance (t : Expr) (beqInst : Expr) : TranslateEnvT Bool := do
  let lawfulCstr ← mkExpr (mkApp2 (← mkLawfulBEqConst) t beqInst)
  let some _d ← trySynthConstraintInstance? lawfulCstr | return false
  return true


/-- Given an expression `c` and a boolean value `b`, perform the following:
     let d ← synthDecidableWithNotFound! c
      - When b is `true`:
         - return `of_decide_eq_true c d (Eq.refl true)`
      - Otherwise:
         - return `of_decide_eq_false c d (Eq.refl true)`
-/
def mkOfDecideEqProof (c : Expr) (b : Bool) : TranslateEnvT Expr := do
 let eqReflInst ← mkExpr (mkApp2 (← mkEqRefl) (← mkBoolType) (← mkBoolLit b))
 let d ← synthDecidableWithNotFound! c
 if b
 then mkExpr (mkApp3 (← mkOfDecideEqTrue) c d eqReflInst)
 else mkExpr (mkApp3 (← mkOfDecideEqFalse) c d eqReflInst)

/-- Given `f x₁ ... xₙ`, return `true` only when one of the following conditions is satisfied:
     - `f := BEq.beq` with sort parameter that has a `LawfulBEq` instance
     - `f := LT.lt` with sort parameter in `relationalCompatibleTypes`
     - `f : LE.le` with sort parameter in `relationalCompatibleTypes`

In fact, we can't assume that `BEq.beq`, `LT.lt` and `LE.le` will properly be defined
for any user-defined types or parametric inductive types (e.g., List, Option, etc).
-/
def isOpaqueRelational (f : Name) (args : Array Expr) : TranslateEnvT Bool := do
  match f with
  | `BEq.beq =>
      if args.size < 2 then throwEnvError "isOpaqueRelational: implicit arguments expected"
      hasLawfulBEqInstance args[0]! args[1]!
  | `LT.lt
  | `LE.le =>
      if args.size < 2 then throwEnvError "isOpaqueRelational: implicit arguments expected"
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


/-- Return `true` only when `f` is a class instance. -/
@[always_inline, inline]
def isInstanceClass (f : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isInstanceCache.get? f with
  | some b => return b
  | none =>
      let b ← isInstance f
      modify (fun env =>
               { env with
                     optEnv.memCache.isInstanceCache :=
                     env.optEnv.memCache.isInstanceCache.insert f b })
      return b

/-- Return `true` when `f` is neither a theorem nor a class instance and
    is tagged as a well-founded recursive definition.
-/
@[always_inline, inline]
def isRecursiveFun (f : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isRecFunCache.get? f with
  | some b => return b
  | none =>
    if (← (isTheorem f) <||> (isInstanceClass f))
    then
      updateIsRec f false
      return false
    else
     let b ← isRecursiveDefinition f
     updateIsRec f b
     return b

  where
    @[always_inline, inline]
    updateIsRec (f : Name) (b : Bool) : TranslateEnvT Unit :=
      modify (fun env =>
                { env with
                      optEnv.memCache.isRecFunCache :=
                      env.optEnv.memCache.isRecFunCache.insert f b })

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

/-- Helper function for isClassConstraint -/
private partial def isClassConstraintAux (n : Name) : TranslateEnvT Bool := do
 if isClass (← getEnv) n then return true
 else
   match (← getConstEnvInfo n) with
   | ConstantInfo.defnInfo defnInfo =>
       match (getForallLambdaBody defnInfo.value).getAppFn' with
       | Expr.const c _ => isClassConstraintAux c
       | _ => return false
   | _ => return false

/-- Return `true` if `n` corresponds to a class or is transitively an abbrevation
    to a class definition (e.g., DecidableEq, DecidableLT, DecidableRel, etc).
-/
@[always_inline, inline]
def isClassConstraint (n : Name) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isClassCache.get? n with
  | some b => return b
  | none =>
      let b ← isClassConstraintAux n
      modify (fun env => { env with
                               optEnv.memCache.isClassCache :=
                               env.optEnv.memCache.isClassCache.insert n b })
      return b

/-- Helper function for getMatcherRecInfo? -/
private def getMatcherRecInfoAux? (n : Name) (l : List Level) : TranslateEnvT (Option MatcherInfo) := do
 if let some r ← getMatcherInfo? n then return r
 if !(isCasesOnRecursor (← getEnv) n) then return none
 let indName := n.getPrefix
 let ConstantInfo.inductInfo info ← getConstEnvInfo indName | return none
 let mut altNumParams := #[]
 for ctor in info.ctors do
   let ConstantInfo.ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
   altNumParams := altNumParams.push ctorInfo.numFields
 return some { numParams := info.numParams,
               numDiscrs := info.numIndices + 1,
               altNumParams,
               uElimPos? := if info.levelParams.length == l.length then none else some 0
               discrInfos := Array.replicate (info.numIndices + 1) {}
             }

/-- Same as the default `getMatcherInfo` in the Lean library but also handles casesOn recursor application. -/
@[always_inline, inline]
def getMatcherRecInfo? (n : Name) (l : List Level) : TranslateEnvT (Option MatcherInfo) := do
 match (← get).optEnv.memCache.getMatcherCache.get? n with
 | some m => return m
 | none =>
     let m ← getMatcherRecInfoAux? n l
     modify (fun env => { env with
                               optEnv.memCache.getMatcherCache :=
                               env.optEnv.memCache.getMatcherCache.insert n m })
     return m

/-- Return `true` if `e` corresponds to a class constraint expression
    (see function `isClassConstraint`).
-/
@[always_inline, inline]
def isClassConstraintExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const n _ => isClassConstraint n
 | _ => return false

/-- Return `true` if `f` corresponds to an inductive type or is an
    abbrevation to an inductive type.
-/
private partial def isInductiveTypeAux (f : Name) (us : List Level) : TranslateEnvT Bool := do
 match (← getConstEnvInfo f) with
 | ConstantInfo.inductInfo _ => return true
 | dInfo@(ConstantInfo.defnInfo _) =>
    if dInfo.type.isProp
    then return false
    else
      -- check for type abbreviation
      if let Expr.const n l := (← instantiateValueLevelParams dInfo us).getAppFn
      then isInductiveTypeAux n l
      else return false
 | _ => return false

/-- Return `true` if `f` corresponds to an inductive type or is an
    abbrevation to an inductive type.
-/
@[always_inline, inline]
def isInductiveType (f : Name) (us : List Level) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isInductiveCache.get? f with
  | some b => return b
  | none =>
       let b ← isInductiveTypeAux f us
       modify (fun env => { env with
                                optEnv.memCache.isInductiveCache :=
                                env.optEnv.memCache.isInductiveCache.insert f b })
       return b

/-- Return `true` if `e` corresponds to an inductive type or is an abbreviation to an inductive type. -/
@[always_inline, inline]
def isInductiveTypeExpr (e : Expr) : TranslateEnvT Bool := do
 match e.getAppFn' with
 | Expr.const n l => isInductiveType n l
 | _ => return false

inductive ResolveTypeStack where
 | InitExpr (t : Expr) : ResolveTypeStack
 | ArgsExpr (f : Expr) (args : Array Expr) (idx : Nat) (stop : Nat) : ResolveTypeStack

/-- Return `true` is `t` is a potential resolvable type -/
private def isResolvableTypeAux (t : Expr) : TranslateEnvT Bool := do
  if (← isProp t) then return false
  match t.getAppFn' with
  | Expr.const n _ =>
       if (← isClassConstraint n) then return false
       if (← getConstEnvInfo n).isInductive then return false
       isType t
  | _ => isType t

/-- Return `true` is `t` is a potential resolvable type -/
def isResolvableType (t : Expr) : TranslateEnvT Bool := do
  match (← get).optEnv.memCache.isResolvableCache.get? t with
  | some b => return b
  | none =>
       let b ← isResolvableTypeAux t
       modify (fun env => { env with
                                optEnv.memCache.isResolvableCache :=
                                env.optEnv.memCache.isResolvableCache.insert t b })
       return b

/-- Given `t x₀ .. xₙ` a type expression, this function resolves type
    abbreviation by performing the following:
    - When `t := Expr.const n us ∧ `defnInfo(n) := d α₀ ... αₙ`:
       - return `resolveTypeAbbrev $ d (resolveTypeAbbrev x₀) ... (resolveTypeAbbrev xₙ)`
    - Otherwise
       - return `t (resolveTypeAbbrev x₀) ... (resolveTypeAbbrev xₙ)`
-/
private partial def resolveTypeAbbrevAux (s : List ResolveTypeStack) : TranslateEnvT Expr := do
  match s with
  | .InitExpr t :: xs =>
      let (f, args) := getAppFnWithArgs t
      match f with
      | Expr.const n us =>
         match (← getConstEnvInfo n) with
         | cinfo@(ConstantInfo.defnInfo _) =>
            let auxApp ← instantiateValueLevelParams cinfo us
            resolveTypeAbbrevAux ( .InitExpr (Expr.beta auxApp args) :: xs)
         | _ => resolveTypeAbbrevAux ( .ArgsExpr f args 0 args.size :: xs)
      | _ =>
         match xs with
         | [] => return t
         | .ArgsExpr f args idx stop :: xs =>
              resolveTypeAbbrevAux ( .ArgsExpr f (args.set! idx t) (idx + 1) stop :: xs )
         | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"
  | .ArgsExpr f args idx stop :: xs =>
       if idx ≥ stop then
         let t' := mkAppN f args
         match xs with
         | [] => return t'
         | .ArgsExpr f' args' idx' stop' :: ys' =>
               resolveTypeAbbrevAux ( .ArgsExpr f' (args'.set! idx' t') (idx' + 1) stop' :: ys' )
         | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"
       else resolveTypeAbbrevAux (.InitExpr args[idx]! :: s)
  | _ => throwEnvError "resolveTypeAbbrevAux: unreachable case !!!"


@[inline, always_inline] def resolveTypeAbbrev (t : Expr) : TranslateEnvT Expr :=
  resolveTypeAbbrevAux [.InitExpr t]

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
 | Expr.mdata _ e  => isGenericParam e skipInductiveCheck
 | Expr.const n _ =>
     -- resolve type abbreviation (if any)
     let t ← resolveTypeAbbrev e
     if !(← exprEq t e) then isGenericParam t skipInductiveCheck
     else
       if (← isInstanceClass n) then return false
       if (← isClassConstraint n) then return false
       if let ConstantInfo.inductInfo _ ← getConstEnvInfo n then return false
       isGenericParam (← inferType e) skipInductiveCheck
 | Expr.fvar v => isGenericParam (← v.getType) skipInductiveCheck
 | Expr.app f arg =>
     if (!skipInductiveCheck) && !(← isClassConstraintExpr f) && (← isInductiveTypeExpr f) then return false
     isGenericParam arg skipInductiveCheck
 | Expr.bvar _ => throwEnvError f!"isGenericParam: unexpected bound variable {reprStr e}"
 | Expr.mvar .. => throwEnvError f!"isGenericParam: unexpected meta variable {reprStr e}"

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

/-- Given application `f x₀ ... xₙ`, return the following sequence:
      let A := [x₀ ... xₙ]
      let instanceArgs := [ { implicitArg := A[i], isInstance := ¬ isExplicit A[i],
                              isGeneric := isGenericParam A[i], idxArg := i}
                            | i ∈ [0..n] ]
      return instanceArgs
    NOTE: It is also assumed that args does not contain any meta or bounded variables.
-/
def getImplicitParameters (f : Expr) (args : Array Expr) : TranslateEnvT ImplicitParameters := do
 let mut instanceParams := (#[] : ImplicitParameters)
 let fInfo ← getFunInfoNArgs f args.size
 for i in [:fInfo.paramInfo.size] do
   let aInfo := fInfo.paramInfo[i]!
   if !aInfo.isExplicit then
     let isGeneric ← isGenericParam args[i]!
     instanceParams := instanceParams.push {effectiveArg := args[i]!, isInstance := true, isGeneric}
   else
     instanceParams := instanceParams.push {effectiveArg := args[i]!, isInstance := false, isGeneric := false}
 return instanceParams


/-- Given `params` an implicit parameters info return a sequence of arguments satisfying the following:
     [ params[i].effectiveArgs | i ∈ [0..params.size-1] ∧ (params[i].isGeneric ∨ ¬ params[i].isInstance) ]
-/
@[inline] def getEffectiveParams (params : ImplicitParameters) : Array Expr :=
  Array.filterMap (λ p => if (p.isGeneric || !p.isInstance) then some p.effectiveArg else none) params


/-- Given a fun body `λ α₀ → ... λ αₙ → body` and `params` the implicit parameters info
    for the corresponding function, perform the following actions:
      - let A := [α₀, ..., αₙ]
      - let B := [ A[i] | i ∈ [0..n] ∧ (params[i].isGeneric ∨ ¬ params[i].isInstance) ]
      - let S := [ A[i] | i ∈ [0..n] ∧ ¬ params[i].isGeneric ∧ params[i].isInstance ]
      - let R := [ params[i] | i ∈ [0..n] ∧ ¬ params[i].isGeneric ∧ params[i].isInstance ]
      - let β₀, .., βₘ = B
      - return `λ β₀ → ... λ βₘ → body [S[0]/R[0]] ... [S[k]/R[k]]` with k = S.size-1

    Assume that params.size ≤ n
-/
partial def specializeLambda (fbody : Expr) (params : ImplicitParameters) : Expr :=
  let rec visit (idx : Nat) (stop : Nat) (e : Expr) (k : Expr → Expr) : Expr :=
    if idx ≥ stop then k e
    else
      match e with
      | Expr.lam n t b bi =>
         let p := params[idx]!
         if p.isGeneric || !p.isInstance then
           visit (idx + 1) stop b fun b' =>
             k (Expr.lam n t b' bi)
         else
           visit (idx + 1) stop (Expr.beta e #[p.effectiveArg]) k
      | _ => k e
  visit 0 (params.size) fbody (λ e => e)

/-- Given function `f` and `params` its implicit parameter info (see `getImplicitParameters`),
    perform the following:
     let instanceArgs := [ params[i] | i ∈ [0..params.size-1] ∧ params[i].isInstance ]
      - When instanceArgs.isEmpty
          - return `f`
      - Otherwise:
          - return `mkExpr $ specializeLambda (← etaExpand f) params
-/
def getInstApp (f : Expr) (params: ImplicitParameters) : TranslateEnvT Expr := do
 let instanceArgs := Array.filter (λ p => p.isInstance) params
 if instanceArgs.isEmpty then return f
 -- need to eta expand first to handle partially applied polymorphic functions
 mkExpr $ specializeLambda (← etaExpand f) params

/-- Given `f` a function name expression, `params` its implicit parameters info (see `getImplicitParameters`),
    and `fbody` corresponding the recursive definition for `f`, perform the following actions:
      - let fbody' be `fbody` in which the recurisve call is annotated with `_solver.recursivecall`
      - When ∀ i ∈ [0..params.size-1], ¬ params[i].isInstance:
          - return fbody'
      - Otherwise:
          - return specializeLambda fbody' params
    An error is triggered when `f` is not a name expression.
-/
partial def generalizeRecCall (f : Expr) (params: ImplicitParameters) (fbody : Expr) : TranslateEnvT Expr := do
 let Expr.const n _ := f | throwEnvError f!"generalizeRecCall: name expression expected but got {reprStr f}"
 let fbody' := fbody.replace (replacePred n)
 if !(params.any (λ p => p.isInstance)) then return fbody'
 return (specializeLambda fbody' params)

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
  modify (fun env => { env with optEnv.recFunInstCache := env.optEnv.recFunInstCache.insert f fbody })


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
      - an entry exists for each opaque recursive function in `recFunMap` before optimization is performed
        (see function `cacheOpaqueRecFun`).
-/
partial def storeRecFunDef (f : Expr) (params : ImplicitParameters) (body : Expr) : TranslateEnvT Expr := do
  let body' := body.replace (replacePred (← mkExpr (mkConst internalRecFun)))
  -- update polymorphic instance cache
  updateRecFunInst f body'
  match (← get).optEnv.recFunMap.get? body' with
  | some fb => return fb
  | none =>
     modify (fun env => { env with optEnv.recFunMap := env.optEnv.recFunMap.insert body' f})
     return f

where
  replacePred (recFun : Expr) (e : Expr) : Option Expr := do
   match toTaggedRecursiveCall? e with
   | some b =>
        let mut margs := b.getAppArgs
        -- replace any occurrence in args first
        for i in [:margs.size] do
           margs := margs.modify i (.replace (replacePred recFun))
        if params.isEmpty then
          -- case when function does not have any implicit parameters and is passed as argument (HOF)
          some (mkAppN recFun margs)
        else
          let mut effectiveArgs := #[]
          for i in [:margs.size] do
             if i < params.size
             then
               if params[i]!.isGeneric || !(params[i]!.isInstance)
               then effectiveArgs := effectiveArgs.push margs[i]!
             else effectiveArgs := effectiveArgs.push margs[i]! -- case when f is partially applied
          some (mkAppN recFun effectiveArgs)
   | _ => none

/-- Given `instApp` corresponding either to a function name expression or
    to a fully/partially instantiated polymorphic function (see function `getInstApp`),
    determine if `instApp` has already a mapping in `recFunInstCache`. If so then retrieve the corresponding
    function application in `recFunMap`. Otherwise return `none`.
    An error is triggered if no corresponding entry can be found in `recFunMap`.
-/
def hasRecFunInst? (instApp : Expr) : TranslateEnvT (Option Expr) := do
  let ⟨_, ⟨_,_,_,_,_,recFunInstCache,_,recFunMap,_, _,_,_⟩⟩ ← get
  match recFunInstCache.get? instApp with
  | some fbody =>
     -- retrieve function application from recFunMap
     match recFunMap.get? fbody with
     | none => throwEnvError f!"hasRecFunInst: expecting entry for {reprStr fbody} in recFunMap"
     | res => return res
  | none => return none


initialize
  registerTraceClass `Optimize.cacheExpr

end Solver.Optimize
