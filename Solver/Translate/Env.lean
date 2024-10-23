rimport Lean
import Solver.Translate.Utils

open Lean Meta

namespace Solver

/--
 Type defining the environment used when optimizing and
 translation a lean theorem to SMTLib
-/
structure TranslateEnv where
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
  /-- Cache memoizing instance of recursive functions.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := fdef`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic parameters of `f` (if any).
        - fdef: correspond to the recursive function body.
  -/
  recFunInstCache : HashMap Lean.Expr Lean.Expr
  /-- Cache keeping track of visited recursive function.
      Note that we here keep track of each instantiated ploymorphic function.
  -/
  recFunCache: HashSet Lean.Expr
  /-- Map to keep the normalized definition for each recursive function,
      which is also used to determine structural equivalence between functions
      (see function `storeRecFunDef`).
  -/
  recFunMap: HashMap Lean.Expr Lean.Expr
  /-- Same as recFunMap but is populated only when an opaque recursive function
      (e.g., `Int.add`, `Int.pow`, etc) definition matches a non-opaque recursive
      definition. If there is at least one entry in this map, rewriting is
      performed again until no entry is introduced in replayRecFunMap.
      (see function `storeRecFunDef`).
      The rewriting will restart from a new `TranslateEnv` that has been
      populated with the old one (see function `restartTranslateEnv`).
  -/
  replayRecFunMap: HashMap Lean.Expr Lean.Expr
 deriving Inhabited

abbrev TranslateEnvT := StateRefT TranslateEnv MetaM


/-- Update rewrite cache with `a := b`.
-/
def updateRewriteCache (a: Expr) (b: Expr) : TranslateEnvT Unit := do
  let env ← get
  set {env with rewriteCache := env.rewriteCache.insert a b }

/-- Update synthesize decidable instance cache with `a := b`.
-/
def updateSynthCache (a: Expr) (b: Expr) : TranslateEnvT Unit := do
  let env ← get
  set {env with synthInstanceCache := env.synthInstanceCache.insert a b }

/-- Return `a'` if `a := a'` is already in translation cache.
    Otherwise, the following actions are performed:
      - add `a := a` in cache only when cacheResult is set to true
      - return `a`
-/
def mkExpr (a : Expr) (cacheResult := true) : TranslateEnvT Expr := do
  let env ← get
  match env.rewriteCache.find? a with
  | some a' => return a'
  | none => do
     if cacheResult then set { env with rewriteCache := env.rewriteCache.insert a a }
     return a

/-- Return `b` if `a := b` is already in the translation cache.
    Otherwise, the following actions are performed:
      - execute `b ← f ()`
      - update cache with `a := b`
      - return `b'`
 NOTE: A call to `mkExpr` must be done whenever any new Expr is created during normalization and rewriting.
 This is so to ensure maximum sharing of expression.
 Moreover, this also ensure that we can direcly use pointer equality during simplification
 instead of the costly isDefEq function.
-/
def withTranslateEnvCache (a : Expr) (f: Unit → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let env ← get
  match env.rewriteCache.find? a with
  | some b => return b
  | none => do
     let b ← f ()
     updateRewriteCache a b
     return b

/-- Given a TranlateEnv `old_env` return a new `env` by performing the following actions:
     - `env` is initilaized to empty
     - set `env.recFunMap` to `old.env.replayRecFunMap`
     - ∀ `fbody := f` ∈ old_env.replayRecFunMap, add `f := f` in `env.rewriteCache`
     - ∀ `fbody := f` ∈ old_env.replayRecFunMap, add `f` in `env.recFunCache`
     - ∀ `fbody := f` ∈ old_env.replayRecFunMap, add `f := fbody` `env.recFunInstCache`
     - ∀ `fbody := f` ∈ old_env.recFunMap,
         if isOpaqueFunExpr f then
           - add `f := f` in `env.rewriteCache`
           - add `f` in `env.recFunCache`
           - add `fbody := f` in `env.recFunMap`
-/
def restartTranslateEnv (old_env : TranslateEnv) : MetaM (Unit × TranslateEnv) := do
 let visit : TranslateEnvT Unit := do
   -- set recFunMap to replayRecFunMap before recFunMap update
   let env ← get
   set {env with recFunMap := old_env.replayRecFunMap }
   old_env.replayRecFunMap.forM fun fbody f => do
      -- update rewrite cache with f to ensure physical equality during rewriting
      let f' ← mkExpr f
      let env ← get
      set {env with recFunCache := env.recFunCache.insert f',
                    recFunInstCache := env.recFunInstCache.insert f' fbody
          }
   old_env.recFunMap.forM fun fbody f => do
      if isOpaqueFunExpr f.getAppFn f.getAppArgs
      then
        -- update rewrite cache with f to ensure physical equality during rewriting
        let f' ← mkExpr f
        let env ← get
        set {env with recFunCache := env.recFunCache.insert f',
                      recFunMap := env.recFunMap.insert fbody f'
            }
 visit|>.run default

/-- Add a recursive function (i.e., function name expression or an instantiated polymorphic function) to the visited cache. -/
def cacheFunName (f : Expr) : TranslateEnvT Unit := do
 let env ← get
 set {env with recFunCache := env.recFunCache.insert f }

/-- Delete a recursive function (i.e., function name expression or an instantiated polymorphic function) from the visited cache. -/
def uncacheFunName (f : Expr) : TranslateEnvT Unit := do
 let env ← get
 set {env with recFunCache := env.recFunCache.erase f }


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
 return (← get).recFunCache.contains f

/-- Return `true` if `f` corresponds to a theorem name. -/
def isTheorem (f : Name) : MetaM Bool := do
  match (← getConstInfo f) with
  | ConstantInfo.thmInfo _ => pure true
  | _ => pure false


/-- Return `true` if `f` corresponds to a recursive function. -/
def isRecursiveFun (f : Name) : MetaM Bool := do
  if (← isTheorem f) then return false
  isRecursiveDefinition f

/-- Return `Bool` type  -/
def mkBoolType : TranslateEnvT Expr := mkExpr (mkConst ``Bool)

/-- Return `true` boolean constructor -/
def mkBoolTrue : TranslateEnvT Expr := mkExpr (mkConst ``true)

/-- Return `false` boolean constructor -/
def mkBoolFalse : TranslateEnvT Expr := mkExpr (mkConst ``false)

/-- Return `not` boolean operator -/
def mkBoolNotOp : TranslateEnvT Expr := mkExpr (mkConst ``not)

/-- Return `or` boolean operator -/
def mkBoolOrOp : TranslateEnvT Expr := mkExpr (mkConst ``or)

/-- Return `and` boolean operator -/
def mkBoolAndOp : TranslateEnvT Expr := mkExpr (mkConst ``and)

/-- Return `Prop` type  -/
def mkPropType : TranslateEnvT Expr := mkExpr (mkSort levelZero)

/-- Return `True` Prop  -/
def mkPropTrue : TranslateEnvT Expr := mkExpr (mkConst ``True)

/-- Return `False` Prop  -/
def mkPropFalse : TranslateEnvT Expr := mkExpr (mkConst ``False)

/-- Return `Not` operator -/
def mkPropNotOp : TranslateEnvT Expr := mkExpr (mkConst ``Not)

/-- Return `Or` operator -/
def mkPropOrOp : TranslateEnvT Expr := mkExpr (mkConst ``Or)

/-- Return `And` operator -/
def mkPropAndOp : TranslateEnvT Expr := mkExpr (mkConst ``And)

/-- Return `BEq.beq` operator -/
def mkBeqOp : TranslateEnvT Expr := mkExpr (mkConst ``BEq.beq [levelZero])

/-- Return `Eq` operator -/
def mkEqOp : TranslateEnvT Expr := mkExpr (mkConst ``Eq [levelOne])

/-- Return `ite` operator -/
def mkIteOp : TranslateEnvT Expr := mkExpr (mkConst ``ite [levelOne])

/-- Return `LE.le` operator -/
def mkLeOp : TranslateEnvT Expr := mkExpr (mkConst ``LE.le [levelZero])

/-- Return `LT.lt` operator -/
def mkLtOp : TranslateEnvT Expr := mkExpr (mkConst ``LT.lt [levelZero])

/-- Return `Decidable` const expression -/
def mkDecidableConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable)

/-- Return `decide` const expression -/
def mkDecideConst : TranslateEnvT Expr := mkExpr (mkConst ``Decidable.decide)

/-- Return `Inhabited` const expression -/
def mkInhabitedConst : TranslateEnvT Expr := mkExpr (mkConst ``Inhabited [levelOne])

/-- Return `BEq` const expression -/
def mkBEqConst : TranslateEnvT Expr := mkExpr (mkConst ``BEq [levelZero])

/-- Return `Nat` Type -/
def mkNatType : TranslateEnvT Expr := mkExpr (mkConst ``Nat)

/-- Return `Nat.add` operator -/
def mkNatAddOp : TranslateEnvT Expr := mkExpr (mkConst ``Nat.add)

/-- Return `Nat.sub` operator -/
def mkNatSubOp : TranslateEnvT Expr := mkExpr (mkConst ``Nat.sub)

/-- Return `Nat.mul` operator -/
def mkNatMulOp : TranslateEnvT Expr := mkExpr (mkConst ``Nat.mul)

/-- Return `Int` Type -/
def mkIntType : TranslateEnvT Expr := mkExpr (mkConst ``Int)

/-- Return `Int.add` operator -/
def mkIntAddOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.add)

/-- Return `Int.mul` operator -/
def mkIntMulOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.mul)

/-- Return `Int.neg` operator -/
def mkIntNegOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.neg)

/-- Return `Int.ofNat` constructor -/
def mkIntOfNat : TranslateEnvT Expr := mkExpr (mkConst ``Int.ofNat)

/-- Return `Int.toNat` operator -/
def mkIntToNatOp : TranslateEnvT Expr := mkExpr (mkConst ``Int.toNat)

/-- `mkAppExpr f #[a₀, ..., aₙ]` constructs the application `f a₀ ... aₙ` and cache the result.
-/
def mkAppExpr (f : Expr) (args: Array Expr) : TranslateEnvT Expr :=
  mkExpr (mkAppN f args)

/-- Return "==" Nat operator -/
def mkNatBeqOp : TranslateEnvT Expr := do
  let beqNat ← mkExpr (mkApp (← mkBeqOp) (← mkNatType))
  mkExpr (mkApp beqNat (← mkExpr (mkConst ``instBEqNat)))

/-- Return the `≤` Nat operator -/
def mkNatLeOp : TranslateEnvT Expr := do
  let leExpr ← mkExpr (mkApp (← mkLeOp) (← mkNatType))
  mkExpr (mkApp leExpr (← mkExpr (mkConst ``instLENat)))

/-- Return the `<` Nat operator -/
def mkNatLtOp : TranslateEnvT Expr := do
  let ltExpr ← mkExpr (mkApp (← mkLtOp) (← mkNatType))
  mkExpr (mkApp ltExpr (← mkExpr (mkConst ``instLTNat)))

/-- Return the `≤` Int operator -/
def mkIntLeOp : TranslateEnvT Expr := do
  let leExpr ← mkExpr (mkApp (← mkLeOp) (← mkIntType))
  mkExpr (mkApp leExpr (← mkExpr (mkConst ``Int.instLEInt)))

/-- Return the `<` Int operator -/
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
  match env.synthInstanceCache.find? cstr with
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
  let some d ← trySynthDecidableInstance? e | throwError "synthesize instance for [Decidable {reprStr e}] cannot be found"
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
  let some d ← trySynthConstraintInstance? beqCstr | throwError "synthesize instance for [BEq {reprStr e}] cannot be found"
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
  match env.whnfCache.find? a with
  | some b => return b
  | none => do
     let b ← whnf a
     set {env with whnfCache := env.whnfCache.insert a b}
     return b

/-- Given application `f x₁ ... xₙ`, return the arguments of `f` instantiating
    the polymorphic parameters of `f`.
    NOTE: It is assumed that all implicit arguments appear first in sequence `x₁ ... xₙ`, i.e.,
    the search is stopped when the first explicit argument is encountered.
-/
def getImplicitArgs (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
 let mut iargs := #[]
 let fInfo ← getFunInfoNArgs f args.size
 for i in [:args.size] do
   if i < fInfo.paramInfo.size then
     let aInfo := fInfo.paramInfo[i]!
     if aInfo.isExplicit
     then return iargs
     else iargs := iargs.push args[i]!
 return iargs


/-- Return `true` only when `e` corresponds to a recursive function call for
    which any entry exists in the visiting cache (i.e., `recFunCache`).
-/
def isVisitedRecFunAppExpr (e : Expr) : TranslateEnvT Bool := do
 match e with
 | Expr.app .. =>
    Expr.withApp e fun f args => do
      let iargs ← getImplicitArgs f args
      let instApp ← mkAppExpr f iargs
      isVisitedRecFun instApp
 | _ => return false

/-- Instantiate the level parameters `us` in `body` when `f` has at least one
    implicit argument (i.e., iargs.size > 0) and tag the recursive call
    in `body`.
-/
def generalizeRecCall (f : Name) (us : List Level) (iargs : Array Expr) (body : Expr) : MetaM Expr := do
 let body' := body.replace replacePred
 if iargs.size == 0 then return body'
 let cinfo ← getConstInfo f
 return (body'.instantiateLevelParams cinfo.levelParams us)

where
  replacePred (e : Expr) : Option Expr := do
   match e.getAppFn with
   | Expr.const rn _ =>
      if rn == f
      then some (tagAsRecursiveCall e)
      else none
   | _ => none


/-- Given `f` which is either a function name expression or an instantiated polymorphic function,
    and `fbody` corresponding to `f`'s definition, update the recursive instance cache (i.e., `recFunInstCache`),
-/
def updateRecFunInst (f : Expr) (fbody : Expr) : TranslateEnvT Unit := do
  let env ← get
  unless (env.recFunInstCache.find? f).isSome do
     set {env with recFunInstCache := env.recFunInstCache.insert f fbody}

/-- Given `f` which is either a function name expression or an instantiated polymorphic function,
    and `fbody` corresponding to `f`'s definition, update the replay recursive functon map (i.e., `replayRecFunMap`),
-/
def updateReplayRecCache (f : Expr) (fbody : Expr) : TranslateEnvT Unit := do
  let env ← get
  unless (env.replayRecFunMap.find? fbody).isSome do
     set {env with replayRecFunMap := env.replayRecFunMap.insert fbody f}


/-- Given application `f x₁ ... xₙ`, return `some fbody` when:
     - `f x₁ ... xₖ := fbody` is in cache and `x₁ ... xₖ` correspond to the implicit arguments of `f`; or
     - `f := fbody` is in cache and there is no implicit arguments in `x₁ ... xₙ`.
    Otherwise return `none`.
-/
def getRecFunInstBody? (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let env ← get
  let iargs ← getImplicitArgs f args
  return (env.recFunInstCache.find? (← mkAppExpr f iargs))


/-- Return `fₙ` if `body[f/_recFun x₁ ... xₖ] := fₙ` is already in the recursive function map only when flag `isOpaque` set to `false`.
    Otherwise,
      - If entry `body[f/_recFun x₁ ... xₖ] := fₙ` is in then recursive function map and flag `isOpaque` is set to `true`
        (i.e., `f` is an opaque function):
          - update the replay function map with `body[f/_recFun x₁ ... xₖ] := f` if entry does not exist.
          - return `f`
      - If there is no entry in the recursive function map for `body[f/_recFun x₁ ... xₖ]`:
         - update recursive function map with `body[f/_recFun x₁ ... xₖ] := f`
         - return `f`.
     where:
       - x₁ ... xₖ` correspond to the implicit arguments of `f` (if any).
    NOTE:
      - `f` is also removed from the visiting cache.
      - The polymorphic instance cache is updated with `f := body[f/_recFun x₁ ... xₖ]` (if required) for all cases.
        This is essential to avoid performing structural equivalence check again on an
        already handled recursive function.
    Assumes that `f` is either a function name expression or an instantiated polymorphic function.
-/
partial def storeRecFunDef (f : Expr) (body : Expr) (isOpaque: Bool) : TranslateEnvT Expr := do
  -- remove from visiting cache
  uncacheFunName f
  -- NOTE: we need to explicitly retrieve implicit arguments from the annotated recursive call
  -- as some opaque function (e.g., Nat.beq) may have been normalized during optimization.
  let some recCall := body.find? isTaggedRecursiveCall
    | throwError f!"storeRecFunDef: annotated recursive call expected in {reprStr body}"
  -- retrieve implicit arguments
  let i_args ← getImplicitArgs recCall.getAppFn' recCall.mdataExpr!.getAppArgs
  let body' := body.replace (replacePred i_args (← mkExpr (mkConst internalRecFun)))
  -- update ploymorphic instance cache
  updateRecFunInst f body'
  let env ← get
  match env.recFunMap.find? body' with
  | some fb =>
     if !isOpaque then return fb
     updateReplayRecCache f body'
     return f
  | none =>
     set {env with recFunMap := env.recFunMap.insert body' f}
     return f

where
  replacePred (i_args : Array Expr) (recFun : Expr) (e : Expr) : Option Expr := do
   match toTaggedRecursiveCall? e with
   | some b =>
        let mut margs := b.getAppArgs
        -- replace any occurrence in args first
        for i in [:margs.size] do
           margs := margs.modify i (.replace (replacePred i_args recFun))
        some (mkAppN recFun margs[i_args.size : margs.size])
   | _ => none


/-- Given `instApp` corresponding either to a function name expression or
    to an instantiated polymorphic function, determine if `instApp` has already a mapping
    in `recFunInstCache`. If so then retrieve the correponding function application in `recFunMap`.
    Otherwise return `none`.
    An error is triggered if no corresponding entry can be found in `recFunMap`.
-/
def hasRecFunInst? (instApp : Expr) (isOpaque: Bool) : TranslateEnvT (Option Expr) := do
  let env ← get
  match env.recFunInstCache.find? instApp with
  | some fbody =>
     -- retrieve function application from recFunMap
     match env.recFunMap.find? fbody with
     | r@(some fb) =>
        if isOpaque && !(← exprEq instApp fb)
        then updateReplayRecCache instApp fbody
             return instApp
        else return r
     | none => throwError f!"hasRecFunInst: expecting entry for {reprStr fbody} in recFunMap"
  | none => return none

end Solver
