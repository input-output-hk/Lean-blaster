import Lean

open Lean Meta
namespace Solver


/--
 Type defining the environment used when optimizing and
 translation a lean theorem to SMTLib
-/
structure TranslateEnv where
  /-- Cache memoizing the normalization and rewriting performed on the lean theorem. -/
  rewriteCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing the synthesize instance for decidable constraint. -/
  synthDecidableCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing the whnf result. -/
  whnfCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing type for a match application of the form
       `f.match.n [p₁, ..., pₙ, pa₍₁₎₍₁₎ → .. → pa₍₁₎₍ₖ₎ → rhs₁, ..., pa₍ₘ₎₍₁₎ → .. → pa₍ₘ₎₍ₖ₎ → rhsₘ]`, s.t.:
      An entry in this map is expected to be of the form `Type(f.match.n [p₁, ..., pₙ])` := fun.match.n p₁ ... pₙ`
      where, p₁, ..., pₙ correspond to the arguments instantiating polymorphic params.
      This is used to determine equivalence between match functions (see function `optimizeMatch`).
  -/
  matchCache: HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing instance of recursive functions.
      An entry in this map is expected to be of the form `f x₁ ... xₙ := (fᵢₙₛₜ, fdef)`,
      where:
        - `x₁ .. xₙ`: correspond to the arguments instantiating the polymorphic parameters of `f` (if any).
        - fᵢₙₛₜ: correspond to a generated instance name (see function `updateRecFunInst`).
        - fdef: correspond to the recursive function body.
  -/
  recFunInstCache : HashMap Lean.Expr (Lean.Name × Lean.Expr)
  /-- Cache keeping track of visited recursive function. -/
  recFunCache: NameHashSet
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
      The rewriting will restart from the old TranslateEnv instance with:
        - Map recFunMap replaced with replayRecFunMap
        - Maps rewriteCache, recFunInstCache and replayRecFunMap emptied
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
  set {env with synthDecidableCache := env.synthDecidableCache.insert a b }

/-- Return `a'` if `a := a'` is already in translation cache.
    Otherwise, the following actions are performed:
      - add `a := a` in cache
      - return `a`
-/
def mkExpr (a : Expr) : TranslateEnvT Expr := do
  let env ← get
  match env.rewriteCache.find? a with
  | some a' => return a'
  | none => do
     set { env with rewriteCache := env.rewriteCache.insert a a }
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

/-- Add a recursive function name to the visited cache. -/
def cacheFunName (f : Name) : TranslateEnvT Unit := do
 let env ← get
 set {env with recFunCache := env.recFunCache.insert f }


/-- Internal genralized rec fun const to be used for in normalized recursive
    definition kept in `recFunMap`
-/
def internalRecFun : Name := `_recFun


/-- Return `true` if f corresponds to internal const ``_recFun. -/
def isRecFunInternal (f : Name) : Bool := f == internalRecFun

/-- Return `true` if f is a const expression corresponding to internal const ``_recFun. -/
def isRecFunInternalExpr (f : Expr) : Bool :=
 match f with
 | Expr.const n _ => isRecFunInternal n
 | _ => false


/-- Return `true` if `f` either corresponds to internal const ``_recFun or
    is already in the recursive function cache. -/
def isVisitedRecFun (f : Name) : TranslateEnvT Bool :=
 return ((isRecFunInternal f) || (← get).recFunCache.contains f)

/-- Return `true` if `f` corresponds to a theorem name. -/
def isTheorem (f : Name) : MetaM Bool := do
  match (← getConstInfo f) with
  | ConstantInfo.thmInfo _ => pure true
  | _ => pure false


/-- Return `true` if `f` is a recursive function or corresponds to internal const ``_recFun. -/
def isRecursiveFun (f : Name) : MetaM Bool := do
  if (isRecFunInternal f)
  then return true
  else if (← isTheorem f)
       then return false
       else isRecursiveDefinition f

#print ConstantInfo
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
  let beqNat ← mkAppExpr (← mkBeqOp) #[← mkNatType]
  mkAppExpr beqNat #[(← mkExpr (mkConst ``instBEqNat))]

/-- Return the `≤` Nat operator -/
def mkNatLeOp : TranslateEnvT Expr := do
  let leExpr ← mkAppExpr (← mkLeOp) #[← mkNatType]
  mkAppExpr leExpr #[(← mkExpr (mkConst ``instLENat))]

/-- Return the `<` Nat operator -/
def mkNatLtOp : TranslateEnvT Expr := do
  let ltExpr ← mkAppExpr (← mkLtOp) #[← mkNatType]
  mkAppExpr ltExpr #[(← mkExpr (mkConst ``instLTNat))]

/-- Return the `≤` Int operator -/
def mkIntLeOp : TranslateEnvT Expr := do
  let leExpr ← mkAppExpr (← mkLeOp) #[← mkIntType]
  mkAppExpr leExpr #[(← mkExpr (mkConst ``Int.instLEInt))]

/-- Return the `<` Int operator -/
def mkIntLtOp : TranslateEnvT Expr := do
  let ltExpr ← mkAppExpr (← mkLtOp) #[← mkIntType]
  mkAppExpr ltExpr #[(← mkExpr (mkConst ``Int.instLTInt))]


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
  | Int.ofNat n => mkAppExpr (← mkIntOfNat) #[(← mkNatLitExpr n)]
  | Int.negSucc n => mkAppExpr (← mkExpr (mkConst ``Int.negSucc)) #[(← mkNatLitExpr n)]

/-- `mkNatNegExpr n` constructs and cache the negation of a Nat literal expression, i.e.,
     Int.negSucc (Expr.lit (Literal.natVal (n - 1))`.
-/
def mkNatNegExpr (n : Nat) : TranslateEnvT Expr := do
  mkAppExpr (← mkExpr (mkConst ``Int.negSucc)) #[(← mkNatLitExpr (n - 1))]


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


/-- Return `d` if there is already a synthesize instance for [Decidable e] in the synthesize cache.
    Otherwise, the following actions are performed:
     - execute `LOption.some d ← trySynthInstance [Decidable e]`
     - add [Decidable e] := d to synthesize cache
     - return d
    Return `none` when `trySynthInstance` does not return `LOption.some`
-/
def trySynthDecidableInstance? (e : Expr) (cacheDecidableCst := true) : TranslateEnvT (Option Expr) := do
  let dCstr ← mkDecidableConstraint e cacheDecidableCst
  let env ← get
  match env.synthDecidableCache.find? dCstr with
  | some d => return d
  | none => do
     let LOption.some d ← trySynthInstance dCstr | return none
     updateSynthCache dCstr d
     return d

/-- Same as `trySynthDecidableInstance` but throws an error when a decidable instance cannot be found. -/
def synthDecidableInstance! (e : Expr) : TranslateEnvT Expr := do
  let some d ← trySynthDecidableInstance? e | throwError "synthesize instance for [Decidable {reprStr e}] cannot be found"
  return d


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


/-- Replace recursive function call `f x₀ ... xₙ` with `_recFun xₖ ... xₙ` in `body` s.t.:
    - `xₖ ... xₙ`: correspond to the explicit arguments of `f` and are derived according
      to the provided implicit arguments `iargs`, with `k = iargs.size - 1`.
   NOTE: that `k = 0` when `iargs.size = 0`.
   NOTE: replacing `f x₀ ... xₙ` with generic name `_recFun` applied to only explicit arguments
   facilitates the detection of structurally equivalent recursive functions.
-/
def generalizeRecCall (f : Name) (us : List Level) (iargs : Array Expr) (body : Expr) : TranslateEnvT Expr := do
 let body' ←
   if iargs.size > 0
   then
     let cinfo ← getConstInfo f
     pure (body.instantiateLevelParams cinfo.levelParams us)
   else pure body
 let genRec ← mkExpr (mkConst internalRecFun)
 return body'.replace (replacePred genRec)

where

  replacePred (recFun : Expr) (e : Expr) : Option Expr := do
   match e.getAppFn with
   | Expr.const rn _ =>
      Expr.withApp e fun _ args => do
       if rn == f
       then some (mkAppN recFun args[iargs.size : args.size])
       else none
   | _ => none

/-- Given recursive function `f`, implicits arguments `x₀ ... xₖ` (if any) and `fbody` corresponding to `f`'s definition,
    update the recursive instance cache (i.e., `recFunInstCache`), when there is no entry for `f x₀ ..., xₖ, s.t.:
      - when k > 0:
        - let fi := f ++ _Inst_ ++ freshId
        - add `f x₁ ... xₖ := (fi, fbody)` in cache
      - when k = 0:
         - add f := (f, body) in cache
    An error is triggered if `f` is not a function name expression.
-/
def updateRecFunInst (f : Expr) (iargs : Array Expr) (fbody : Expr) : TranslateEnvT Unit := do
  match f with
  | Expr.const n _ =>
     let auxApp := if iargs.size > 0 then mkAppN f iargs else f
      let env ← get
      unless (env.recFunInstCache.find? auxApp).isNone do
       let fi ←
          if iargs.size > 0
          then
            let id ← mkFreshId
            pure (n ++ `_Inst_ ++ id)
          else pure n
       set {env with recFunInstCache := env.recFunInstCache.insert auxApp (fi, fbody)}
  | _ => throwError "updateRecFunInst: function name expression expected but got {reprStr f}"

/-- Given application `f x₁ ... xₙ`, return `some (fi, fbody)` when:
     - `f x₁ ... xₖ := (fi, fbody)` is in cache and `x₁ ... xₖ` correspond to the implicit arguments of `f`; or
     - `f := (f, fbody)` is in cache and there is no implicit arguments in `x₁ ... xₙ`.
    Otherwise return `none`.
-/
def getRecFunInstName? (f : Expr) (args : Array Expr) : TranslateEnvT (Option (Name × Expr)) := do
  let env ← get
  let iargs ← getImplicitArgs f args
  let auxApp  := if iargs.size > 0 then mkAppN f iargs else f
  return (env.recFunInstCache.find? auxApp)

/-- Return `fₙ` if `body := fₙ` is already in the recursive function map.
    Otherwise, the following actions are performed:
      - update recursive function map with `body := f iargs`
      - update polymorphic instance cache if necessary (see function `updateRecFunInst`)
      - return `f iargs`.
    Assumes that the recursive function call on `f` has been replaced with the generic call `_recFun`
    (see function `generalizeRecCall`).
    Assumes that `iargs` only contain the implicit arguments for `f` (if any).
-/
def storeRecFunDef (f : Expr) (iargs : Array Expr) (body : Expr) : TranslateEnvT Expr := do
 let env ← get
  match env.recFunMap.find? body with
  | some fb => return fb
  | none =>
     let auxApp ← mkAppExpr f iargs
     set {env with recFunMap := env.recFunMap.insert body auxApp}
     updateRecFunInst f iargs body
     return auxApp


end Solver
