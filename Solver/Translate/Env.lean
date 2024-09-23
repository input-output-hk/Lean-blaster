import Lean

open Lean Meta
namespace Solver


/--
 Type defining the environment used when optimizing and
 translation a lean theorem to SMTLib
-/
structure TranslateEnv where
  /-- Names of type and functions encountered in the lean theorem to be solved. -/
  constants : NameHashSet := .empty
  /-- Free variables encountered in the lean theorem to be solved. -/
  freeVars : FVarIdHashSet := .empty
  /-- Cache memoizing the normalization and rewriting performed on the lean theorem. -/
  rewriteCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing the synthesize instance for decidable constraint. -/
  synthDecidableCache : HashMap Lean.Expr Lean.Expr
  /-- Cache memoizing the whnf result. -/
  whnfCache : HashMap Lean.Expr Lean.Expr
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


/-- Add `n` to the constants set maintained by the translation environment. -/
def addConstant (n : Name) : TranslateEnvT Unit := do
  let env ← get
  unless (env.constants.contains n) do
    set { env with constants := env.constants.insert n }

/-- Delete `n` from the constants set maintained by the translation environment.
-/
def removeConstant (n : Name) : TranslateEnvT Unit := do
  let env ← get
  set { env with constants := env.constants.erase n }


/-- Add `v` to the FVar set maintained by translation environment. -/
def addFVar (v : FVarId) : TranslateEnvT Unit := do
  let env ← get
  unless (env.freeVars.contains v) do
    set { env with freeVars := env.freeVars.insert v }

/-- Remove `n` to the constants name set in the translation environment.
-/
def removeFVar (v : FVarId) : TranslateEnvT Unit := do
  let env ← get
  set { env with freeVars := env.freeVars.erase v }


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

/-- `mkAppExpr f #[a₀, ..., aₙ]` constructs the application `f a₀ ... aₙ` and cache the result.
-/
def mkAppExpr (f : Expr) (args: Array Expr) : TranslateEnvT Expr :=
  mkExpr (mkAppN f args)

/-- Return "==" nat operator -/
def mkNatBeqOp : TranslateEnvT Expr := do
  let beqNat ← mkAppExpr (← mkBeqOp) #[← mkNatType]
  mkAppExpr beqNat #[(← mkExpr (mkConst ``instBEqNat))]


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
  | Int.ofNat n => mkAppExpr (← mkExpr (mkConst ``Int.ofNat)) #[(← mkNatLitExpr n)]
  | Int.negSucc n => mkAppExpr (← mkExpr (mkConst ``Int.negSucc)) #[(← mkNatLitExpr n)]

/-- `evalBinIntOp f n1 n2 perform the following:
      - let r := f n1 n2
      - construct int literal for `r`
      - cache result and return r
-/
def evalBinIntOp (f: Int -> Int -> Int) (n1 n2 : Int) : TranslateEnvT Expr :=
  mkIntLitExpr (f n1 n2)


/-- `mkDecidableConstraint e` constructs constraint [Decidable e] and cache the result.
-/
def mkDecidableConstraint (e : Expr) : TranslateEnvT Expr := do
  mkExpr (mkAppN (← mkExpr (mkConst ``Decidable)) #[e])

/-- Return `d` if there is already a synthesize instance for [Decidable e] in the synthesize cache.
    Otherwise, the following actions are performed:
     - execute d ← synthInstance [Decidable e]
     - add [Decidable e] := d to synthesize cache
     - return d
-/
def synthDecidableInstance (e : Expr) : TranslateEnvT Expr := do
  let dCstr ← mkDecidableConstraint e
  let env ← get
  match env.synthDecidableCache.find? dCstr with
  | some d => return d
  | none => do
     let d ← synthInstance dCstr
     updateSynthCache dCstr d
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

end Solver
