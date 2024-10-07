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

end Solver
