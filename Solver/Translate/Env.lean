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
  cache : HashMap Lean.Expr Lean.Expr
 deriving Inhabited

abbrev TranslateEnvT := StateRefT TranslateEnv MetaM


/-- Update cache with `a := b`
. -/
def updateCache (a: Expr) (b: Expr) : TranslateEnvT Unit := do
  let env ← get
  set {env with cache := env.cache.insert a b }

/-- Return `a'` if `a := a'` is already in translation cache.
    Otherwise, the following actions are performed:
      - add `a := a` in cache
      - return `a`
-/
def mkExpr (a : Expr) : TranslateEnvT Expr := do
  let env ← get
  match env.cache.find? a with
  | some a' => return a'
  | none => do
     set { env with cache := env.cache.insert a a }
     return a

/-- Return `b` if `a := b` is already in the translation cache.
    Otherwise, the following actions are performed:
      - execute `b ← f ()`
      - update cache with `a := b`
      - if `b := b'` is already in cache
        then return `b'`
        else
          - add `b := b` in cache
          - return `b`
 NOTE: The last caching action is mainly performed to ensure maximum sharing of expression.
 This allows to direcly used pointer equality during simplification instead of the costly isDefEq function.
-/
def withTranslateEnvCache (a : Expr) (f: Unit → TranslateEnvT Expr) : TranslateEnvT Expr := do
  let env ← get
  match env.cache.find? a with
  | some b => return b
  | none => do
     let b ← f ()
     updateCache a b
     if a == b
     then return b
     else mkExpr b


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



end Solver
