import Blaster.Optimize.Env.Utils

open Lean Meta
namespace Blaster.Optimize

private abbrev GroundKey := PtrExpr × Bool

private inductive GroundTask where
  | visit (e : Expr) (parameter : Bool)
  | finish (e : Expr) (key : GroundKey) (children : Array (Expr × Bool))
  deriving Inhabited

/-- Only the built-in numeral instances are accepted, never an arbitrary OfNat
    instance. This is a definitional literal conversion, independent of hypotheses. -/
private def frontendNumeral? (e : Expr) : TranslateEnvT (Option Expr) := do
  let args := e.getAppArgs
  unless e.isAppOfArity ``OfNat.ofNat 3 do return none
  let some n := isNatValue? args[1]! | return none
  if args[0]!.isConstOf ``Nat && args[2]!.isAppOfArity ``instOfNatNat 1 &&
      Expr.eqv args[2]!.appArg! args[1]! then
    return some (← mkNatLitExpr n)
  if args[0]!.isConstOf ``Int && args[2]!.isAppOfArity ``instOfNat 1 &&
      Expr.eqv args[2]!.appArg! args[1]! then
    return some (← mkIntLitExpr (Int.ofNat n))
  return none

private def groundChildren? (e : Expr) (parameter : Bool) : TranslateEnvT (Option (Array (Expr × Bool))) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  if e.isAppOfArity ``Neg.neg 3 && (e.getArg! 0).isConstOf ``Int &&
      (e.getArg! 1).isConstOf ``Int.instNegInt then
    return some #[(e.getArg! 2, false)]
  let .const name _ := e.getAppFn | return none
  let args := e.getAppArgs
  match ← getConstEnvInfo name with
  | .inductInfo info =>
    if !parameter || args.size > info.numParams + info.numIndices then return none
    return some (args.map fun arg => (arg, true))
  | .ctorInfo info =>
    -- String.mk must retain the existing character-to-string normalization.
    if name == ``String.mk then return none
    if args.size != info.numParams + info.numFields then return none
    let .inductInfo inductiveInfo ← getConstEnvInfo info.induct | return none
    if inductiveInfo.type.getForallBody.isProp then return none
    return some (args.mapIdx fun i arg => (arg, i < info.numParams))
  | _ => return none

private def finishGround (e : Expr) (args : Array Expr) : TranslateEnvT Expr := do
  if e.getAppFn.isConstOf ``Nat.zero then return ← mkNatLitExpr 0
  if e.getAppFn.isConstOf ``Nat.succ then
    let some n := isNatValue? args[0]! | return e
    return ← mkNatLitExpr (n + 1)
  if e.isAppOfArity ``Neg.neg 3 then
    let some n := isIntValue? args[0]! | return e
    return ← mkIntLitExpr (-n)
  let fn ← mkExpr e.getAppFn
  let original := e.getAppArgs
  if exprEq fn e.getAppFn && original.size == args.size &&
      (original.zip args).all (fun (a, b) => exprEq a b) then return ← mkExpr e
  mkAppNExpr fn args

/-- Canonicalize only closed constructor trees and exact built-in numeral
    encodings. No general computation is unfolded and no local equality is read.
    The per-query DAG cache therefore never contains a hypothesis-derived rewrite.
    The caller must still apply the current context's ordinary equality handling. -/
partial def groundConstructorValue? (e : Expr) : TranslateEnvT (Option Expr) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  let key : GroundKey := (⟨e⟩, false)
  let mut cache := (← get).optEnv.memCache.groundValueCache
  if let some result := cache.get? key then return result
  let mut todo := [GroundTask.visit e false]
  while !todo.isEmpty do
    let task := todo.head!
    todo := todo.tail!
    match task with
    | .visit term parameter =>
      let key : GroundKey := (⟨term⟩, parameter)
      if (cache.get? key).isNone then
        if term.hasFVar || term.hasMVar || term.hasLooseBVars then cache := cache.insert key none
        else if term.isLit || (parameter && term.isSort) then cache := cache.insert key (some (← mkExpr term))
        else if let some numeral ← frontendNumeral? term then cache := cache.insert key (some numeral)
        else
          match ← groundChildren? term parameter with
          | none => cache := cache.insert key none
          | some children =>
            if children.isEmpty then cache := cache.insert key (some (← finishGround term #[]))
            else
              todo := .finish term key children :: todo
              for child in children.reverse do todo := .visit child.1 child.2 :: todo
    | .finish term key children =>
      let normalized := children.mapM fun (child, parameter) => cache.getD (⟨child⟩, parameter) none
      match normalized with
      | none => cache := cache.insert key none
      | some args => cache := cache.insert key (some (← finishGround term args))
  modify fun env => { env with optEnv.memCache.groundValueCache := cache }
  return cache.getD key none

def isGroundConstructorValue (e : Expr) : TranslateEnvT Bool := do
  return (← groundConstructorValue? e).isSome

end Blaster.Optimize
