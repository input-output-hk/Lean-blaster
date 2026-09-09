import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize
namespace Tests.Issue242

-- Enter the same beta-cache entry while its previous invocation is still live.
-- Detect cycles before expanding them, so the unfixed regression fails quickly.
run_cmd liftTermElabM do
  let listId ← Tests.parseTerm (← `(fun xs : List Nat => xs))
  let pair ← Tests.parseTerm (← `(fun x y : Nat => (x, y)))
  let funId ← Tests.parseTerm (← `(fun f : Nat → Nat => f))
  let twice ← Tests.parseTerm (← `(fun x : Nat => x + x))
  let check : TranslateEnvT (Expr × Expr) := do
    let nat ← hashcons (mkConst ``Nat)
    let nil ← mkAppExpr (mkConst ``List.nil [levelZero]) nat
    let cons (n : Nat) (xs : Expr) :=
      mkApp3Expr (mkConst ``List.cons [levelZero]) nat (mkNatLit n) xs
    let listId ← hashcons listId
    let first ← betaLambdaEnv listId #[nil]
    let second ← betaLambdaEnv listId #[← cons 0 first.betaReduced]
    let assigned ← getMVarValue second.betaReduced
    if (assigned.find? (fun e => exprEq e second.betaReduced)).isSome then
      throwError "beta-cache reuse created a cyclic metavariable assignment"
    let nested ← instantiateSharedMVars second.betaReduced
    unless ← isDefEq nested (← cons 0 nil) do throwError "nested beta argument changed value"
    restoreMVarDecls second.prevMVarIdDecls
    unless ← isDefEq (← instantiateSharedMVars first.betaReduced) nil do
      throwError "outer beta assignment was not restored"

    -- The dependency can pass through another assigned metavariable.
    let alias ← hashcons (← mkFreshExprMVar none)
    assignMVar alias first.betaReduced
    let viaAlias ← betaLambdaEnv listId #[← cons 1 alias]
    unless ← isDefEq (← instantiateSharedMVars viaAlias.betaReduced) (← cons 1 nil) do
      throwError "transitive beta argument changed value"
    restoreMVarDecls viaAlias.prevMVarIdDecls

    -- Match reduction can legitimately pass unassigned pattern variables.
    let pending ← hashcons (← mkFreshExprMVar (some (mkApp (mkConst ``List [levelZero]) nat)))
    let withPending ← betaLambdaEnv listId #[pending]
    unless exprEq (← getMVarValue withPending.betaReduced) pending do
      throwError "an unassigned pattern variable was not preserved"
    restoreMVarDecls withPending.prevMVarIdDecls

    -- Resolve all right-hand sides before assigning any left-hand side.
    let pair ← hashcons pair
    discard <| betaLambdaEnv pair #[mkNatLit 1, mkNatLit 2]
    let some cached := (← get).optEnv.memCache.betaLambdaCache.get? (mkInstKey pair 2)
      | throwError "expected cached pair lambda"
    let swapped ← betaLambdaEnv pair #[cached.mvarArgs[1]!, cached.mvarArgs[0]!]
    let expected ← mkApp4Expr (mkConst ``Prod.mk [levelZero, levelZero]) nat nat (mkNatLit 2) (mkNatLit 1)
    unless ← isDefEq (← instantiateSharedMVars swapped.betaReduced) expected do
      throwError "beta-cache substitution was not simultaneous"
    restoreMVarDecls swapped.prevMVarIdDecls

    -- An extra argument also refers to the old assignment. Snapshotting only
    -- the arguments consumed by the lambda would change twice (succ 3) to 12.
    let funId ← hashcons funId
    let outer ← betaLambdaEnv funId #[← hashcons (mkConst ``Nat.succ)]
    let extra ← mkAppExpr outer.betaReduced (mkNatLit 3)
    let applied ← betaLambdaEnv funId #[← hashcons twice, extra]
    let overApplied ← instantiateSharedMVars applied.betaReduced
    restoreMVarDecls applied.prevMVarIdDecls
    unless ← isDefEq (← instantiateSharedMVars outer.betaReduced) (← hashcons (mkConst ``Nat.succ)) do
      throwError "over-application did not restore its outer function"
    return (nested, overApplied)
  let (nested, overApplied) ← check.run' (default : TranslateEnv)
  for (name, value) in [(`Tests.Issue242.nestedResult, nested),
                         (`Tests.Issue242.overAppliedResult, overApplied)] do
    addDecl <| .defnDecl {
      name, levelParams := [], type := ← inferType value, value,
      hints := .abbrev, safety := .safe }

#testOptimize ["Issue242NestedCachedBeta"] (norm-result: 1)
  nestedResult ===> ([0] : List Nat)
#testOptimize ["Issue242OverAppliedCachedBeta"] (norm-result: 1)
  overAppliedResult ===> (8 : Nat)
#blaster [overAppliedResult = 8]

end Tests.Issue242
