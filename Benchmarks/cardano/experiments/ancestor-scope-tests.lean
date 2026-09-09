import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

namespace Tests.Optimize.CacheReuse

-- Lifetime/isolation checks for the stateful cache, independent of any solver.
run_cmd liftTermElabM do
  let check : TranslateEnvT Unit := do
    let key ← hashcons (mkConst `cacheProbe)
    let one ← hashcons (mkRawNatLit 1)
    let two ← hashcons (mkRawNatLit 2)
    let parent ← newCtx
    updateLocalRewriteCache key one
    let child ← newCtx
    unless exprEq (← findLocalCache key (← get)) one do
      throwError "child did not reuse its parent's rewrite"
    updateLocalRewriteCache key two
    unless exprEq (← findLocalCache key (← get)) two do
      throwError "nearest cache entry must win"
    endCtx child
    let sibling ← newCtx
    unless exprEq (← findLocalCache key (← get)) one do
      throwError "a closed sibling's rewrite escaped its scope"
    endCtx sibling
    endCtx parent
    let other ← newCtx
    unless exprEq (← findLocalCache key (← get)) instCacheMiss do
      throwError "a closed parent's rewrite escaped its scope"
    endCtx other
    -- Choice scopes can be re-entered, while discarded maps remain misses.
    let reused ← newCtx
    updateLocalRewriteCache key two
    resetChoiceContext (some reused) #[] key 0
    setAndCommitCtx reused
    let nested ← newCtx
    unless exprEq (← findLocalCache key (← get)) two do
      throwError "re-entered choice scope lost its parent relationship"
    endCtx nested
    endCtx reused
  check.run' (default : TranslateEnv)

-- A child's additional facts still need to simplify the result of an ancestor.
#blaster (gen-cex: 0)
  [∀ x y : Nat, x = y → y = 0 → x + 1 = 1]
#testOptimize ["NestedBranchFacts"]
  (∀ x y : Nat, (if x = y then (if y = 0 then x + 1 else y + 1) else x + 1) = x + 1) ===> True
#testOptimize ["SiblingIsolation"]
  (∀ x : Nat, (if x = 0 then x + 1 else x + 2) =
    (if x = 0 then 1 else x + 2)) ===> True
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ x : Nat, (if x = 0 then x + 1 else x + 2) = 1]

end Tests.Optimize.CacheReuse
