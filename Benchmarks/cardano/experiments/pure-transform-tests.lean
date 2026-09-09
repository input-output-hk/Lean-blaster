import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

namespace Tests.Optimize.CacheReuse

-- Compare both cold and warm results with Lean, including a shared subterm
-- reached under different binder depths and different substitution slices.
run_cmd liftTermElabM do
  let check : TranslateEnvT Unit := do
    let nat ← hashcons (mkConst ``Nat)
    let x ← hashcons (mkFVar ⟨`transform_x⟩)
    let y ← hashcons (mkFVar ⟨`transform_y⟩)
    let z ← hashcons (mkFVar ⟨`transform_z⟩)
    let args := #[x, y, z]
    let pair ← hashcons (mkApp2 (mkConst ``Nat.add) x y)
    let body ← hashcons (mkApp2 (mkConst ``Nat.add) pair (mkLambda `t .default nat pair))
    for vars in #[args, #[z, x, y], #[x], #[y, z]] do
      for stop in [:vars.size] do
        for _ in [:2] do
          let r ← abstractFVarsRange body stop vars
          unless r == body.abstractRange (stop + 1) vars do
            throwError "memoized abstraction disagrees with Lean"
    let abstracted ← abstractFVars body args
    let replacements ← (#[mkRawNatLit 11, mkBVar 2, mkRawNatLit 33]).mapM hashcons
    for vars in #[args, replacements, replacements.reverse] do
      for start in [:vars.size + 1] do
        for stop in [start:vars.size + 1] do
          for _ in [:2] do
            let r ← instantiateSharedRevRange abstracted start stop vars
            unless r == abstracted.instantiateRevRange start stop vars do
              throwError "memoized substitution disagrees with Lean"
    -- Syntactic operations remain identical when the active hypotheses change.
    let parent ← newCtx
    updateEqualityMap x y parent.current
    let r ← abstractFVars body args
    let child ← newCtx
    updateEqualityMap x z child.current
    unless (← abstractFVars body args) == r do
      throwError "raw abstraction depended on branch hypotheses"
    endCtx child
    endCtx parent
    unless (← get).optEnv.memCache.sharedTransforms.hits > 0 do
      throwError "the differential checks did not exercise warm cache entries"
  check.run' (default : TranslateEnv)

-- Child facts must still normalize existing propositions and nested choices.
#testOptimize ["ChildHypothesesRemainVisible"]
  (∀ a b c : Prop, (a → b) ∧ (a → c ∧ (a → b))) ===>
  (∀ a b c : Prop, (a → b) ∧ (a → b ∧ c))

#blaster (gen-cex: 0) [∀ x y : Nat, (fun a b : Nat => a + b) y x = x + y]
#blaster (gen-cex: 0) (solve-result: 1) [∀ x : Nat, (if x = 0 then x + 1 else x + 2) = 1]

end Tests.Optimize.CacheReuse
