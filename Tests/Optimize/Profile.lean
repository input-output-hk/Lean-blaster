import Tests.Utils

open Lean Meta Elab Command Blaster.Optimize

-- Compare the actual optimizer with profiling enabled and disabled. Exercise
-- nested/sibling facts, closures, and constructor choices, not just a counter.
run_cmd liftTermElabM do
  let syntaxes := #[
    (← `(∀ x y : Nat, x = y → y = 0 → x + 1 = 1)),
    (← `(fun x : Nat => if x = 0 then x + 1 else x + 2)),
    (← `(fun x y : Nat => (fun a b : Nat => a + b) y x)),
    (← `(fun p q : Bool => ([if p then 1 else 2, if q then 3 else 4] : List Nat)))
  ]
  let inputs ← syntaxes.mapM fun stx => Tests.parseTerm stx
  for input in inputs do
    let (expected, baseEnv) ← (Optimize.main input).run (default : TranslateEnv)
    let now ← IO.monoNanosNow
    let ref ← IO.mkRef ({ startedNs := now, lastNs := now } : NormalizationProfile)
    let env := { (default : TranslateEnv) with optEnv.options.profile? := some ref }
    let (actual, profileEnv) ← (Optimize.main input).run env
    unless ← isDefEq actual expected do throwError "profiling changed the normalized expression"
    unless baseEnv.optEnv.hashConsCache.size == profileEnv.optEnv.hashConsCache.size &&
        baseEnv.optEnv.options.nextCtxId == profileEnv.optEnv.options.nextCtxId do
      throwError "profiling changed optimizer allocation/context counts"
    let p ← ref.get
    unless p.owners.isEmpty && p.imbalances == 0 && p.misses > 0 && p.hits > 0 do
      throwError "unbalanced or empty normalization profile"
    let total := p.entries.fold (fun sum _ e => sum + e.selfNs) 0
    unless total == p.lastNs - p.startedNs do throwError "exclusive profile times do not partition elapsed time"

section
set_option blaster.profileNormalize true
#testOptimize ["ProfiledSiblingFacts"]
  (∀ x : Nat, (if x = 0 then x + 1 else x + 2) =
    (if x = 0 then 1 else x + 2)) ===> True
#blaster (gen-cex: 0) (solve-result: 1) [∀ x : Nat, x = 0]
end

-- A later invocation must not inherit an earlier invocation's diagnostic ref.
run_cmd liftTermElabM do
  let (_, env) ← (Optimize.main (mkConst ``True)).run (default : TranslateEnv)
  unless env.optEnv.options.profile?.isNone do throwError "profile state leaked across invocations"
