import Blaster

open Lean Elab Command Term Meta Blaster.Optimize

-- Exercise the reconstruction fallback directly: skipping it must produce a
-- placeholder of the expected type, while matching proofs must be preserved.
run_elab do
  unless (default : Blaster.Options.BlasterOptions).reconstructProofs do
    throwError "Proof reconstruction must remain enabled by default"
  let expected ← elabTerm (← `(1 < (2 : Nat))) none
  let original ← elabTerm (← `(True.intro)) none
  let matching := Lean.mkConst ``True.intro
  let matchingType := Lean.mkConst ``True
  for enabled in [true, false] do
    let env := { (default : TranslateEnv) with
      optEnv.options.solverOptions.reconstructProofs := enabled }
    let (proof, _) ← (do backwardProof (← hashcons expected) (← hashcons original)).run env
    unless proof.hasSorry == !enabled do
      throwError "Unexpected reconstruction result with reconstructProofs={enabled}"
    unless ← isDefEq (← inferType proof) expected do
      throwError "Reconstructed proof has the wrong type"
    let (reused, _) ← (do backwardProof (← hashcons matchingType) (← hashcons matching)).run env
    unless reused == matching do
      throwError "Matching proof was not preserved"

-- Computational Decidable instances and dependent proof arguments still work.
#blaster (reconstruct-proofs: 0) (timeout: 5)
  [∀ x : Fin 5, (x + 1).val = (x.val + 1) % 5]
#blaster (reconstruct-proofs: 1) (timeout: 5)
  [∀ x : Fin 5, (x + 1).val = (x.val + 1) % 5]
#blaster (reconstruct-proofs: 0) (timeout: 5)
  [∀ n : Nat, (if n < 3 then n + 1 else n) ≥ n]
#blaster (reconstruct-proofs: 0) (timeout: 5) (solve-result: 1)
  [∀ n : Nat, (if n < 3 then n + 1 else n) = n]
