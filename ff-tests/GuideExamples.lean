import Blaster
import Tests.FiniteField.LargePrime

/-! Executable companion to docs/finite-fields/native-support.md.
Theorems below use checked Lean proofs. Commands and the meta-level example
observe solver verdicts only; none closes a theorem with `blaster`.
Run from the repository root after building the imports and staging the solver:
  BLASTER_FF_CVC5="$PWD/.artifacts/finite-fields/solving/bin/cvc5" \
    lake env lean ff-tests/GuideExamples.lean
-/

namespace FiniteFieldGuide

open Blaster.FiniteField

-- This entire algebra section also works with import Blaster.FiniteField alone.
theorem primeSeven : Prime 7 :=
  prime_of_bounded 7 2 (by decide) (by decide) (by decide)

theorem evidenceSeven : PrimeModulus 7 := ⟨primeSeven⟩

example : (5 : Residue 6) + 3 = 2 := by decide

section
local instance : PrimeModulus 7 := evidenceSeven

example : (1 : Residue 7) / 2 = 4 := by decide
end

example (p : Nat) [PrimeModulus p] : (0 : Residue p)⁻¹ = 0 :=
  Residue.inv_zero

example (p : Nat) [PrimeModulus p] (x : Residue p) : x / 0 = 0 := by
  rw [Residue.div_eq_mul_inv, Residue.inv_zero, Lean.Grind.Semiring.mul_zero]

-- These are conditional queries, not definitions of Lean proof terms. The
-- explicit evidence parameter remains in the native admission context.
#blaster (solver: cvc5) (timeout: 30)
  [∀ (_ : PrimeModulus 7) (x y : Residue 7),
    x * y = 0 → x = 0 ∨ y = 0]

#blaster (solver: cvc5) (timeout: 30) (solve-result: 1)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x * x ≠ 2]

#blaster (solver: cvc5) (timeout: 30)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x / 0 = 0]

#blaster (solver: cvc5) (only-smt-lib: 1) (solve-result: 2)
  [∀ (_ : PrimeModulus 7) (x : Residue 7), x ^ (7 : Nat) = x]

open Test.FiniteFieldLargePrime

-- A checked fixture, not a production prime registry or a solver claim.
theorem suppliedCurve25519 : PrimeModulus (2 ^ 255 - 19) :=
  curve25519_eq ▸ curve25519_evidence

-- Direct solver clients can install actual checked evidence in a scoped local
-- let. Unlike a global instance alone, this is visible to native admission.
private instance : NeZero (2 ^ 255 - 19) := ⟨by decide⟩

private def largeDistributive : Prop :=
  ∀ x y : Residue (2 ^ 255 - 19), x * (y + 1) = x * y + x

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt

run_meta do
  let proof := mkConst ``suppliedCurve25519
  withLetDecl `checkedPrime (← inferType proof) proof fun _ => do
    let environment : TranslateEnv :=
      { (default : TranslateEnv) with optEnv.options.solverOptions := {
          solver := some .cvc5, timeout := some 30 } }
    let ((result, _), _) ←
      (Translate.main (mkConst ``largeDistributive)).run environment
    match result with
    | .Valid => logInfo "Curve25519: Valid (solver verdict, not a reconstructed proof)"
    | .Falsified _ => throwError "Curve25519 distributivity was falsified"
    | .Undetermined => throwError "Curve25519 distributivity was undetermined"

end FiniteFieldGuide
