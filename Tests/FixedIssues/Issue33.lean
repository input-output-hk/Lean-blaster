import Blaster

namespace Tests.Issue33

-- Issue: Unexpected Valid
-- Diagnosis: lambda definition axioms ranged over every value of an SMT
-- carrier instead of only values represented by the corresponding Lean type.
-- This is unsound for refined encodings such as `Nat`, whose SMT carrier is
-- `Int` and whose valid domain is selected by `@isNat`.

-- For the closure-converted equality lambda `fun x y : Nat => x = y`, the
-- unguarded definition constrained its behavior even at negative integers.
-- The closures obtained at `x = -1` and `x = -2` agree on every valid `Nat`,
-- so valid-domain function extensionality equates them. Their unguarded
-- definitions nevertheless disagree at `y = -1`, making the SMT theory
-- inconsistent. Guarding the monomorphic captured values and explicit lambda
-- arguments with their domain predicates prevents this contradiction.

-- Minimal soundness check: agreement at one point does not imply equality.
#blaster (gen-cex: 0) (solve-result: 1) [∀ (f g : Nat → Bool), f 0 = g 0 → f = g]

-- Real-world regression: the validator is true only when the threshold is
-- zero and there are no verifiers. The universally quantified claim below is
-- false for every positive threshold. Z3 4.15.2 does not find its model within
-- the existing three-second limit, but it must never derive `Valid` from an
-- inconsistent background theory.
structure Verifier where
  payment_key : Nat
  is_mandatory : Bool

structure VerifierConfig where
  verifiers : List Verifier
  optional_threshold : Nat

def validate_signatures (verifier_config : VerifierConfig) (signatories : List Nat) : Bool :=
  let (mandatory_verifiers, optional_verifiers) :=
    verifier_config.verifiers.partition Verifier.is_mandatory

  let mandatory_payment_keys := mandatory_verifiers.map Verifier.payment_key
  let optional_payment_keys := optional_verifiers.map Verifier.payment_key

  let all_mandatory_signed :=
    mandatory_payment_keys.all
      (λ payment_key => signatories.any (λ signature => signature == payment_key))

  let optional_signatures_count :=
    optional_payment_keys.foldr
      (λ payment_key acc =>
        if signatories.any (λ signature => signature == payment_key)
          then acc + 1
          else acc)
      0

  let threshold_met := optional_signatures_count >= verifier_config.optional_threshold

  all_mandatory_signed && threshold_met

#blaster (gen-cex: 0) (solve-result: 2) (timeout: 3)
  [∀ (transaction : List Nat) (n : Nat),
       validate_signatures (VerifierConfig.mk [] n) transaction = true]

end Tests.Issue33
