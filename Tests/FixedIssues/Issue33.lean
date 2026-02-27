import Blaster

namespace Tests.Issue33

-- Issue: Functional extensionality axiom has incorrect quantifier structure, causing unsoundness.

-- Blaster emits the following axiom in the SMT-LIB translation:

-- (assert (forall ((@x0 Nat) (@f (@@ArrowT2 Nat Bool)) (@g (@@ArrowT2 Nat Bool)))
--   (!(=> (= (@apply_uniq @f @x0) (@apply_uniq @g @x0)) (= @f @g))
--   :pattern ( (= (@apply_uniq @f @x0) (@apply_uniq @g @x0)))
--   :qid @apply_uniq_ext_fun)
-- ))

-- This is intended to be functional extensionality:
--   ∀ f g, (∀ x, f(x) = g(x)) → f = g

-- But the quantifier structure is wrong. It says:
--   ∀ x f g, f(x) = g(x) → f = g

-- In the buggy version, f and g agreeing on any single point implies equality.
-- In the correct version, f and g must agree on all points.

-- This makes the theory inconsistent. For example, let:
--   f = (λ x => x == 0)   -- true only at 0
--   g = (λ x => x == 1)   -- true only at 1

-- f and g agree at 42: f(42) = false = g(42).
-- So the buggy axiom concludes f = g. But f(0) = true ≠ false = g(0).
-- Contradiction. The theory is inconsistent and can prove anything.

-- Diagnosis: In generateApplyFunAndAssertions, the quantifier over x was placed
-- at the outer level alongside f and g, instead of being nested inside the
-- antecedent of the implication.

-- Fix: Introduce an inner ∀ x over the equality f(x) = g(x), and quantify
-- only f and g at the outer level.

-- Minimal reproduction: Blaster incorrectly proves that any two functions
-- agreeing at 0 must be equal everywhere.
#blaster (solve-result: 1) [∀ (f g : Nat → Bool), f 0 = g 0 → f = g]

-- Real-world example: a multi-signature validator that Blaster incorrectly
-- deems always valid, regardless of the threshold.
-- validate_signatures should only return true when threshold is zero and
-- there are no verifiers. For threshold n > 0, it should return false.
-- Blaster proves it valid for arbitrary n, which is false.
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

#blaster (solve-result: 1) (timeout: 3)
  [∀ (transaction : List Nat) (n : Nat),
  validate_signatures (VerifierConfig.mk [] n) transaction = true]

end Tests.Issue33
