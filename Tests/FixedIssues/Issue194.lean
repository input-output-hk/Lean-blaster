import Blaster

namespace Tests.Issue194

-- Issue: Unexpected Valid on a false theorem, giving a kernel-accepted `False`.
-- Diagnosis: Guard asymmetry made the SMT background theory inconsistent.
--            The extensionality/congruence assertions generated for function
--            sorts (`generateFunInstDeclAux`) quantify over the QUALIFIED
--            domain only, e.g.
--
--   (assert (forall ((@x0 Nat) (@f (@@ArrowT2 Nat Bool)) (@g (@@ArrowT2 Nat Bool)))
--     (=> ... (= (forall ((@x0 Nat)) (=> (@isNat @x0) (= (@apply @f @x0) (@apply @g @x0))))
--             (= @f @g)) ...))
--
--            but the lambda definition constraints (`*_def_cstr`) pinning a
--            concrete lambda's values were emitted UNGUARDED:
--
--   (assert (forall (($7 Nat))
--     (!(= (@apply @lambda $7) (< $7 3)) :pattern ...)))
--
--            Since `Nat` is aliased to `Int`, the unguarded def_cstr also pins
--            the lambda's values on the negative integers. Extensionality
--            concludes that two lambdas agreeing on the qualified domain (here,
--            the actual naturals) are EQUAL, while their unguarded def_cstrs
--            force them to differ off-domain — a contradiction independent of
--            the goal, making every negated goal unsat, i.e., every theorem
--            "Valid".
-- Fix: `translateLambda` now guards the def_cstr quantifiers with the same
--      domain-qualifier premises used by the extensionality/congruence
--      assertions: `(=> (@isNat $7) (= (@apply @lambda $7) (< $7 3)))`.

-- The two lambdas below agree on all of Nat exactly when they agree on
-- {0, 1, 2} ∪ {y | y ≥ 3}; with the inconsistent theory Blaster proved the
-- (false) claim Valid for every list. Now it is correctly falsified,
-- e.g. by l = [3].
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - l: (List.cons 3 List.nil)
-/
#guard_msgs in
#blaster (solve-result: 1)
  [∀ (l : List Nat),
     (l.all (fun y => decide (y < 3)) && l.all (fun y => decide (y = 0 ∨ y = 1 ∨ y = 2))) = true]

-- Same goal through the `blaster` tactic: the tactic must refuse to close the
-- goal (it used to accept it via `blasterProven`, from which `False` was
-- derivable with `bogus [5]`).
/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - l: (List.cons 3 List.nil)
---
error: Tactic `blaster` failed: Goal was falsified (see counterexample above)

l : List Nat
⊢ ((l.all fun y => decide (y < 3)) && l.all fun y => decide (y = 0 ∨ y = 1 ∨ y = 2)) = true
-/
#guard_msgs in
theorem bogus (l : List Nat) :
    (l.all (fun y => decide (y < 3)) && l.all (fun y => decide (y = 0 ∨ y = 1 ∨ y = 2))) = true := by
  blaster (solve-result: 1)

end Tests.Issue194
