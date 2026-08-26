import Blaster

namespace Tests.Issue195

-- Issue: `@isFun` membership unsatisfiable for lambdas over qualified codomain arrows.
-- Diagnosis: the `@isFun{v}_cstr` iff quantified the function's arguments over the whole
--            carrier sort instead of the qualified domain: for `Nat → Nat` it read
--              (= (forall ((@x0 Nat)) (@isNat (@apply @f @x0))) (@isFun @f))
--            with `Nat` aliased to `Int`. A concrete lambda such as `fun x : Nat => x + 1`
--            has a def_cstr that pins `@apply` off-domain too (`(@apply L -2) = -1`), so
--            the unguarded forall was falsifiable and `(@isFun L)` was forced FALSE.
--            Every congruence/extensionality axiom premised on `@isFun` was then vacuous
--            for the lambda:
--             - true funext goals were reported ❌ Falsified (bogus counterexample);
--             - worse, arrow-typed hypotheses assert their membership positively
--               (`(assert (@isFun $f))`), so a hypothesis `f = lambda` forced
--               `(@isFun L)` TRUE and the context became inconsistent: blaster proved
--               `False` ✅ Valid (see probe 3 below).
-- Fix: guard each argument of the isFun constraint's inner forall with its domain
--      qualifier (Quantifier.lean, generateApplyFunAndAssertions):
--        (= (forall ((@x0 Nat)) (=> (@isNat @x0) (@isNat (@apply @f @x0)))) (@isFun @f))
--      NOTE: a Bool codomain hides the bug (`@isBool` is trivially true); these probes
--      must keep a non-trivial codomain qualifier such as `Nat`.

-- 1. True by funext; needs `@apply_ext_fun`, whose `@isFun` premises were vacuous.
--    Reported ❌ Falsified before the fix.
#blaster [∀ (f : Nat → Nat), (∀ x, f x = x + 1) → f = fun x => x + 1]

-- 2. Congruence through a hypothesis equality with a lambda; pins the guarded path.
--    (Also "Valid" before the fix, but only because the context was inconsistent.)
#blaster [∀ (f : Nat → Nat), f = (fun x => x + 1) → f 2 = 3]

-- 3. The unsoundness vector: this statement is FALSE (take f := fun x => x + 1).
--    Reported ✅ Valid before the fix: `(assert (@isFun $f))` + `$f = L` +
--    unguarded cstr forced `∀ x:Int. @isNat (@apply L x)`, contradicting the
--    def_cstr's off-domain value `(@apply L -2) = -1`. Falsified is the honest answer.
/--
error: ❌ Falsified
---
error: Tactic `blaster` failed: Goal was falsified (see counterexample above)

f : Nat → Nat
⊢ (f = fun x => x + 1) → False
-/
#guard_msgs in
example (f : Nat → Nat) (h : f = fun x => x + 1) : False := by
  blaster (gen-cex: 0)

-- NOTE (#194 interaction): until the lambda def_cstr guard (PR #198) also lands,
-- reviving `@isFun` re-exposes the off-domain values that unguarded def_cstrs pin: two
-- lambdas that agree on Nat but whose SMT images differ at negative Ints (e.g.
-- `fun x => x % (x + 1)` vs `fun x => x`) are forced equal by `@apply_ext_fun`, making
-- the context inconsistent. This fix must therefore be merged together with / after
-- PR #198. Once both are in, enable the following (verified on the combined tree):
-- #blaster (gen-cex: 0) (solve-result: 1)
--   [∀ (g : (Nat → Nat) → Nat), g (fun x => x % (x + 1)) + g (fun x => x) = 1000 → False]

end Tests.Issue195
