import Blaster

namespace Tests.Issue34

/-!
# Issue XX — Blaster can unsoundly prove FALSE theorems Valid (residual functional-extensionality hole)

## Status: OPEN (not fixed). This file is a reproduction / bug report.

## Summary

This is a residual instance of the same class of soundness bug fixed in #98 / `Issue33.lean`
(functional extensionality). #98 corrected the *quantifier structure* of the extensionality
axiom; this issue is the leftover *domain-guard asymmetry*.

`Blaster` models Lean's `Nat` as SMT `Int` together with a guard predicate
`@isNat x := (0 <= x)`. The SMT domain therefore contains "phantom" negative integers that are
not real naturals. The unsoundness comes from an asymmetry in how that guard is applied:

  * Function **extensionality** is emitted GUARDED by `@isNat` — it concludes `f = g` from
    agreement on natural-number arguments only:
        (∀ x, @isNat x → apply(f, x) = apply(g, x)) → f = g
    (see `generateApplyFunAndAssertions` in `Blaster/Smt/Translate/Quantifier.lean`, where the
    inner `∀` body is wrapped with the `@isNat` predicate qualifier — around lines 748-779).

  * But the lambda / `apply` **definition** axioms (`@..._def_cstr`, e.g. the translation of
    `fun a b => a == b`) are emitted UNGUARDED — they pin `apply` values over the *entire* `Int`
    domain, including the phantom negatives.

Because of this mismatch, two functions that agree on every natural but differ on a phantom
negative point get wrongly identified as equal by the guarded extensionality axiom, and then
applying that (false) equality at the negative point yields `true = false`.

Concretely: let `eqk(-1)` be the predicate `fun y => (-1 == y)` (the SMT image of an equality
lambda at the phantom argument `-1`) and let `cf` be a constant-false function (e.g. `[].any …`).
They agree on every natural (`-1` equals no natural; `cf` is false everywhere), so the guarded
extensionality axiom derives `eqk(-1) = cf`. But `apply(eqk(-1), -1) = (-1 == -1) = true` while
`apply(cf, -1) = false`. Contradiction. An inconsistent theory proves anything, so Blaster reports
the goal below as **Valid** even though it is false.

## The false theorem

`validate_signatures (VerifierConfig.mk [] n) transaction` reduces to `0 ≥ n` (empty verifier
list ⇒ `all_mandatory_signed = true`, `optional_signatures_count = 0`, result = `0 ≥ n`). So the
universally-quantified claim below is FALSE — `n = 1` is a counterexample. A *sound* Blaster must
never report it Valid; it should refute it (Falsified) or, at worst, give up (Undetermined).
It must NOT prove it. `solve-result: 1` (ExpectedFalsified) below therefore encodes the sound
expectation: the reproduction currently fails with "❌ Unexpected Valid" whenever the solver
detects the (latent) inconsistency.

## Why this is hard to reproduce reliably (important!)

The generated SMT theory is genuinely inconsistent, but whether z3 *finds* the contradiction in
the full query is a fragile, heuristic-dependent coin-flip. Empirically the outcome flips between
`unsat` (→ Valid, bug visible) and `unknown` (→ Undetermined, bug hidden) depending on:

  * the z3 build — same version `4.15.2` returns `unsat` on macOS/arm64 but `unknown` on the CI
    Linux/x64 build, so CI currently passes while local runs fail;
  * the exact SMT symbol names — any declaration added *above* the `#blaster` command bumps Lean's
    fresh-name counter, renumbering the `@..._uniq.NNNN` symbols; that renaming alone flips z3 from
    `unsat` (0.8s) to `unknown` (times out). So editing anything above this command can make the
    "bug disappear";
  * the z3 option combination and the `timeout`.

Do NOT read an Undetermined/passing result here as "the bug is fixed" — it only means this
particular solver run failed to walk into the inconsistency. The bug is only truly fixed when the
generated theory is made consistent (guard the lambda/`apply` `_def_cstr` axioms with `@isNat`, to
match the guard extensionality already uses). See the SMT snippet below for a check that is
*independent* of that fragility.
-/

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

-- FALSE theorem (n = 1 is a counterexample). Sound expectation is Falsified (solve-result: 1);
-- on affected solver builds Blaster instead proves it Valid → "❌ Unexpected Valid".
-- Keep this `#blaster` the FIRST command in the namespace: inserting declarations above it
-- renumbers the SMT symbols and can mask the bug (see the header).
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 20)
  [∀ (transaction : List Nat) (n : Nat),
       validate_signatures (VerifierConfig.mk [] n) transaction = true]

end Tests.Issue34

/-!
## Reliable, solver-independent proof of the inconsistency

Save the block below as `issueXX.smt2` and run `z3 issueXX.smt2`. It returns `unsat` on *every*
z3 configuration (default options, MBQI, macro-finder, all platforms) — it distils Blaster's
encoding to the four relevant axioms plus a single ground negative witness, so the solver does not
have to *search* for the phantom point. `unsat` here means: the axioms Blaster emits for
`Nat → Bool` functions are contradictory.

```smt2
(define-sort Nat () Int)
(define-fun isNat ((x Nat)) Bool (<= 0 x))
(declare-sort Fun 0)
(declare-fun apply (Fun Nat) Bool)
(declare-fun isFun (Fun) Bool)

; @isFun_*_cstr : isBool is always true, so every f is a valid Nat->Bool function.
(assert (forall ((f Fun)) (isFun f)))

; @apply_*_ext_fun : extensionality GUARDED by isNat  (agree on naturals ⇒ equal).  <-- the bug
(assert (forall ((f Fun) (g Fun))
  (=> (isFun f) (=> (isFun g)
      (=> (forall ((x Nat)) (=> (isNat x) (= (apply f x) (apply g x))))
          (= f g))))))

; @..._def_cstr for the equality lambda (fun a b => a == b), asserted UNGUARDED over all Int.
(declare-fun eqk (Nat) Fun)
(assert (forall ((k Nat) (y Nat)) (= (apply (eqk k) y) (= k y))))

; @..._def_cstr for a constant-false function (e.g. `[].any …`), also asserted UNGUARDED.
(declare-const cf Fun)
(assert (forall ((y Nat)) (= (apply cf y) false)))

; One phantom-negative witness. We only put the term (eqk nk) into the e-graph; guarded
; extensionality then derives (eqk nk) = cf, and the theory blows up at the negative point nk.
(declare-const nk Nat)
(assert (< nk 0))
(assert (isFun (eqk nk)))

(check-sat)   ; => unsat, on every z3 configuration
```

Suggested fix: emit the lambda / `apply` `_def_cstr` axioms guarded by `@isNat` on their
quantified arguments (mirroring the `@isNat` guard already used by `@apply_*_ext_fun`), so that
`apply` is only pinned on naturals and phantom-negative values stay free for extensionality to
unify consistently.
-/
