import Blaster

namespace Tests.Issue195

-- Function typing must constrain results only on qualified arguments. In
-- particular, Nat's SMT carrier includes negative integers, and a generic
-- domain may be empty. Membership is a typing predicate with a forward
-- contract, not an iff based on behavior over the domain (which is vacuous
-- when the domain is empty). Every generic domain/codomain indexes it.
-- Lambda definitions also need the guards from Issue194.

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

-- Lambdas equal on Nat can have different raw integer expressions. Their
-- applications at negative integers must not make the context inconsistent.
#blaster (gen-cex: 0) (solve-result: 1)
  [∀ (g : (Nat → Nat) → Nat), g (fun x => x % (x + 1)) + g (fun x => x) = 1000 → False]

-- The earlier partial fix skipped generic domains. That restriction was
-- still unsound: even Empty has an identity function.
example : ¬ (∀ α : Type, ∀ f : α → α, (∀ x, f x = x) → ∃ _ : α, True) := by
  intro h
  obtain ⟨x, _⟩ := h Empty id (fun x => Empty.elim x)
  exact Empty.elim x

#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, ∀ f : α → α, (∀ x, f x = x) → ∃ _ : α, True]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α : Type, ∀ f : α → Nat, (∀ x, f x = 0) → ∃ _ : α, True]
#blaster (timeout: 5)
  [∀ α : Type, ∀ f : α → Nat, (∀ x, f x = 0) → f = fun _ => 0]


-- Empty domains must not collapse the shared carrier of other function types.
example : ¬ (∀ α β : Type, ∀ _b : β, ∀ g : (β → Nat) → Nat,
    (∀ _ : α, False) → g (fun _ => 0) ≠ g (fun _ => 1) → False) := by
  intro h
  exact h Empty Unit () (fun f => f ()) (fun x => Empty.elim x) (by decide)
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ α β : Type, ∀ _b : β, ∀ g : (β → Nat) → Nat,
    (∀ _ : α, False) → g (fun _ => 0) ≠ g (fun _ => 1) → False]

-- Extensionality witnesses cover every argument and use the qualified domains.
#blaster (timeout: 5)
  [∀ f g : Nat → Nat → Nat, (∀ x y, f x y = g x y) → f = g]
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 5)
  [∀ f : Nat → Nat → Nat, f = (fun x y => x + y + 1) → False]
#blaster (timeout: 5)
  [∀ α β : Type, ∀ f g : α → β → Nat, (∀ x y, f x y = g x y) → f = g]

end Tests.Issue195
