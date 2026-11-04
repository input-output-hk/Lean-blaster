import Lean
import Blaster

namespace Tests.Issue287

-- Issue: Unexpected Valid / bogus counterexample caused by a wrong match context reuse.
--        - https://github.com/input-output-hk/Lean-blaster/issues/152
--
-- Diagnosis: In `optimizeMatchAlt` (Blaster/Optimize/Rewriting/OptimizeMatch.lean:713) the
--            instance used as key for context reuse only carries the generic type parameters
--            of the matcher, i.e.,
--
--              let matchInst ← mkAppRangeExpr mInfo.nameExpr 0 mInfo.numParams args
--
--            The entry stored by `resetChoiceContext` (Blaster/Optimize/OptimizeStack.lean:66)
--            is then keyed by `(matchInst, altIdx)` and the parent context id. Hence, when
--            the same matcher is applied twice in the same context to *different*
--            discriminators, the second application silently reuses the scope (equality map
--            and NotEq patterns) and pattern fvars built for the first one.
--            With `numParams = 0` the key is the bare matcher name: `match y with ...`
--            reuses the hypotheses `x := A n` / `x := B n` of `match x with ...`, so every
--            occurrence of `x` in the alternatives of the second match is rewritten.
--
-- Related PR: This bug was originally reported in the following PR
--              - https://github.com/input-output-hk/Lean-blaster/pull/285

inductive T where
  | A (n : Nat)
  | B (n : Nat)
deriving DecidableEq, Inhabited

/-! ## Example 1: same matcher, different discriminators, same context (wrong reuse)

`dep x y` and `dep y x` are both elaborated with `dep.match_1` (no generic parameter).
Optimizing `dep x y` stores the contexts `x := A n` (alt 0) and `x := B n` (alt 1).
Optimizing `dep y x` reuses them: the alternatives `x = A n` / `x = B n` are rewritten to
`A n = A n` / `B n = B n`, i.e. `True`, and `dep y x` collapses to `True`.
-/

def dep (x y : T) : Prop :=
  match x with
  | .A n => y = .A n
  | .B n => y = .B n

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, dep x y ∨ dep y x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, dep y x ∨ dep x y]

-- Sanity checks (unaffected): the two applications are not in the same context (implication),
-- or the wrong reuse does not change the result (conjunction).
#blaster [∀ x y : T, dep x y → dep y x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, dep y x ∧ dep x y]

def tagOf (x y : T) : Nat :=
  match x with
  | .A n => if y = .A n then 1 else 0
  | .B n => if y = .B n then 1 else 0

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, tagOf x y + tagOf y x ≠ 0]

-- True but was falsified with the bogus counterexample x = A 11797, y = A 0.
-- Valid expected by Blaster
#blaster [∀ x y : T, tagOf x y = tagOf y x]

/-! ## Example 2: same matcher, same discriminators, appearing in its own rhs

Lean shares matchers with identical patterns: `outer` is elaborated with `inner.match_1`
(see `#print outer` with `pp.match false`). The catch-all alternative of `outer` unifies
`x, y` with no constructor pattern, and its rhs applies the very same matcher to the very
same discriminators through `inner x y`.
This example is correct with the current key, and remains correct when the key also carries
the motive and the discriminators, i.e.
  let matchInst ← mkAppRangeExpr mInfo.nameExpr 0 mInfo.getFirstAltPos args
-/

def inner (x y : T) : Nat :=
  match x, y with
  | .A n, .A m => n + m
  | _, _ => 0

def outer (x y : T) : Nat :=
  match x, y with
  | .A n, .A m => n * m
  | _, _ => inner x y + 1

-- true
#blaster [∀ x y : T, inner x y = 0 → outer x y = 0 ∨ outer x y = 1]
#blaster [∀ x y : T, outer x y ≠ 0 → outer x y = 1 ∨ inner x y ≠ 0]
#blaster [∀ x y : T, outer x y = inner x y + 1 ∨ outer x y = 0 ∨ inner x y ≥ 2]
-- false: x = A 1, y = A 1
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, outer x y = inner x y + 1]
-- false: x = A 1, y = A 0
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, outer x y = 0 → inner x y = 0]

-- Same shape with opaque discriminators: no unification possible for `f x` / `g y`.
opaque f : T → T
opaque g : T → T

def inner' (x y : T) : Nat :=
  match f x, g y with
  | .A n, .A m => n + m
  | _, _ => 0

def outer' (x y : T) : Nat :=
  match f x, g y with
  | .A n, .A m => n * m
  | _, _ => inner' x y + 1

-- Valid expected by Blaster
#blaster [∀ x y : T, inner' x y = 0 → outer' x y = 0 ∨ outer' x y = 1]
-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, outer' x y = inner' x y + 1]

-- Same matcher applied to the same discriminators through recursive unfolding.
def rec2 (x y : T) (k : Nat) : Nat :=
  match x, y with
  | .A n, .A m => n + m + k
  | _, _ => if h : k = 0 then inner x y else rec2 x y (k - 1)
termination_by k
decreasing_by omega

-- Valid expected by Blaster
#blaster [∀ x y : T, rec2 x y 2 = rec2 x y 1 + 1 ∨ rec2 x y 2 = 0]
#blaster [∀ x y : T, rec2 x y 0 ≥ inner x y]

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, rec2 x y 1 = 0]

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, rec2 x y 2 = 2]

-- Same matcher applied twice to the same discriminators in one context, then to swapped ones.
#blaster [∀ x y : T, inner x y + outer x y = outer x y + inner x y]
#blaster [∀ x y : T, inner x y = inner y x]
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, outer x y = outer y x → inner x y = 0]

-- Valid expected by Blaster
#blaster [∀ x y : T, dep x y ↔ dep y x]

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ x y : T, dep x y ↔ ¬ dep y x]

end Tests.Issue287
