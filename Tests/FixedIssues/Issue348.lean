import Lean
import Blaster
import Tests.Utils

namespace Tests.Issue348

-- Issue: https://github.com/input-output-hk/Lean-blaster/issues/348
--        an expression without any FVar/MVar was always looked up in, and cached into, the global
--        rewrite cache (context 0), even when it was optimized inside a local context (i.e., under
--        hypotheses introduced by an implication, a `dite` branch, a `match` alternative, ...).
--        A rewrite only valid under the local hypotheses (e.g., `f 0 = true ∧ g 0 = true ↔ g 0 = true`
--        reduces to `True` under `f 0 = true`) therefore leaked into the parent and global contexts:
--        `no_fvar_mvar_local_rewriting_cex` below was wrongly declared `Valid`.
--
-- Diagnosis: `isInOptimizeEnvCache` forced `isGlobal := true` for expressions without FVar/MVar and
--            `updateOptimizeEnvCache` stored unchanged expressions without FVar in the global cache.
-- Modifications: the rewrite cache to use is now only determined by the current context: the global
--                cache is used iff `curCtx == 0`, regardless of the free variables of the expression.
--
-- NOTE: `A ↔ B` is normalized to `(B → A) ∧ (A → B)`, `a = true ∧ b = true` to `true = (a && b)`
--       and `a = true ∨ b = true` to `true = (a || b)`.

set_option warn.sorry false

axiom f : Nat → Bool
axiom g : Nat → Bool
axiom h : Nat → Nat
axiom p : Nat → Prop

/-! ## Original example: local rewrite leaking into the global (parent) context -/

def no_fvar_mvar_local_rewriting_cex :=
    (f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
    ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)

-- the implication is `True` under its hypothesis, the second conjunct must be left untouched
#testOptimize ["LocalRewriteNotInGlobal"] (norm-result: 1)
  no_fvar_mvar_local_rewriting_cex ===>
  (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [no_fvar_mvar_local_rewriting_cex]

-- same with the global occurrence optimized (and cached in the global context) first
def global_first_then_local_cex :=
    ((f 0 = true ∧ g 0 = true) ↔ g 0 = true) ∧
    (f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true))

-- the global cache entry must not prevent the local rewrite to `True`
#testOptimize ["GlobalRewriteNotInLocal"] (norm-result: 1)
  global_first_then_local_cex ===>
  (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [global_first_then_local_cex]

/-! ## Local rewrite leaking into a sibling local context -/

-- different hypotheses on the same expression in two sibling contexts
def sibling_ctx_cex :=
    (f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
    (g 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true))

#testOptimize ["LocalRewriteNotInSibling"] (norm-result: 1)
  sibling_ctx_cex ===> (true = g 0 → true = f 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [sibling_ctx_cex]

-- sibling contexts through the equality map (`h 0 := 3` vs `h 0 := 5`)
def sibling_eq_ctx_cex :=
    (h 0 = 3 → h 0 + 1 = 4) ∧
    (h 0 = 5 → h 0 + 1 = 4)

#testOptimize ["LocalEqRewriteNotInSibling"] (norm-result: 1)
  sibling_eq_ctx_cex ===> ¬ (5 = h 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [sibling_eq_ctx_cex]

-- same hypothesis in both siblings: each context must recompute (and obtain) the same rewrite
theorem sibling_ctx_same_hyp :
    (f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
    (f 0 = true → (¬ (f 0 = true ∧ g 0 = true) ↔ ¬ g 0 = true)) := by blaster

theorem sibling_eq_ctx_same_hyp :
    (h 0 = 3 → h 0 + 1 = 4) ∧
    (h 0 = 3 → h 0 * 2 = 6) := by blaster

/-! ## Local rewrite leaking into a (local) parent context -/

-- the inner implication is optimized in a child context of the `p 1` context
def nested_ctx_cex :=
    p 1 → ((f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
           ((f 0 = true ∧ g 0 = true) ↔ g 0 = true))

#testOptimize ["LocalRewriteNotInParent"] (norm-result: 1)
  nested_ctx_cex ===>
  p 1 → (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [nested_ctx_cex]

def nested_eq_ctx_cex :=
    p 1 → ((h 0 = 3 → h 0 + 1 = 4) ∧ h 0 + 1 = 4)

#testOptimize ["LocalEqRewriteNotInParent"] (norm-result: 1)
  nested_eq_ctx_cex ===> p 1 → 3 = h 0

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [nested_eq_ctx_cex]

/-! ## Local rewrite properly reused within its own context and recomputed in child contexts -/

-- `f 0 = true ∧ g 0 = true` is rewritten once and reused for the second occurrence of the same context
theorem reuse_in_same_ctx :
    f 0 = true → (((f 0 = true ∧ g 0 = true) ↔ g 0 = true) ∧
                  (¬ (f 0 = true ∧ g 0 = true) ↔ ¬ g 0 = true)) := by blaster

theorem reuse_eq_in_same_ctx :
    h 0 = 3 → (h 0 + 1 = 4 ∧ h 0 * 2 = 6 ∧ (h 0 + 1) * 2 = 8) := by blaster

-- hypotheses of the parent context are visible in the child context: the child context has its own
-- rewrite cache but must obtain the same rewrite
theorem reuse_in_child_ctx :
    f 0 = true → (((f 0 = true ∧ g 0 = true) ↔ g 0 = true) ∧
                  (p 1 → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true))) := by blaster

theorem reuse_eq_in_child_ctx :
    h 0 = 3 → (h 0 + 1 = 4 ∧ (p 1 → h 0 + 1 = 4)) := by blaster

-- the child context adds a hypothesis: the parent rewrite must not be overwritten by the child one
def child_ctx_overrides_cex :=
    g 0 = true → (((f 0 = true ∧ g 0 = true) ↔ f 0 = true) ∧
                  (f 0 = true → ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
                  ((f 0 = true ∧ g 0 = true) ↔ g 0 = true))

#testOptimize ["ChildRewriteNotInParent"] (norm-result: 1)
  child_ctx_overrides_cex ===> true = g 0 → true = f 0

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [child_ctx_overrides_cex]

/-! ## Local contexts introduced by `dite` branches -/

def dite_then_ctx_cex :=
    (if f 0 = true then ((f 0 = true ∧ g 0 = true) ↔ g 0 = true) else True) ∧
    ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)

#testOptimize ["DiteThenRewriteNotInParent"] (norm-result: 1)
  dite_then_ctx_cex ===>
  (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [dite_then_ctx_cex]

def dite_else_ctx_cex :=
    (if f 0 = true then True else ((f 0 = true ∨ g 0 = true) ↔ g 0 = true)) ∧
    ((f 0 = true ∨ g 0 = true) ↔ g 0 = true)

#testOptimize ["DiteElseRewriteNotInParent"] (norm-result: 1)
  dite_else_ctx_cex ===> (true = (f 0 || g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [dite_else_ctx_cex]

-- the `then` branch rewrite (`f 0 = true` holds) must not be reused in the `else` branch
def dite_then_else_ctx_cex :=
    if f 0 = true
    then ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)
    else ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)

#testOptimize ["DiteThenRewriteNotInElse"] (norm-result: 1)
  dite_then_else_ctx_cex ===> (false = f 0 → false = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [dite_then_else_ctx_cex]

theorem dite_both_branches_valid :
    (if f 0 = true
     then ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)
     else ((f 0 = true ∨ g 0 = true) ↔ g 0 = true)) := by blaster

/-! ## Local contexts introduced by `match` alternatives -/

def match_ctx_cex :=
    (match f 0 with
     | true => ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)
     | false => True) ∧
    ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)

#testOptimize ["MatchAltRewriteNotInParent"] (norm-result: 1)
  match_ctx_cex ===>
  (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [match_ctx_cex]

def match_eq_ctx_cex :=
    (match h 0 with
     | 3 => h 0 + 1 = 4
     | _ => True) ∧
    h 0 + 1 = 4

#testOptimize ["MatchAltEqRewriteNotInParent"] (norm-result: 1)
  match_eq_ctx_cex ===> 3 = h 0

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [match_eq_ctx_cex]

-- the first alternative rewrite (`h 0 := 3`) must not be reused in the second alternative
def match_alt_ctx_cex :=
    match h 0 with
    | 3 => h 0 + 1 = 4
    | _ => h 0 + 1 = 4

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [match_alt_ctx_cex]

theorem match_alts_valid :
    (match h 0 with
     | 3 => h 0 + 1 = 4
     | 5 => h 0 + 1 = 6
     | _ => True) := by blaster

/-! ## Local contexts introduced by negated hypotheses and binders -/

def neg_hyp_ctx_cex :=
    (¬ f 0 = true → ((f 0 = true ∨ g 0 = true) ↔ g 0 = true)) ∧
    ((f 0 = true ∨ g 0 = true) ↔ g 0 = true)

#testOptimize ["NegHypRewriteNotInParent"] (norm-result: 1)
  neg_hyp_ctx_cex ===> (true = (f 0 || g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [neg_hyp_ctx_cex]

-- the hypothesis is introduced under a `∀` binder, the rewritten expression does not mention it
def forall_ctx_cex :=
    (∀ n : Nat, f 0 = true → n = n ∧ ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)) ∧
    ((f 0 = true ∧ g 0 = true) ↔ g 0 = true)

#testOptimize ["ForallHypRewriteNotInParent"] (norm-result: 1)
  forall_ctx_cex ===>
  (true = g 0 → true = f 0) ∧ (true = (f 0 && g 0) → true = g 0)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [forall_ctx_cex]

end Tests.Issue348
