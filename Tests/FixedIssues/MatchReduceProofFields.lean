import Lean
import Blaster
import Tests.Utils

namespace Tests.MatchReduceProofFields

-- Issue: reducing a `match` on a constructor with a proof field, e.g. `List.get`'s
--          | _ :: as, ⟨i+1, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩
--        - on a list with a symbolic tail, fails with
--            getMVarAssignment!: assignment expected for meta variable ...
--              : Nat.succ ?m < (?m :: ?m).length
--        - on a concrete list, leaves the `match` unreduced, with a `sorryAx` in it.
--
-- Diagnosis: `normProof` (OptimizeStack.lean) rebuilds a proof argument whose type no longer
--            matches syntactically after optimization (e.g., `Nat.succ i` became `Nat.add 1 i`),
--            and falls back to `sorry`. In the alternative's pattern this replaces the pattern
--            variable `h` itself, so `isPatternMatch` never assigns it, while the rhs still
--            refers to it: `instantiateUnifiedMVars` hands the unassigned mvar to `betaLambdaEnv`.
--            On a concrete list the match does not even unify: `isPatternMatch` compares the
--            parameter `n` of `@Fin.mk n v h` structurally (`Nat.add 1 (List.length ?as)` against
--            the literal `2`), though inductive parameters are not patterns.
--
-- Fix: `isPatternMatch` matches two applications of the same constructor field by field,
--      skipping the inductive's parameters and assigning (not comparing) proof fields; a proof
--      pattern variable still unassigned after `assignEqRefl` gets the proof `normProof` would
--      have built (`backwardProof`).

set_option warn.sorry false

def getOr (l : List Nat) (i : Nat) : Nat := if h : i < l.length then l.get ⟨i, h⟩ else 1

def getOrIdx (l : List Nat) (i : Nat) : Nat := if h : i < l.length then l[i] else 1

-- symbolic tail: used to fail with getMVarAssignment!
#testOptimize ["GetSymbolicTail"]
  ∀ (a : Nat) (l : List Nat), getOr (a :: l) 1 = getOr l 0 ===> True

#testOptimize ["GetElemSymbolicTail"]
  ∀ (a : Nat) (l : List Nat), getOrIdx (a :: l) 1 = getOrIdx l 0 ===> True

-- concrete list: used to stay a `match` containing `sorryAx`
#testOptimize ["GetConcreteList"]
  ∀ (a b : Nat), getOr [a, b] 1 = b ===> True

#testOptimize ["GetElemConcreteList"]
  ∀ (a b : Nat), getOrIdx [a, b] 1 = b ===> True

-- index 0 already worked; it must keep working
#testOptimize ["GetHead"]
  ∀ (a : Nat) (l : List Nat), getOr (a :: l) 0 = a ===> True

/-! The same through the `blaster` tactic and the `#blaster` command. A goal that keeps a
    `List.get` on a symbolic list cannot reach the solver (the smt translation does not support
    `Fin`), so the symbolic-tail cases below are those the optimizer closes. -/

-- closed by the optimizer once the match reduces
theorem get_symbolic_tail : ∀ (a : Nat) (l : List Nat), getOr (a :: l) 1 = getOr l 0 := by
  blaster

theorem getElem_symbolic_tail : ∀ (a : Nat) (l : List Nat), getOrIdx (a :: l) 1 = getOrIdx l 0 := by
  blaster

theorem get_concrete_list : ∀ (a b : Nat), getOr [a, b] 1 = b := by blaster

theorem getElem_concrete_list : ∀ (a b : Nat), getOrIdx [a, b] 1 = b := by blaster

theorem get_last_of_three : ∀ (a b c : Nat), getOr [a, b, c] 2 > b → c > b := by blaster

-- left to the solver once the match reduces (optimization alone leaves it undetermined)
theorem get_then_arith :
  ∀ (a b : Nat) (l : List Nat), b > 3 → getOr (a :: b :: l) 1 + a > a + 3 :=
    by blaster

#blaster [∀ (a : Nat) (l : List Nat), getOr (a :: l) 1 = getOr l 0]
#blaster [∀ (a b c : Nat), getOr [a, b, c] 2 > b → c > b]

-- must be falsified, not merely undetermined
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : Nat), getOr [a, b] 1 = a]
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b c : Nat), getOr [a, b, c] 2 > b]

end Tests.MatchReduceProofFields
