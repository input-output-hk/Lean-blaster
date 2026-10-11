import Lean
import Blaster


-- Issue: Unexpected counterexample on existential quantifier
-- Diagnosis: Predicate qualifier was only declared and not constraint to always evaluate to true.

namespace Tests.Issue17


theorem exist_bool_true : ∃ p : Bool, p := by simp

#blaster [exist_bool_true]


inductive NatGroup where
 | first (n : Nat) (h1 : n ≥ 10) (h2 : n < 100): NatGroup
 | second (n : Nat) (h1 : n > 100) (h2 : n < 200) : NatGroup
 | next (n : NatGroup)


def sizeOfNatGroup (x : NatGroup) : Nat :=
  match x with
  | .first n _ _ => n
  | .second n _ _ => n
  | .next ng => 1 + sizeOfNatGroup ng

#blaster [∃ (x : NatGroup), sizeOfNatGroup x ≥ 10]

#blaster [∃ (x : NatGroup), sizeOfNatGroup x > 100]

#blaster [∃ (x : NatGroup), sizeOfNatGroup x > 200]

#blaster [∃ (x : NatGroup), sizeOfNatGroup x < 20]

-- Expecting a counterexample
-- Remove solver options when supporting proof by induction
#blaster (timeout: 2) (solve-result: 2) [∃ (x : NatGroup), sizeOfNatGroup x < 10]


end Tests.Issue17
