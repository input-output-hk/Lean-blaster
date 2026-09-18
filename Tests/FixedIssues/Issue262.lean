import Blaster

namespace Tests.Issue262

-- Issues:
--  - https://github.com/input-output-hk/Lean-blaster/issues/262
-- Diagnosis:
--   - Inductive datatypes with no constructors should be represented as abstract sort at the smtlib level
--     and should not admit any element.
--   - Axiom and Opaque type should be resolved and handled as typical sort types.


set_option warn.sorry false

inductive DigestOne : Type
axiom digestOneSize : DigestOne → Int

-- Valid expected as does not have any Inhabited/NonEmpty instance
example : ∀ (d : DigestOne), digestOneSize d > 0 := by blaster

-- Valid expected as does not have any Inhabited/NonEmpty instance
example : ∀ (_d : DigestOne), False := by blaster

inductive DigestTwo : Type

axiom digestTwoSize : DigestTwo → Int

-- Valid expected even with Nonempty constraint. Indeed, DigestTwo does not have any constructor
example [Nonempty DigestTwo] : ∀ (d : DigestTwo), digestTwoSize d > 0 := by blaster

-- Valid expected even with Inhabited constraint. Indeed, DigestTwo does not have any constructor
example [Inhabited DigestTwo] : ∀ (d : DigestTwo), digestTwoSize d > 0 := by blaster

def newLength (l : List DigestOne) : Nat :=
  match l with
  | [] => 0
  | _ :: [ ] => 0
  | _ :: _ :: [] => 0
  | _ => l.length

-- Theorem can be proved in Lean4 even though newLength and length are not equivalent
-- as DigestOne is no habited
theorem newLength_eq_length : ∀ (xs : List DigestOne), newLength xs = xs.length := by
  intro xs
  cases xs with
  | nil => simp [newLength]
  | cons x xs => nomatch x

-- Valid expected by Blaster
#blaster [newLength_eq_length]

-- Theorem can be proved in Lean4 even though the accumulation can be negative as DigestOne is no habited
theorem foldr_valid : ∀ (xs : List DigestOne) (f : DigestOne → Int), xs.foldr (λ a acc => f a + acc) 0 ≥ 0 := by
  intro xs
  cases xs with
  | nil => simp
  | cons x xs => nomatch x

-- Valid expected by Blaster
#blaster [foldr_valid]

def foldr_cex := ∀ (xs : List DigestOne) (f : DigestOne → Int), xs.foldr (λ a acc => f a + acc) 0 > 0
-- Counterexample expected by Blaster as nil case returns zero
#blaster (gen-cex: 0) (solve-result: 1) [foldr_cex]

axiom DigestThree : Type
axiom digestThreeSize : DigestThree → Int

def example_axiom_cex := ∀ (d : DigestThree), digestThreeSize d > 0
#blaster (gen-cex: 0) (solve-result: 1) [example_axiom_cex]

opaque DigestFour : Type
axiom digestFourSize : DigestFour → Int

def example_opaque_cex :=  ∀ (d : DigestFour), digestFourSize d > 0
#blaster (gen-cex: 0) (solve-result: 1) [example_opaque_cex]

end Tests.Issue262
