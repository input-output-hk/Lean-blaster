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

-- Can be proved as DigestOne does not admit any element
theorem empty_ind_1 : ∀ (d : DigestOne), digestOneSize d > 0 := by
  intro d
  cases d

-- Valid expected by Blaster
#blaster [empty_ind_1]

-- Can be proved as DigestOne does not admit any element
theorem empty_ind_2 : ∀ (_d : DigestOne), False := by
  intro d
  cases d

-- Valid expected by Blaster
#blaster [empty_ind_2]

inductive DigestTwo : Type

axiom digestTwoSize : DigestTwo → Int

-- Can be proved even with Nonempty constraint as DigestTwo does not admit any element
theorem empty_ind_3 (d : DigestTwo) (_h : Nonempty DigestTwo) : digestTwoSize d > 0 := by cases d

-- Valid expected by Blaster
#blaster [empty_ind_3]

-- Can be proved even with Inhabited constraint as DigestTwo does not admit any element
theorem empty_ind_4 (d : DigestTwo) (_h : Inhabited DigestTwo) : digestTwoSize d > 0 := by cases d

-- Valid expected by Blaster
#blaster [empty_ind_4]


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


inductive E : Type
opaque f (x : E) : E := x

def example_undecl_fun_cex_1 := ∀ (n : Nat), n = 0 ∧ (∀ e : E, f e = e)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [example_undecl_fun_cex_1]

inductive P (α : Type u) where
  | Node : α → P α

axiom g : Nat → P E

-- Can be proved as g does not admit any instance
theorem empty_fun_1 : ∀ (e : P E) (n : Nat), g n = e := nomatch g 0

-- Valid expected by Blaster
#blaster [empty_fun_1]

-- Can be proved as foo does not admit any instance
theorem empty_fun_2 : ∀ (e : P E) (n : Nat) (foo : Nat → P E), foo n = e := by
  intro e n foo
  cases e with
  | Node a => cases a

-- Valid expected by Blaster
#blaster [empty_fun_2]

theorem empty_fun_3 : ∀ (n : Nat), n = 0 ∧ (∀ (e : P E) (x : Nat), g x = e) := by nomatch g 0

-- Valid expected by Blaster
#blaster [empty_fun_3]

axiom fg : P α

-- Can be proved as fg does not admit any instance
theorem empty_fun_4 : ∀ (e : P E), fg = e := nomatch fg

-- Valid expected by Blaster
-- NOTE: test to validate case when function only has implicit parameters as input
#blaster [empty_fun_4]

def example_undecl_fun_cex_2 := ∀ (α : Type) (x : P α), fg = x

-- Counterexample expected by Blaster
-- NOTE: test to validate case when function only has implicit parameters but instantiated
-- with polymorphic instance
#blaster (gen-cex: 0) (solve-result: 1) [example_undecl_fun_cex_2]

axiom gg : Nat → List E
def example_undecl_fun_cex_3 := ∀ (n : Nat), n = 0 ∧ (∀ (e : List E) (x : Nat), gg x = e)

-- Counterexample expected by Blaster, as gg admits the nil instance
#blaster (gen-cex: 0) (solve-result: 1) [example_undecl_fun_cex_3]

def example_undecl_fun_cex_4 := ∀ (n : Nat), n = 0 ∧ ∀ (e : E) (x : Nat) (foo : Nat → E), foo x = e

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [example_undecl_fun_cex_4]

-- Can be proved as foo does not admit any instance
theorem empty_fun_5 : ∀ (foo : Nat → E) (n : Nat), n = 0 ∧ ∀ (e : E) (x : Nat) , foo x = e := by
  intro foo n
  nomatch foo 0

-- Valid expected by Blaster
#blaster [empty_fun_5]

axiom DigestThree : Type
axiom digestThreeSize : DigestThree → Int

def example_axiom_cex := ∀ (d : DigestThree), digestThreeSize d > 0
#blaster (gen-cex: 0) (solve-result: 1) [example_axiom_cex]

opaque DigestFour : Type
axiom digestFourSize : DigestFour → Int

def example_opaque_cex :=  ∀ (d : DigestFour), digestFourSize d > 0
#blaster (gen-cex: 0) (solve-result: 1) [example_opaque_cex]


end Tests.Issue262
