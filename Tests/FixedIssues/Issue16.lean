import Lean
import Blaster

-- Issue: Valid result when counterexample expected
-- Diagnosis : The use of Array type to model higher order function introduces unsound smt context.
--             We therefore introduces ArrowTx types with the necessary congruences constraints.
-- New Diagnosis : The theorems were wrongly formulated. Indeed, we can derive `false` from the hypothesis
--                 by providing (λ _ => 0) as instance for `f`.
--                 Use of Array type to represent HOF is sound provided that the isFun predicate is properly defined.

namespace Tests.Issue16

mutual
  inductive Attribute (α : Type u) where
  | Named (n : String)
  | Pattern (p : List (Term α))
  | Qid (n : String) (p : Except (Option (Term α)) (List (Attribute α)))

  inductive Term (α : Type u) where
  | Ident (s : String)
  | Seq (x : List α)
  | App (nm : String) (args : List (Term α))
  | Annotated (t : Term α) (annot : List (Attribute α))

end

def example_1 :=
  (∀ (x : Int) (f : Int → Nat), f x > 2) →
  (∀  (x y : Int) (f : Int → Nat), f x + f y > 10)

/-- Can be proved due to false hypothesis -/
example : example_1 := by
  simp [example_1]
  intro h1 x y
  have h2 := h1 x (λ _ => 0)
  simp at h2

-- Valid expected by Blaster
#blaster [example_1]


def example_2 :=
  (∀ (β : Type) (x : Term (List β)) (f : Term (List β) → Nat), f x > 0) →
  (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 20)

/-- Can be proved due to false hypothesis -/
example : example_2 := by
  simp [example_2]
  intro h1 α x y
  have h2 := h1 α x (λ _ => 0)
  simp at h2

-- Valid expected by Blaster
#blaster [example_2]

def example_3 :=
  (∀ (β : Type) (x : Term (List β)) (g : Term (List β) → Nat), g x > 10) →
  (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 30)


example : example_3 := by
  simp [example_3]
  intro h1 α x y
  have h2 := h1 α x (λ _ => 0)
  simp at h2

-- Valid expected by Blaster
#blaster [example_3]

def example_4 :=
  ∀ (f : Int → Nat), (∀ (x : Int), f x > 2) →
  ∀ (x y : Int), f x + f y > 10

#blaster (gen-cex: 0) (solve-result: 1) [example_4]

def example_5 :=
  ∀ (β : Type) (f : Term (List β) → Nat),
   (∀ (x : Term (List β)), f x > 0) →
   ∀ (x y : Term (List β)), f x + f y > 20

#blaster (gen-cex: 0) (solve-result: 1) [example_5]

end Tests.Issue16
