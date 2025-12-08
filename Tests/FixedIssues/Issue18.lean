import Lean
import Blaster

-- Issue: getApplyInstName: declaration instance expected for Lean.Expr.forallE ...
-- Diagnosis: We need to generate predicate qualifier and congruence assertions
--            for any function type used in rec fun/lambda parameters.

namespace Tests.Issue18

#blaster (gen-cex: 0) (solve-result: 1)
       [ ∀ (xs : List Nat), !(List.isEmpty xs) → List.head! (List.map Int.ofNat xs) ≥ 10 ]

#blaster [ ∀ (x : Nat) (xs : List Nat), !(List.isEmpty xs) → List.head! (List.map (Nat.add x) xs) ≥ x ]

#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (xs : List Nat) (f : List Nat → Nat) (c : Bool), f xs < 10 → (if c then f else List.length) xs < 10 ]

#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (xs : List (List Nat)), !(List.isEmpty xs) → List.head! (List.map List.length xs) < 0 ]

def addOptionList (x : Option Nat) (xs : List Nat) : List Nat :=
  match x with
  | none => xs
  | some x' => List.map (Nat.add x') xs

#blaster [∀ (x : Option Nat) (xs : List Nat), !(List.isEmpty xs) → List.head! (addOptionList x xs)  ≥ x ]


def addOptionPoly [LE α] [DecidableLE α] (x : Option α) (xs : List α) : List α :=
  match x with
  | none => xs
  | some x' => List.map (λ y => if x' ≤ y then x' else y) xs


#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (α : Type) (x : Option α) (xs : List α),
          [LE α] → [DecidableLE α] → [Inhabited α] →
          !(List.isEmpty xs) → (List.head! (addOptionPoly x xs)) ≤ x
       ]

end Tests.Issue18
