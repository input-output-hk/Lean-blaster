import Tests.Utils

namespace Tests.NestedConstructor

inductive Box where
  | list : List Nat → Box
  | other : Nat → Box

def work : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => work n (acc + 1)

def select : Box → Nat
  | .list [] => 0
  | .list (n :: _) => n
  | .other _ => work 1000000 0

-- The outer constructor is known, but the nested list constructor is not.
-- Optimizing the impossible .other branch would unfold a million recursive steps.
#testOptimize ["NestedConstructor_unknown_list"]
  ∀ xs : List Nat, select (.list xs) = (List.casesOn xs 0 (fun n _ => n)) ===> True

#testOptimize ["NestedConstructor_distinct_calls"]
  ∀ xs ys : List Nat, select (.list xs) = (List.casesOn xs 0 (fun n _ => n)) ∧
    select (.list ys) = (List.casesOn ys 0 (fun n _ => n)) ===> True

example (xs : List Nat) :
    select (.list xs) = (match xs with | [] => 0 | n :: _ => n) := by
  cases xs <;> rfl

-- A reachable branch still affects the result.
#testOptimize ["NestedConstructor_negative_control"] (norm-result: 1)
  ∀ n : Nat, select (.list [n]) = 0 ===> ∀ n : Nat, 0 = n

inductive Payload (α : Type) where
  | list : List α → Payload α
  | other : Payload α

def first : Payload α → Option α
  | .list [] => none
  | .list (x :: _) => some x
  | .other => none

#testOptimize ["NestedConstructor_polymorphic_fields"]
  ∀ (α : Type) (xs : List α), first (.list xs) =
    List.casesOn (motive := fun _ => Option α) xs none (fun x _ => some x) ===> True

example (xs : List α) : first (.list xs) =
    List.casesOn (motive := fun _ => Option α) xs none (fun x _ => some x) := by
  cases xs <;> rfl

end Tests.NestedConstructor
