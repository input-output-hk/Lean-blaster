import Blaster
import Tests.Proof.Support

/-!
# Functional induction on list programs

`blaster (induction: auto)` on goals without a machine run: functional
induction on the recursive definitions, with recursive calls uninterpreted at
the leaves. Insertion sort is proved to sort in two steps: insertion into a
sorted list keeps it sorted (by induction), and the sort is sorted given that
fact as a summary. A false claim is rejected, and the library attribute
admits only theorems proved by Blaster.
-/

namespace Tests.Lists

/-- Insert into a list sorted in ascending order. -/
def insert (y : Int) : List Int → List Int
  | [] => [y]
  | x :: xs => if y ≤ x then y :: x :: xs else x :: insert y xs

def sorted : List Int → Bool
  | x :: y :: rest => x ≤ y && sorted (y :: rest)
  | _ => true

def isort : List Int → List Int
  | [] => []
  | x :: xs => insert x (isort xs)

end Tests.Lists

set_option maxHeartbeats 0
open Tests.Lists

@[blaster_library] theorem Tests.Lists.insert_sorted (y : Int) (xs : List Int) :
    sorted xs = true → sorted (insert y xs) = true := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

theorem Tests.Lists.isort_sorted (xs : List Int) : sorted (isort xs) = true := by
  blaster (induction: auto) (summaries: [insert_sorted]) (timeout: 10) (gen-cex: 0)

-- False without its premise: `insert 3 [2, 1] = [2, 1, 3]` is not sorted.
#reject "could not prove the goal" in
theorem Tests.Lists.insert_sorted_always (y : Int) (xs : List Int) :
    sorted (insert y xs) = true := by
  blaster (induction: auto) (timeout: 10) (gen-cex: 0)

-- Library facts must be Blaster's own proofs.
/-- error: blaster_library facts must be proved by blaster: Tests.Lists.length_singleton -/
#guard_msgs in
@[blaster_library] theorem Tests.Lists.length_singleton (y : Int) : [y].length = 1 := rfl

#print axioms Tests.Lists.insert_sorted
#print axioms Tests.Lists.isort_sorted
