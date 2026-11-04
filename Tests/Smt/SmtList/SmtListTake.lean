import Blaster

namespace Test.SmtListTake

/-! ## Test objectives to validate `List.take` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : List.take 10 ([] : List Nat) = [] := by blaster (only-optimize: 1)
example : List.take 0 ([] : List Nat) = [] := by blaster (only-optimize: 1)
example : List.take 4 ["aa", "bb", "cc", "dd", "ee"] = ["aa", "bb", "cc", "dd"] := by blaster (only-optimize: 1)
example : List.take 5 ["aa", "bb", "cc", "dd", "ee"] = ["aa", "bb", "cc", "dd", "ee"] := by blaster (only-optimize: 1)
example : List.take 15 ["aa", "bb", "cc", "dd", "ee"] = ["aa", "bb", "cc", "dd", "ee"] := by blaster (only-optimize: 1)
example : List.take 0 ["aa", "bb", "cc", "dd", "ee"] = [] := by blaster (only-optimize: 1)

example : ∀ (xs : List α) (n : Nat), n ≥ xs.length → List.take n xs = xs := by
  intro xs n
  induction n generalizing xs
  . cases xs <;> blaster
  . blaster

example : ∀ (xs : List α) (n : Nat), n < xs.length → (List.take n xs).length = n := by
  intro xs n
  induction n generalizing xs <;> blaster

example : ∀ (xs : List α) (n : Nat), n < xs.length → List.take n xs ++ (List.drop n xs) = xs := by
  intro xs n
  induction n generalizing xs <;> blaster

/-! # Test cases to ensure that counterexample are properly detected -/

def cex_1 : Prop := List.take 0 ([] : List Nat) = [1]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := List.take 4 ["aa", "bb", "cc", "dd", "ee"] = ["aa", "bb", "cc"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := List.take 0 ["aa", "bb", "cc", "dd", "ee"] = ["aa", "bb", "cc", "dd", "ee"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]

def cex_4 : Prop := List.take 10 ["aa", "bb", "cc", "dd", "ee"] = []
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_4]

end Test.SmtListTake
