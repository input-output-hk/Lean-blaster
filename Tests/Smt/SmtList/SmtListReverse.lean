import Blaster

namespace Test.SmtListReverse

/-! ## Test objectives to validate `List.reverseAux` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : List.reverse ([] : List Nat) = [] := by blaster (only-optimize: 1)
example : List.reverse ["aa", "bb", "cc", "dd", "ee"] = ["ee", "dd", "cc", "bb", "aa" ] := by blaster (only-optimize: 1)
example : List.reverse (List.reverse ["aa", "bb", "cc", "dd", "ee"]) = ["aa", "bb", "cc", "dd", "ee"] := by blaster (only-optimize: 1)

example : ∀ (xs : List α), xs.isEmpty → List.reverse xs = [] := by blaster

example : ∀ (xs : List α), (List.reverse xs).length = xs.length := by
  intro xs
  induction xs
  . blaster
  . simp

/-! # Test cases to ensure that counterexample are properly detected -/

def cex_1 : Prop := List.reverse ([] : List Nat) = [1]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := List.reverse ["aa", "bb", "cc", "dd", "ee"] = ["ee", "aa", "bb", "cc" ]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := List.reverse ["aa", "bb", "cc", "dd", "ee"] = []
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]

end Test.SmtListReverse
