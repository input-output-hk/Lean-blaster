import Blaster

namespace Test.SmtListAppend

/-! ## Test objectives to validate `List.append` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : List.append ([] : List Nat) [] = [] := by blaster (only-optimize: 1)
example : List.append [] ["aa", "bb", "cc"] = ["aa", "bb", "cc"] := by blaster (only-optimize: 1)
example : List.append [] ["aa", "bb", "cc"] = List.append ["aa", "bb", "cc"] [] := by blaster (only-optimize: 1)
example : List.append ["ee", "ff"] ["aa", "bb", "cc"] = ["ee", "ff", "aa", "bb", "cc"] := by blaster (only-optimize: 1)

/-! # Test cases to ensure that counterexample are properly detected -/

example : ∀ (xs : List α), xs.isEmpty → (List.append [] xs) = [] := by blaster
example : ∀ (xs ys : List α), xs.isEmpty → (List.append xs ys) = ys := by blaster

example : ∀ (xs ys : List α), (List.append xs ys).length = xs.length + ys.length := by
  intro xs ys
  induction xs generalizing ys <;> blaster


def cex_1 : Prop := List.append ([] : List Nat) [] = [1]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := List.append ["aa", "bb", "cc", "dd", "ee"] [] = ["bb", "cc", "dd", "ee", "aa"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := List.append ["aa", "bb", "cc", "dd", "ee"] ["ee"] = ["aa", "bb", "cc", "dd", "ee"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]

end Test.SmtListAppend
