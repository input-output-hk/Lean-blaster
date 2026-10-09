import Blaster

namespace Test.SmtListLength

/-! ## Test objectives to validate `List.length` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : List.length ([] : List Nat) = 0 := by blaster (only-optimize: 1)
example : List.length ["aa", "bb", "cc", "dd", "ee"] = 5 := by blaster (only-optimize: 1)

example : ∀ (xs : List α), ¬ List.isEmpty xs → xs.length > 0 := by
  intro xs
  induction xs <;> blaster

/-! # Test cases to ensure that counterexample are properly detected -/

def cex_1 : Prop := List.length ([] : List Nat) = 2
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := List.length ["aa", "bb", "cc", "dd", "ee"] = 3
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := List.length ["aa", "bb", "cc", "dd", "ee"] = 0
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]

end Test.SmtListLength
