import Blaster

namespace Test.SmtListGet

/-! ## Test objectives to validate `List.get?Internal` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : ([] : List Nat)[0]? = none := by blaster (only-optimize: 1)
example : ([] : List Nat)[13]? = none := by blaster (only-optimize: 1)
example : ["aa", "bb", "cc", "dd", "ee"][4]? = some "ee" := by blaster (only-optimize: 1)
example : ["aa", "bb", "cc", "dd", "ee"][5]? = none := by blaster (only-optimize: 1)
example : ["aa", "bb", "cc", "dd", "ee"][0]? = some "aa" := by blaster (only-optimize: 1)

example : ∀ (n : Nat) (xs : List Nat), n < xs.length → xs[n]? ≠ none := by
  intro n xs
  induction xs generalizing n <;> blaster

example : ∀ (xs : List α), 10 ≥ xs.length → xs[10]? = none := by
  intro xs
  induction xs <;> blaster

example : ∀ (n : Nat) (xs : List α), n ≥ xs.length → xs[n]? = none := by
  intro n xs
  induction xs generalizing n
  . blaster
  . cases n <;> blaster

/-! # Test cases to ensure that counterexample are properly detected -/

def cex_1 : Prop := ([] : List Nat)[0]? = some 1
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := ["aa", "bb", "cc", "dd", "ee"][4]? = some "aa"
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := ["aa", "bb", "cc", "dd", "ee"][5]? = some "bb"
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]


end Test.SmtListGet
