import Blaster

namespace Test.SmtListReplicate

/-! ## Test objectives to validate `List.replicate` optimization and constant propagation rules -/

/-! # Test cases to validate optimization and constant propagation rules -/

set_option warn.sorry false

example : List.replicate 0 "s" = [] := by blaster (only-optimize: 1)
example : List.replicate 0 1 = [] := by blaster (only-optimize: 1)
example : List.replicate 1 "s" = ["s"] := by blaster (only-optimize: 1)
example : List.replicate 2 "s" = ["s", "s"] := by blaster (only-optimize: 1)
example : List.replicate 5 "s" = ["s", "s", "s", "s", "s"] := by blaster (only-optimize: 1)
example : List.replicate 5 100 = [100, 100, 100, 100, 100] := by blaster (only-optimize: 1)
example : List.replicate 5 "aaa" = ["aaa", "aaa", "aaa", "aaa", "aaa"] := by blaster (only-optimize: 1)

example : ∀ (n : Nat) (x : α), (List.replicate n x).length = n := by
  intro n x
  induction n <;> blaster

example [DecidableEq α] : ∀ (n : Nat) (x : α), List.all (List.replicate n x) (λ (e : α) => e = x)  := by
  intro n x
  induction n <;> blaster

/-! # Test cases to ensure that counterexample are properly detected -/

def cex_1 : Prop := List.replicate 0 "s" = ["s"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_1]

def cex_2 : Prop := List.replicate 1 "s" = []
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_2]

def cex_3 : Prop := List.replicate 2 "s" = ["s", "s", "s"]
#blaster (gen-cex: 0) (solve-result: 1) (only-optimize: 1) [cex_3]


end Test.SmtListReplicate
