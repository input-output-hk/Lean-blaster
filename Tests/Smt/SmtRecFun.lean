import Lean
import Solver.Command.Syntax

namespace Test.SmtRecFun

/-! ## Test objectives to validate recursive functions Smt lib translation -/

#solve [ ∀ (x : Nat) (xs : List Nat), List.length xs + 1 = List.length (x :: xs) ]

#solve [ ∀ (α : Type) (x : α) (xs : List α), List.length xs + 1 = List.length (x :: xs) ]

#solve [ ∀ (s1 s2 : String), String.length s1 + String.length s2 = String.length (String.append s1 s2) ]


/-! ## Test objectives to validate mutually recursive functions Smt lib translation -/

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => ! isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => ! isEven n
end

#solve [ ∀ (n : Nat), isEven (n+1) = ¬ (isOdd n) ]

-- NOTE: remove solver options when induction schema supported
#solve (timeout: 5) (solve-result: 2) [ ∀ (n : Nat), isEven (n+2) → isEven n ]


/-! # Test cases to ensure that counterexample are properly detected -/

#solve (gen-cex: 0) (solve-result: 1)
  [ ∀ (x : Nat) (xs : List Nat), List.length xs + 2 = List.length (x :: xs) ]

#solve (gen-cex: 0) (solve-result: 1)
  [ ∀ (s1 s2 : String), String.length s1 + String.length s2 > String.length (String.append s1 s2) ]

#solve (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

#solve (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+2) → ¬ isEven n ]

end Test.SmtRecFun
