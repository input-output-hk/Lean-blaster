import Lean
import Blaster

namespace Test.SmtRecFun

/-! ## Test objectives to validate recursive functions Smt lib translation -/


#blaster [ ∀ (x : Nat) (xs : List Nat), List.length xs + 1 = List.length (x :: xs) ]

#blaster [ ∀ (α : Type) (x : α) (xs : List α), List.length xs + 1 = List.length (x :: xs) ]

#blaster [ ∀ (s1 s2 : String), String.length s1 + String.length s2 = String.length (String.append s1 s2) ]

-- NOTE: remove induction when supporting implicit induction
set_option warn.sorry false in
theorem length_append {as bs : List α} : (as ++ bs).length = as.length + bs.length := by
 induction as <;> simp <;> blaster

/-! ## Test objectives to validate mutually recursive functions Smt lib translation -/

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end

#blaster [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

-- NOTE: remove solver options when induction schema supported
#blaster [ ∀ (n : Nat), isEven (n+2) → isEven n ]

mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

mutual
def A.sizeA : A → Nat
  | .self a => a.sizeA + 1
  | .other b => b.sizeB + 1
  | .empty => 0

def B.sizeB : B → Nat
  | .self b => b.sizeB + 1
  | .other a => a.sizeA + 1
  | .empty => 0
end

set_option warn.sorry false in
theorem A_self_size (a : A) : (A.self a).sizeA = a.sizeA + 1 := by blaster


/-! # Test cases to ensure that counterexample are properly detected -/

#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (x : Nat) (xs : List Nat), List.length xs + 2 = List.length (x :: xs) ]

#blaster (gen-cex: 0) (solve-result: 1)
  [ ∀ (s1 s2 : String), String.length s1 + String.length s2 > String.length (String.append s1 s2) ]

#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+1) = ¬ isOdd n ]

#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+2) → ¬ isEven n ]

end Test.SmtRecFun
