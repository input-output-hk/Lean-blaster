import Lean
import Blaster

namespace Test.SmtRecFun

/-! ## Test objectives to validate recursive functions Smt lib translation -/

#blaster [ ∀ (x : Nat) (xs : List Nat), List.length xs + 1 = List.length (x :: xs) ]

-- #blaster [ ∀ (α : Type) (x : α) (xs : List α), List.length xs + 1 = List.length (x :: xs) ]

#blaster [ ∀ (s1 s2 : String), String.length s1 + String.length s2 = String.length (String.append s1 s2) ]

-- NOTE: remove induction when supporting implicit induction
set_option warn.sorry false in
theorem length_append {as bs : List α} : (as ++ bs).length = as.length + bs.length := by
 induction as <;> blaster


/-! ## Test objectives to validate mutually recursive functions Smt lib translation -/

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end

#blaster (only-optimize: 1) [ ∀ (n : Nat), isEven (n+1) = isOdd n ]

#blaster (only-optimize: 1) [ ∀ (n : Nat), isEven (n+2) → isEven n ]

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

#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+1) = ¬ isOdd n ]

#blaster (gen-cex: 0) (solve-result: 1) [ ∀ (n : Nat), isEven (n+2) → ¬ isEven n ]

def mylen {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + mylen xs

#blaster [∀ (α : Type) (g : (List α → Nat) → Nat), g (fun l => mylen l) = g (@mylen α)]

#blaster [∀ (α : Type) (g : (List α → Nat) → Nat) (l : List α), mylen l = 0 → g (@mylen α) = g (fun x => mylen x)]

#blaster [∀ (α : Type) (g : (List α → Nat) → Nat), g (@mylen α) = g (fun l => mylen l)]

def mysum {α : Type} [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + mysum xs

#blaster [∀ (g : (List Nat → Nat) → Nat), g (@mysum Nat _ _) = g (fun l => mysum l)]

end Test.SmtRecFun
