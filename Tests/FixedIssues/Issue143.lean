import Blaster

namespace Tests.Issue143

-- Issues:
--  - https://github.com/input-output-hk/Lean-blaster/issues/143
-- Diagnosis: The translation of mutually recursive functions wrongly assumes that the mutually recursive functions
--            will have the same number of effective arguments.
-- Modifications: Apply the same technique like what is used to generate predicate qualifier, i.e.,
--                using assertions to specify recursive functions. This breaks cyclic dependency during translation.


set_option warn.sorry false

inductive Data where
 | Constr : Int → List Data → Data
 | List : List Data → Data
 | I : Int → Data
 | B : String → Data

mutual
  def eqData : Data → Data → Bool
    | .Constr i args, .Constr i' args' => eqDataConstr i args i' args'
    | .List l, .List l' => eqDataList l l'
    | .I i, .I i' => i == i'
    | .B b, .B b' => b == b'
    | _ , _ => false

  def eqDataList : List Data → List Data → Bool
    | [] , [] => true
    | x :: xs, y :: ys => eqData x y && eqDataList xs ys
    | _ , _ => false

  def eqDataConstr : Int → List Data → Int → List Data → Bool
    | i , args , i' , args' => (i == i') && eqDataList args args'
end

def example_cex := ∀ (i j : Nat) (xs ys : List Data), eqData (.Constr i xs) (.Constr (Int.ofNat j) [.List ys])

#blaster (gen-cex: 0) (solve-result: 1) [example_cex]

example : ∀ (i j : Nat) (ys : List Data), eqData (.Constr i []) (.Constr j ys) → i = j ∧ [] = ys := by blaster

example : ∀ (ys : List Data), eqDataList [] ys → [] = ys := by blaster


/-! Test cases to validate new recursive function smt translation and to show that
    the recfun_finder option we added to z3 must be set to obtain the expected counterexample.
    Otherwise, the MBQI instantiation does not terminate.
-/

def rec_encode_example_1 := ∀ (xs : List Int), xs.length < 3
#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_1]

mutual
 def isEven (n : Int) : Bool := if n ≤ 0 then true else isOdd (n - 1)
 termination_by n.toNat
  decreasing_by
    simp_wf
    omega

 def isOdd (n : Int) : Bool := if n ≤ 0 then false else isEven (n - 1)
 termination_by n.toNat
  decreasing_by
    simp_wf
    omega
end

def rec_encode_example_2 := ∀ (k : Int), isEven k → k > 0
#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_2]


mutual
inductive DTree where
  | children : Forest → DTree

inductive Forest where
  | nil : Forest
  | cons : DTree → Forest → Forest
end

mutual
 def sizeT (t : DTree) : Int :=
  match t with
  | .children f => 1 + sizeF f

 def sizeF (f : Forest) : Int :=
   match f with
   | .nil => 0
   | .cons t f' => sizeT t + sizeF f'
end

def rec_encode_example_3 := ∀ (t : DTree), sizeT t < 5

#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_3]

def decr (x : Int) : Int :=
  if x ≤ 0 then 0
  else if (decr (x - 1) = 0) then 1
  else 1 + decr (x - 1)
termination_by x.toNat
decreasing_by
  all_goals omega

def rec_encode_example_4 := ∀ (n : Int), n ≥ 0 → decr n < 3
#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_4]

def decr_k (x : Int) : Int :=
  if x ≤ 0 then 0
  else if decr_k (x - 1) = 0 then 1
  else 2
termination_by x.toNat
decreasing_by all_goals omega

theorem decr_k_lt_three : ∀ (n : Int), decr_k n < 3 := by blaster

def decr_g (x : Int) : Int :=
  if x ≤ 0 then 0
  else if decr_g (x - 1) > 5 then decr_g (x - 1) - 1
  else decr_g (x - 1) + 2
termination_by x.toNat
decreasing_by
  all_goals omega

def rec_encode_example_5 := ∀ (n : Int), n ≥ 0 → decr_g n < 6

#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_5]

def decr_f (x : Int) : Int :=
  if x ≤ 0 then 0
  else if decr_f (x - 1) = 0 then 1 else 1 + decr_f (x - 1)
termination_by x.toNat
decreasing_by
  all_goals omega

def rec_encode_example_6 := ∀ (n : Int), n ≥ 0 → decr_f n < 3
#blaster (gen-cex: 0) (solve-result: 1) [rec_encode_example_6]


end Tests.Issue143
