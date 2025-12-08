import Lean
import Blaster

namespace Tests.Issue10

-- Issue: Unexpected counterexample
-- Diagnosis: Need to guarantee unique names for quantified variables, pattern named
-- and pattern matched variables to avoid variable scoping at smt level

inductive NormalizedAction where
  | NormalizedSC : Int → Int → NormalizedAction
  | NormalizedRC : Int → Int → NormalizedAction
  | NormalizedDoubleSell : Int → Int → NormalizedAction
  | NormalizedDoubleBuy : Int → Int → Int -> NormalizedAction

def getBuySCTokens (x : NormalizedAction) : Option Int :=
  match x with
  | .NormalizedSC n _ => some n
  | _ => none

def validAction (x : NormalizedAction) : Prop :=
  match x with
  | .NormalizedSC n p
  | .NormalizedRC n p => (n < 0 ∧ p = 0) ∨ (n > 0 ∧ p > 0)
  | .NormalizedDoubleSell n m => n < 0 ∧ m < 0
  | .NormalizedDoubleBuy m n p => m > 0 ∧ n > 0 ∧ p > 0

#blaster [∀ (x : NormalizedAction) (n : Int),
          validAction x →
          some n = getBuySCTokens x →
          n ≠ 0
       ]

end Tests.Issue10
