import Lean
import Solver.Command.Syntax

namespace Tests.Issue6

-- Issue: translateApp: unexpected application constNatGroup.proof_1
-- Diagnosis : Need to handle embedded theorems during translation
--             Note that we only support embedded theorems with full demonstration
--             (i.e., no sorry demonstration).

theorem and_imp_right {p q : Prop} (h : p ∧ q) : p := by
  cases h; assumption

theorem and_imp_left {p q : Prop} (h : p ∧ q) : q := by
  cases h; assumption

inductive NatGroup where
 | first (n : Nat) (h1 : n ≥ 10) (h2 : n < 100): NatGroup
 | second (n : Nat) (h1 : n > 100) (h2 : n < 200) : NatGroup
 | next (n : NatGroup)

def constrNatGroup (n : Nat) : NatGroup :=
 if h1 : n ≥ 10 ∧ n < 100
 then NatGroup.first n (and_imp_right h1) (and_imp_left h1)
 else if h2 : n > 100 ∧ n < 200
      then NatGroup.second n (and_imp_right h2) (and_imp_left h2)
      else NatGroup.next (NatGroup.first 10 (by decide) (by decide))

def isFirst (x : NatGroup) : Bool :=
  match x with
  | .first .. => Bool.true
  | _ => Bool.false

def toFirst (x : NatGroup) : Nat :=
  match x with
  | .first n _ _ => n
  | _ => 0

#solve [∀ (x : Nat),
          let c := constrNatGroup x;
          isFirst c →
          let r := toFirst c;
          r ≥ 10 ∧ r < 100]

end Tests.Issue6
