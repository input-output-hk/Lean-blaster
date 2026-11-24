import Blaster

namespace Tests.Issue152

-- Issues:
--  - https://github.com/input-output-hk/Lean-blaster/issues/152
-- Diagnosis: Recursion occurring in a lambda passed as argument will trigger a translation error as the current recursive
--            function is yet to be defined.
-- Modifications: Apply the same technique like what is used to generate predicate qualifier, i.e.,
--                using assertions to specify recursive functions. This breaks cyclic dependency during translation.

set_option warn.sorry false

inductive Tree where
  | leaf : Int → Tree
  | node : List Tree → Tree


mutual

def fold (xs : List Tree) (acc : String) : Option String :=
  match xs with
  | [] => some acc
  | a :: as =>
      match enc a with
      | some s => fold as (acc ++ s)
      | none => none

def enc : Tree → Option String
  | .leaf _ => .some "i"
  | .node xs => fold xs ""

end

theorem enc_nil : enc (.node []) = some "" := by blaster

def encFoldM : Tree → Option String
  | .leaf _ => .some "i"
  | .node xs => List.foldlM (fun s a => do .some (s ++ (← encFoldM a))) "" xs
  decreasing_by
    have : sizeOf a < sizeOf xs := by apply List.sizeOf_lt_of_mem; assumption
    simp; omega

theorem enc_nil_foldM : encFoldM (.node []) = some "" := by blaster

end Tests.Issue152
