import Lean
import Blaster

open Lean Meta
namespace Tests.Issue27

-- Issue:  (kernel) application type mismatch ...
-- Diagnosis: Before calling blaster we also need to revert quantifiers so as to properly normalize their types.
--            Note that is is now no more necessary as we are implicitly instantiating any
--            universe level meta variables.

set_option warn.sorry false
-- NOTE: remove induction when supporting implicit induction
theorem length_set {as : List α} {i : Nat} {a : α} : (as.set i a).length = as.length := by
 induction as generalizing i <;> blaster


end Tests.Issue27
