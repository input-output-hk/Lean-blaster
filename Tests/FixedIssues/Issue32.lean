import Lean
import Blaster

namespace Tests.Issue32

-- Issue: Unexpected smt error: (.. unknown constant @isTests.Issue32.Term._uniq.2392 ((@Tests.Issue30.Term (@List @@Type))) ")
-- Diagnosis : Predicate qualifier for single recursive datatype must still use limited call so as to properly
--             declare the recursive qualifier function.

abbrev IdentName := String

inductive Term (α : Type u) where
 | Ident (s : IdentName)
 | Seq (x : List α)
 | App (nm : IdentName) (args : List (Term α))
 | Annotated (t : Term α) (annot : List (String))

#blaster [ (∀ (β : Type) (x : Term (List β)) (f : Term (List β) → Nat), f x > 10) →
           (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 20)
         ]


end Tests.Issue32
