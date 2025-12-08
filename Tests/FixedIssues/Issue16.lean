import Lean
import Blaster

-- Issue: Valid result when counterexample expected
-- Diagnosis : The use of Array type to model higher order function introduces unsound smt context.
--             We therefore introduces ArrowTx types with the necessary congruences constraints.

namespace Tests.Issue16

mutual
  inductive Attribute (α : Type u) where
  | Named (n : String)
  | Pattern (p : List (Term α))
  | Qid (n : String) (p : Except (Option (Term α)) (List (Attribute α)))

  inductive Term (α : Type u) where
  | Ident (s : String)
  | Seq (x : List α)
  | App (nm : String) (args : List (Term α))
  | Annotated (t : Term α) (annot : List (Attribute α))

end

#blaster (gen-cex: 0) (solve-result: 1)
       [ (∀ (x : Int) (f : Int → Nat), f x > 2) →
         (∀  (x y : Int) (f : Int → Nat), f x + f y > 20)
       ]

#blaster (gen-cex:0) (solve-result: 1)
       [ (∀ (β : Type) (x : Term (List β)) (f : Term (List β) → Nat), f x > 0) →
         (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 20)
       ]

#blaster (gen-cex:0) (solve-result: 1) (random-seed: 2)
       [ (∀ (β : Type) (x : Term (List β)) (g : Term (List β) → Nat), g x > 10) →
         (∀ (α : Type) (x y : Term (List α)) (f : Term (List α) → Nat), f x + f y > 30)
       ]


end Tests.Issue16
