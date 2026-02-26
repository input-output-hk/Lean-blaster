import Lean
import Tests.Utils
import Tests.Smt.Benchmarks.ValidatorsExamples.PlutusLedgerAPI.VDummy

open Lean Elab Command Term
open Tests.ValidatorsExamples.PlutusLedgerAPI

namespace Test.OptimizeListAny

-- Another approach: Specializing new recursive function

-- List.any l (λ x => x == k) ===> true = List.elem k l
#testOptimize [ "ListAnyElem_1" ]
  ∀ (l : List Nat) (k : Nat), List.any l (λ x => x == k) ===>
  ∀ (l : List Nat) (k : Nat), true = List.elem k l

-- List.any l (λ x => k == x) ===> true = List.elem k l
#testOptimize [ "ListAnyElem_2" ]
  ∀ (l : List Nat) (k : Nat), List.any l (λ x => k == x) ===>
  ∀ (l : List Nat) (k : Nat), true = List.elem k l

-- Custom type with deriving BEq
#testOptimize [ "ListAnyElem_3" ]
  ∀ (l : List VerificationKeyHash) (k : VerificationKeyHash),
    List.any l (λ x => x == k) ===>
  ∀ (l : List VerificationKeyHash) (k : VerificationKeyHash),
    true = List.elem k l

end Test.OptimizeListAny
