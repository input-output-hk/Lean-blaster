import Lean
import Tests.Utils

open Lean Elab Command Term

namespace Tests.UnfoldExists

/-! ## Test objectives to validate `Exists unfolding -/

/-! Test cases to validate unfolding of `Exists only when reduced to a constant value or via rewriting. -/

-- TODO: add test cases when simplification rules are added for Exists


/-! Test cases to validate when `Exists must not be unfolded -/

-- ∀ (x : Int), ∃ (y z : Int), y > x ∧ z > y ===> ∀ (x : Int), ∃ (y z : Int), x < y ∧ y < z
#testOptimize [ "ExistsNotUnfolded_1" ] ∀ (x : Int), ∃ (y z : Int), y > x ∧ z > y ===>
                                        ∀ (x : Int), ∃ (y z : Int), x < y ∧ y < z

-- ∀ (x : Nat), ∃ (y z : Nat), y > x ∧ z > y ===> ∀ (x : Nat), ∃ (y z : Nat), x < y ∧ y < z
#testOptimize [ "ExistsNotUnfolded_2" ] ∀ (x : Nat), ∃ (y z : Nat), y > x ∧ z > y ===>
                                        ∀ (x : Nat), ∃ (y z : Nat), x < y ∧ y < z


end Tests.UnfoldExists
