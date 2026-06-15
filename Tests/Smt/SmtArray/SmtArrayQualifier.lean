import Blaster

namespace Test.SmtArrayQualifier

open Blaster

/-! # Test cases for the pointwise element-qualifier lift (soundness).

Every `(select a i)` must satisfy the element type's qualifier. The two `Fin 5`
tests below are *discriminating*: they are Valid only because the element
constraint is lifted onto the array — without the lift the element is an
unconstrained Int and each is Falsifiable (a `Fin 5` element ≥ 5). The two `Nat`
tests are general functional coverage (they happen to hold with or without the
lift, since universal-position Nat reads also pick up `@isNat` via the codomain
path); the lift's necessity for `Nat` is exercised by the existential
false-proof regression verified during review. -/

-- DISCRIMINATING: Fin element stays in range (Falsifiable without the lift)
#blaster [∀ (a : SMTArray (Fin 5)) (i : Nat), (a.get i).val < 5]

-- DISCRIMINATING: two Fin elements both constrained; max sum is 4 + 4 = 8 < 9
#blaster [∀ (a : SMTArray (Fin 5)) (i j : Nat), (a.get i).val + (a.get j).val < 9]

-- functional coverage: Nat element ≥ 0 in an arithmetic context
#blaster [∀ (a : SMTArray Nat) (i j : Nat), a.get i + a.get j ≥ a.get j]

-- functional coverage: read-over-write with a qualified (Nat) element type
#blaster [∀ (a : SMTArray Nat) (i : Nat) (v : Nat), (a.set i v).get i = v]

-- the @isArray premise is satisfiable, so universal goals are not vacuously
-- Valid: a too-strong claim about elements is still Falsified
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : SMTArray (Fin 5)) (i : Nat), (a.get i).val < 4]

end Test.SmtArrayQualifier
