import Blaster

namespace Test.SmtArrayQualifier

open Blaster

/-! # Test cases pinning the pointwise element-qualifier lift (soundness).

Every `(select a i)` must satisfy the element type's qualifier. These props are
Valid ONLY because that constraint is lifted onto the array; without it the
element is an unconstrained Int and each would yield a spurious counterexample
(a `Fin 5` element ≥ 5, or a `Nat` element < 0). They reach the solver (not
optimizer-folded), so they genuinely exercise the lifted `@isArray` predicate. -/

-- Fin element stays in range
#blaster [∀ (a : SMTArray (Fin 5)) (i : Nat), (a.get i).val < 5]

-- two Fin elements both constrained: max sum is 4 + 4 = 8 < 9
#blaster [∀ (a : SMTArray (Fin 5)) (i j : Nat), (a.get i).val + (a.get j).val < 9]

-- Nat element ≥ 0: adding it can't decrease the other operand
#blaster [∀ (a : SMTArray Nat) (i j : Nat), a.get i + a.get j ≥ a.get j]

-- read-over-write with a qualified (Nat) element type
#blaster [∀ (a : SMTArray Nat) (i : Nat) (v : Nat), (a.set i v).get i = v]

end Test.SmtArrayQualifier
