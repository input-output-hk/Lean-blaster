import Lean
import Blaster

namespace Test.SmtExtension

structure MyPt where
  x : Nat
  y : Nat

axiom mkMyPt : Nat → Nat → MyPt
axiom firstPt (p : MyPt) : Nat

@[blaster (noRestart := true)]
axiom first_pt_of_mk : ∀ (x y : Nat), firstPt (mkMyPt x y) = x

#blaster (only-optimize: 1) [∀ (a b : Nat), firstPt (mkMyPt (a + 0) b) = a]

#blaster (only-optimize: 1) [∀ (a b : Nat), firstPt (mkMyPt (a + 1) b) > a]


universe u a b

def mk (_α : Sort u) : PUnit.{u+1} := PUnit.unit

@[blaster (noRestart := true)]
theorem mk_eq (α : Sort u) : mk α = PUnit.unit.{u+1} := rfl

-- VALID expected by Blaster
#blaster [∀ (α : Sort (max a b)), mk α = PUnit.unit]

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Sort (max a b)), mk α ≠ PUnit.unit]

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [∀ (α : Sort a), mk α ≠ PUnit.unit]

end Test.SmtExtension

