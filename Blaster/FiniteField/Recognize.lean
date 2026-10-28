import Blaster.FiniteField.Structural
import Blaster.Optimize.Basic

open Lean

namespace Blaster.FiniteField

/-- A concrete residue carrier, retaining the original full type and modulus
    expressions alongside the normalized numeric modulus. No primality evidence
    or field admission is implied, even for zero, one or composite moduli. -/
structure ResidueDescriptor where
  type : Expr
  modulus : Expr
  modulusValue : Nat

/-- Concrete recognition sits above `Optimize.Basic` to reuse its closed-modulus
    normalizer without introducing an optimizer import cycle. Open moduli are
    rejected here, independently of structural opacity for symbolic rings. -/
def getResidueDescriptor? (type : Expr) : Optimize.TranslateEnvT (Option ResidueDescriptor) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars then return none
  let some modulus ← getResidueModulus? type | return none
  let some modulusValue ← Optimize.getNatModulus? modulus | return none
  return some { type, modulus, modulusValue }

end Blaster.FiniteField
