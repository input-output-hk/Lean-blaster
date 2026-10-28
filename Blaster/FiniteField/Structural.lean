import Lean
import Blaster.FiniteField.Residue

open Lean Meta

namespace Blaster.FiniteField

/-- Recognize the nominal carrier without requiring a concrete modulus. This
    low-level layer may be used by the optimizer itself: symbolic ring operations
    must remain opaque too. It neither normalizes a modulus nor admits primality.
    Reducible type aliases are accepted, but `Fin p` is never a residue carrier. -/
def getResidueModulus? (type : Expr) : MetaM (Option Expr) := do
  if let some modulus := type.app1? ``Residue then return some modulus
  return (← withReducible (whnf type)).app1? ``Residue

end Blaster.FiniteField
