import Blaster.FiniteField.Residue

/-!
# FF-04 source compatibility

The experiment now uses the public nominal carrier. These reducible forwards
preserve its representation-facing spellings without duplicating ring instances.
-/

namespace Blaster.FF04

/-- Compatibility spelling for the sole public nominal carrier. -/
abbrev Residue := Blaster.FiniteField.Residue

namespace Residue

abbrev mk {p : Nat} (rep : Fin p) : Residue p :=
  Blaster.FiniteField.Residue.mk rep

abbrev rep {p : Nat} (a : Residue p) : Fin p :=
  Blaster.FiniteField.Residue.rep a

theorem ext {p : Nat} {a b : Residue p} (h : a.rep = b.rep) : a = b :=
  Blaster.FiniteField.Residue.ext h

theorem mk.injEq {p : Nat} (a b : Fin p) : (mk a = mk b) = (a = b) :=
  Blaster.FiniteField.Residue.mk.injEq a b

end Residue
end Blaster.FF04
