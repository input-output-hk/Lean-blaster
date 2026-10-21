import Blaster.FF04.Corpus

/-! FF-04 reconstruction benchmark; see the shared corpus for scope and limits.
Run with `lake env lean -Dprofiler=true -Dprofiler.threshold=0` and this path.
The normalizer uses kernel `decide`, never `native_decide`.
-/
namespace Test.FiniteFieldPolynorm
open Blaster.FF04 Blaster.FF04.Polynorm

theorem distributeGrind (ctx : Context F) : distributeL.eval ctx = distributeR.eval ctx := by
  simp only [distributeL, distributeR, Expr.eval]
  grind

theorem characteristicGrind (ctx : Context F) : characteristicL.eval ctx = characteristicR.eval ctx := by
  simp only [characteristicL, characteristicR, Expr.eval]
  grind

theorem nestedGrind (ctx : Context F) : nestedL.eval ctx = nestedR.eval ctx := by
  simp only [nestedL, nestedR, Expr.eval]
  grind

theorem coefficientsGrind (ctx : Context F) : coefficientsL.eval ctx = coefficientsR.eval ctx := by
  simp only [coefficientsL, coefficientsR, Expr.eval]
  grind

#print axioms distributeGrind
#print axioms characteristicGrind
#print axioms nestedGrind
#print axioms coefficientsGrind

end Test.FiniteFieldPolynorm
