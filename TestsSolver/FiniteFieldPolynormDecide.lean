import Blaster.FF04.Corpus

/-! FF-04 reconstruction benchmark; see the shared corpus for scope and limits.
Run with `lake env lean -Dprofiler=true -Dprofiler.threshold=0` and this path.
The normalizer uses kernel `decide`, never `native_decide`.
-/
namespace Test.FiniteFieldPolynorm
open Blaster.FF04 Blaster.FF04.Polynorm

theorem distributeDecide (ctx : Context F) : distributeL.eval ctx = distributeR.eval ctx := by
  apply Expr.denote_eq_from_toPolynomial_eq
  decide

theorem characteristicDecide (ctx : Context F) : characteristicL.eval ctx = characteristicR.eval ctx := by
  apply Expr.denote_eq_from_toPolynomial_eq
  decide

theorem nestedDecide (ctx : Context F) : nestedL.eval ctx = nestedR.eval ctx := by
  apply Expr.denote_eq_from_toPolynomial_eq
  decide

theorem coefficientsDecide (ctx : Context F) : coefficientsL.eval ctx = coefficientsR.eval ctx := by
  apply Expr.denote_eq_from_toPolynomial_eq
  decide

#print axioms distributeDecide
#print axioms characteristicDecide
#print axioms nestedDecide
#print axioms coefficientsDecide

end Test.FiniteFieldPolynorm
