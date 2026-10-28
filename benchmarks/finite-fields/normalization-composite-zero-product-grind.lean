/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open Test.FiniteFieldPolynorm

theorem NormalizationCompositeZeroProductGrind (ctx : Context (Residue 6)) :
    zeroProduct.eval ctx = (Expr.val (0 : Residue 6)).eval ctx := by
  simp only [zeroProduct, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationCompositeZeroProductGrind

end FFM20.Normalization
