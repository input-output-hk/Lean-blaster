/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open Test.FiniteFieldPolynorm

theorem NormalizationCompositeZeroProductDecide (ctx : Context (Residue 6)) :
    zeroProduct.eval ctx = (Expr.val (0 : Residue 6)).eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show zeroProduct.toPolynomial = (Expr.val (0 : Residue 6)).toPolynomial by decide)

end FFM20.Normalization
