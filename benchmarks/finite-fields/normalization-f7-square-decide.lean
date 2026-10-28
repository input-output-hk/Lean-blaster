/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationF7SquareDecide (ctx : Context F7) :
    squareL.eval ctx = squareR.eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show squareL.toPolynomial = squareR.toPolynomial by decide)

run_cmd emit ``NormalizationF7SquareDecide

end FFM20.Normalization
