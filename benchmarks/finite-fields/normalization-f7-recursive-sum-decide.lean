/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationF7RecursiveSumDecide (ctx : Context F7) :
    sumL.eval ctx = sumR.eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show sumL.toPolynomial = sumR.toPolynomial by decide)

run_cmd emit ``NormalizationF7RecursiveSumDecide

end FFM20.Normalization
