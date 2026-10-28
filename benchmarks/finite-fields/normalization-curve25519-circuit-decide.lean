/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Circuits

theorem NormalizationCurve25519CircuitDecide (ctx : Context FP) :
    chainL.eval ctx = chainR.eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show chainL.toPolynomial = chainR.toPolynomial by decide)

run_cmd emit ``NormalizationCurve25519CircuitDecide

end FFM20.Normalization
