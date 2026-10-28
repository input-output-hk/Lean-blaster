/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Circuits

theorem NormalizationF7CircuitDecide (ctx : Context F7) :
    fiveL.eval ctx = fiveR.eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show fiveL.toPolynomial = fiveR.toPolynomial by decide)

run_cmd emit ``NormalizationF7CircuitDecide

end FFM20.Normalization
