/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open Test.FiniteFieldPolynorm

theorem NormalizationFf04CharacteristicDecide (ctx : Context F) :
    characteristicL.eval ctx = characteristicR.eval ctx := by
  exact Expr.denote_eq_from_toPolynomial_eq (ctx := ctx)
    (show characteristicL.toPolynomial = characteristicR.toPolynomial by decide)

run_cmd emit ``NormalizationFf04CharacteristicDecide

end FFM20.Normalization
