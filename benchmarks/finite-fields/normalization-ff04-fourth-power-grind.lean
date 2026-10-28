/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open Test.FiniteFieldPolynorm

theorem NormalizationFf04FourthPowerGrind (ctx : Context F) :
    nestedL.eval ctx = nestedR.eval ctx := by
  simp only [nestedL, nestedR, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationFf04FourthPowerGrind

end FFM20.Normalization
