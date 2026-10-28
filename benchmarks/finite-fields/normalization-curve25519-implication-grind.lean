/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationCurve25519ImplicationGrind (ctx : Context FP) :
    implicationL.eval ctx = implicationR.eval ctx := by
  simp only [implicationL, implicationR, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationCurve25519ImplicationGrind

end FFM20.Normalization
