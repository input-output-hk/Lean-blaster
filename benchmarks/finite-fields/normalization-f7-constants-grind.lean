/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationF7ConstantsGrind (ctx : Context F7) :
    wrapL.eval ctx = wrapR.eval ctx := by
  simp only [wrapL, wrapR, Expr.eval] <;> grind (ematch := 0)

run_cmd emit ``NormalizationF7ConstantsGrind

end FFM20.Normalization
