/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationFalseGoalGrind (ctx : Context (F7)) :
    falseL.eval ctx = falseR.eval ctx := by
  simp only [falseL, falseR, Expr.eval]
  grind (ematch := 0)

end FFM20.Normalization
