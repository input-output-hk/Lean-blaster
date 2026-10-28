/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationCurve25519IdentityGrind (ctx : Context FP) :
    largeL.eval ctx = largeR.eval ctx := by
  simp only [largeL, largeR, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationCurve25519IdentityGrind

end FFM20.Normalization
