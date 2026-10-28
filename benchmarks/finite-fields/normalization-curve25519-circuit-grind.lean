/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Circuits

theorem NormalizationCurve25519CircuitGrind (ctx : Context FP) :
    chainL.eval ctx = chainR.eval ctx := by
  simp only [chainL, chainR, chainOutput, chainR0, chainR1, chainR2, chainR3, chainR4, chainR5, chainR6, chainR7, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationCurve25519CircuitGrind

end FFM20.Normalization
