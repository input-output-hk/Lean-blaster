/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Circuits

theorem NormalizationF7CircuitGrind (ctx : Context F7) :
    fiveL.eval ctx = fiveR.eval ctx := by
  simp only [fiveL, fiveR, fiveR0, fiveR1, fiveR2, fiveR3, fiveR4, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationF7CircuitGrind

end FFM20.Normalization
