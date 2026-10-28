/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open Test.FiniteFieldPolynorm

theorem NormalizationFf04CharacteristicGrind (ctx : Context F) :
    characteristicL.eval ctx = characteristicR.eval ctx := by
  simp only [characteristicL, characteristicR, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationFf04CharacteristicGrind

end FFM20.Normalization
