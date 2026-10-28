/-
Copyright (c) 2026 lean-blaster contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import benchmarks.«finite-fields».NormalizationMetrics

namespace FFM20.Normalization
open Blaster.FiniteField Blaster.FF04.Polynorm
open FFM19.Semantic

theorem NormalizationF7CharacteristicGrind (ctx : Context F7) :
    characteristicL.eval ctx = characteristicR.eval ctx := by
  simp only [characteristicL, characteristicR, Expr.eval]
  grind (ematch := 0)

run_cmd emit ``NormalizationF7CharacteristicGrind

end FFM20.Normalization
