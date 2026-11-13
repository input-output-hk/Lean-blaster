import Blaster
import Tests.Utils

namespace Tests.Issue413

-- Issues:
--  - https://github.com/input-output-hk/Lean-blaster/issues/413
-- Diagnosis: We should normalize universe levels after level mvar instantiation.

set_option warn.sorry false

/-- Should be reported as valid by Blaster -/
theorem unit_eq : PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} := by blaster

universe u v w

#testOptimize [ "CtorMaxCommEq" ]
  PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} ===> True
#testOptimize [ "CtorMaxCommNe" ]
  PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1} ===> False

-- The issue's original claim must be falsified by optimization alone.
#blaster (gen-cex: 0) (only-optimize: 1) (solve-result: 1)
  [PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1}]

-- Reassociation and distributing successor through max exercise level
-- equivalence beyond the spelling used by the reproducer.
example : PUnit.unit.{max (max u v) w + 1} =
    PUnit.unit.{max u (max v w) + 1} := rfl
example : PUnit.unit.{max u v + 1} =
    PUnit.unit.{max (u + 1) (v + 1)} := rfl

#testOptimize [ "CtorMaxAssocEq" ]
  PUnit.unit.{max (max u v) w + 1} =
    PUnit.unit.{max u (max v w) + 1} ===> True
#testOptimize [ "CtorMaxAssocNe" ]
  PUnit.unit.{max (max u v) w + 1} ≠
    PUnit.unit.{max u (max v w) + 1} ===> False
#testOptimize [ "CtorSuccMaxEq" ]
  PUnit.unit.{max u v + 1} =
    PUnit.unit.{max (u + 1) (v + 1)} ===> True
#testOptimize [ "CtorSuccMaxNe" ]
  PUnit.unit.{max u v + 1} ≠
    PUnit.unit.{max (u + 1) (v + 1)} ===> False

-- A nonzero right operand reduces imax to max.
example : PUnit.unit.{imax u (v + 1) + 1} =
    PUnit.unit.{max u (v + 1) + 1} := rfl

#testOptimize [ "CtorIMaxEq" ]
  PUnit.unit.{imax u (v + 1) + 1} =
    PUnit.unit.{max u (v + 1) + 1} ===> True
#testOptimize [ "CtorIMaxNe" ]
  PUnit.unit.{imax u (v + 1) + 1} ≠
    PUnit.unit.{max u (v + 1) + 1} ===> False

-- The comparison must also reach constructor heads in applied and nested terms.
example (α : Type (max u v)) (x : α) :
    @Option.some.{max u v} α x = @Option.some.{max v u} α x := rfl

#testOptimize [ "AppliedCtorMaxEq" ]
  ∀ (α : Type (max u v)) (x : α),
    @Option.some.{max u v} α x = @Option.some.{max v u} α x ===> True
#testOptimize [ "AppliedCtorMaxNe" ]
  ∀ (α : Type (max u v)) (x : α),
    @Option.some.{max u v} α x ≠ @Option.some.{max v u} α x ===> False

example : some [PUnit.unit.{max (max u v) w + 1}] =
    some [PUnit.unit.{max u (max w v) + 1}] := rfl

#testOptimize [ "NestedCtorMaxEq" ]
  some [PUnit.unit.{max (max u v) w + 1}] =
    some [PUnit.unit.{max u (max w v) + 1}] ===> True
#testOptimize [ "NestedCtorMaxNe" ]
  some [PUnit.unit.{max (max u v) w + 1}] ≠
    some [PUnit.unit.{max u (max w v) + 1}] ===> False

-- Equivalent levels must not hide a genuinely different constructor or field.
#testOptimize [ "DistinctCtorMaxEq" ]
  ∀ (α : Type (max u v)) (x : α),
    @Option.some.{max u v} α x = @Option.none.{max v u} α ===> False
#testOptimize [ "DistinctCtorMaxNe" ]
  ∀ (α : Type (max u v)) (x : α),
    @Option.some.{max u v} α x ≠ @Option.none.{max v u} α ===> True
#testOptimize [ "DistinctCtorFieldEq" ]
  some [true, false] = some [true, true] ===> False
#testOptimize [ "DistinctCtorFieldNe" ]
  some [true, false] ≠ some [true, true] ===> True
#testOptimize [ "UnknownCtorFieldEq" ]
  ∀ (x y : Bool), some x = some y ===> ∀ (x y : Bool), some x = some y

-- In particular the tactic must not close the reproducer's false inequality.
example : PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} := by
  fail_if_success
    have : PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1} := by
      solve | blaster (only-optimize: 1)
  rfl


end Tests.Issue413
