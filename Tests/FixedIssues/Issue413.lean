import Tests.Utils

namespace Tests.Issue413

-- https://github.com/input-output-hk/lean-blaster/issues/413
-- Constructor constants with definitionally equal universe levels must not be
-- treated as different constructors merely because their level syntax differs.

universe u v w

-- The original false inequality must optimize to False, while its equality is
-- independently checked by Lean's kernel using rfl.
example : PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} := rfl

#testOptimize [ "CtorMaxCommEq" ]
  PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} ===> True
#testOptimize [ "CtorMaxCommNe" ]
  PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1} ===> False

-- The issue's original claim must be falsified by optimization alone.
#blaster (only-optimize: 1) (solve-result: 1)
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

-- These direct checks also cover universe instances that cannot be placed in
-- one homogeneous equality: the same constructor at unrelated levels is
-- inconclusive, whereas different constructor names are provably distinct.
-- The imax distribution pair denotes equal levels, but Level.isEquiv and
-- Lean's definitional equality comparison are incomplete here, so the
-- structural comparison must remain inconclusive too.
run_meta do
  let u := Lean.Level.param `u
  let v := Lean.Level.param `v
  let w := Lean.Level.param `w
  let unit := fun l => Lean.mkConst ``PUnit.unit [l]
  let imaxLeft : Lean.Level := .succ (.imax (.max u v) w)
  let imaxRight : Lean.Level := .succ (.max (.imax u w) (.imax v w))
  let cons := Lean.mkConst ``List.cons [.zero]
  let consNat := Lean.mkApp cons (Lean.mkConst ``Nat)
  let consZero := Lean.mkApp consNat (Lean.mkNatLit 0)
  let mulZero := fun n => Lean.mkApp2 (Lean.mkConst ``Nat.mul) (Lean.mkNatLit 0) (Lean.mkNatLit n)
  let cases : List (String × Lean.Expr × Lean.Expr × Option Bool) := [
    ("same constructor, equivalent levels",
      unit (.succ (.max u v)), unit (.succ (.max v u)), some true),
    ("same constructor, unrelated levels", unit (.succ u), unit (.succ v), none),
    ("same constructor, inconclusive imax levels", unit imaxLeft, unit imaxRight, none),
    ("same constructor, constant versus application", cons, consNat, none),
    ("same constructor, application versus constant", consNat, cons, none),
    ("same constructor, unequal application arities", consNat, consZero, none),
    ("noninjective function, distinct arguments", mulZero 1, mulZero 2, none),
    ("distinct constructors", Lean.mkConst ``Bool.true, Lean.mkConst ``Bool.false, some false)]
  for (label, lhs, rhs, expected) in cases do
    let (actual, _) ← (Blaster.Optimize.structEq? lhs rhs).run default
    unless actual == expected do
      throwError "{label}: expected {reprStr expected}, got {reprStr actual}"

-- In particular the tactic must not close the reproducer's false inequality.
example : PUnit.unit.{max u v + 1} = PUnit.unit.{max v u + 1} := by
  fail_if_success
    have : PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1} := by
      solve | blaster (only-optimize: 1)
  rfl

end Tests.Issue413
