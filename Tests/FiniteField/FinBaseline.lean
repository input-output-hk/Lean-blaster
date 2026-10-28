import Tests.Pure

namespace Test.FiniteField.FinBaseline

/-! Baseline adapted from `TestsSolver/SmtFinBaseline.lean` at
    `724e32c377b5c6bfdecaf200984203b21c75355b`. Quantified `Fin` goals still
    fail in translation; closed goals are evaluated by the optimizer.
    Explicit modes keep these regressions independent of solver binaries. -/

-- A true ring identity is rejected before any SMT query can be completed.
/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (only-smt-lib: 1)
  [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

-- Optimization alone cannot discharge the quantified identity.
/-- info: ✅ Expected Undetermined -/
#guard_msgs in
#blaster (only-optimize: 1) (solve-result: 2)
  [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

-- This false goal is rejected too, rather than producing a counterexample.
/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (only-smt-lib: 1) [∀ (a : Fin 7), a * a ≠ 2]

-- Quantified division does not acquire a field interpretation.
/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (only-smt-lib: 1) [∀ (a b : Fin 7), a / b * b = a]

set_option trace.Translate.optExpr true

/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster (only-optimize: 1) [(3 : Fin 7) * 5 + 2 = 3]

-- `Fin.div` truncates the natural-number representatives.
/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster (only-optimize: 1) [(1 : Fin 7) / 2 = 0]

/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster (only-optimize: 1) [(6 : Fin 7) / 2 = 3]

-- Division by zero follows `Nat.div`, without any field inverse.
/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster (only-optimize: 1) [(3 : Fin 7) / 0 = 0]

-- In GF(7), 1 / 2 = 4; that claim must remain false for `Fin.div`.
/--
info: ✅ Expected Falsified
---
trace: [Translate.optExpr] optimized expression: False
-/
#guard_msgs in
#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 1)
  [(1 : Fin 7) / 2 = 4]

end Test.FiniteField.FinBaseline
