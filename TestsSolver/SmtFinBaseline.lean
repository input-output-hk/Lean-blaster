import Blaster

namespace Test.SmtFinBaseline

/-! ## Baseline: `Fin 7` ring goals on the current backend (finite-field plan S4)

    Pins the behavior Blaster had before any finite-field support, as observed
    on `hillclimb-base` (see `docs/finite-fields/baseline-fin.md`). These are
    regression tests of the *current* behavior, not of desired behavior: a
    later finite-field step is expected to update them deliberately.

    Observed:
     - Goals quantifying over `Fin 7` are optimized to nested `Fin.add.match_1`
       / `Fin.mul.match_1` matches over `⟨(x op y).mod 7, ⋯⟩`, and translation
       then fails because `Fin` is an inductive type whose parameter `n : Nat`
       is a value rather than a type. No SMT query reaches the solver.
     - Closed `Fin 7` goals are fully evaluated by the optimizer to `True` or
       `False` and never reach translation.
     - `Fin.div` is `Nat` truncating division of the representatives, not
       field division: `(1 : Fin 7) / 2 = 0`, whereas in GF(7) `1 / 2 = 4`.
-/

set_option trace.Translate.optExpr true

/-! # Ring identity over `Fin 7`: optimized form, then translation failure -/

/--
warning: ⚠️ Undetermined
---
trace: [Translate.optExpr] optimized expression: ∀ (a b c : Fin 7),
      (match a,
          match b, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩) =
        match
          match a, b with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩,
          match a, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩
-/
#guard_msgs in
#blaster (only-optimize: 1) [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

/--
error: Inductive datatype with instance parameters not supported: `Fin
---
trace: [Translate.optExpr] optimized expression: ∀ (a b c : Fin 7),
      (match a,
          match b, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩) =
        match
          match a, b with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩,
          match a, c with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩ with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.add b).mod 7, ⋯⟩
-/
#guard_msgs in
#blaster [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

/-! # A false ring goal (3 * 3 = 2 in `Fin 7`) is not falsified either -/

/--
error: Inductive datatype with instance parameters not supported: `Fin
---
trace: [Translate.optExpr] optimized expression: ∀ (a : Fin 7),
      ¬⟨2, ⋯⟩ =
          match a, a with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩
-/
#guard_msgs in
#blaster [∀ (a : Fin 7), a * a ≠ 2]

/-! # Closed goals are decided by the optimizer alone -/

/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster [(3 : Fin 7) * 5 + 2 = 3]

/-! # `Fin.div` is truncating `Nat` division, not field division -/

/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster [(1 : Fin 7) / 2 = 0]

/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster [(6 : Fin 7) / 2 = 3]

-- Division by zero is `Nat` division by zero, i.e. `0`; there is no inverse.
/--
info: ✅ Valid
---
trace: [Translate.optExpr] optimized expression: True
-/
#guard_msgs in
#blaster [(3 : Fin 7) / 0 = 0]

-- In GF(7), 1 / 2 = 4 (2 * 4 = 8 = 1); `Fin.div` disagrees.
/--
info: ✅ Expected Falsified
---
trace: [Translate.optExpr] optimized expression: False
-/
#guard_msgs in
#blaster (gen-cex: 0) (solve-result: 1) [(1 : Fin 7) / 2 = 4]

/--
error: Inductive datatype with instance parameters not supported: `Fin
---
trace: [Translate.optExpr] optimized expression: ∀ (a b : Fin 7),
      a =
        match
          match a, b with
          | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨a.div b, ⋯⟩,
          b with
        | ⟨a, h⟩, ⟨b, isLt⟩ => ⟨(a.mul b).mod 7, ⋯⟩
-/
#guard_msgs in
#blaster [∀ (a b : Fin 7), a / b * b = a]

end Test.SmtFinBaseline
