import Blaster

namespace Test.Cvc5FinBaseline

/-! Finite-field plan S4 baseline, cvc5 side: selecting cvc5 does not change
    how `Fin 7` goals are handled, since the failure happens in the
    solver-independent translation (see `Tests.Smt.SmtFinBaseline` and
    `docs/finite-fields/baseline-fin.md`). Closed goals never reach a solver. -/

/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (solver: cvc5) [∀ (a b c : Fin 7), a * (b + c) = a * b + a * c]

/-- error: Inductive datatype with instance parameters not supported: `Fin -/
#guard_msgs in
#blaster (solver: cvc5) [∀ (a : Fin 7), a * a ≠ 2]

/-- info: ✅ Valid -/
#guard_msgs in
#blaster (solver: cvc5) [(1 : Fin 7) / 2 = 0]

-- The same ring identity stated over `Nat` representatives modulo 7 is
-- decided by cvc5.
/-- info: ✅ Valid -/
#guard_msgs in
#blaster (solver: cvc5)
  [∀ (a b c : Nat), a < 7 → b < 7 → c < 7 →
     (a * ((b + c) % 7)) % 7 = ((a * b) % 7 + (a * c) % 7) % 7]

end Test.Cvc5FinBaseline
