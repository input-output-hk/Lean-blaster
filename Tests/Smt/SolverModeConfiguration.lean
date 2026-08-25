import Blaster

namespace Test.SolverModeConfiguration

/--
error: ❌ `solver` conflicts with `solver-mode: first` and `solver-mode: agree`; concurrent modes always run both Z3 and cvc5.
-/
#guard_msgs in
#blaster (solver: z3) (solver-mode: first) [∀ (x : Int), x = x]

/--
error: ❌ `only-smt-lib` cannot be combined with concurrent solver modes.
-/
#guard_msgs in
#blaster (solver-mode: agree) (only-smt-lib: 1) [∀ (x : Int), x = x]

-- `only-optimize` never starts either solver, even with a concurrent mode.
#blaster (solver-mode: first) (only-optimize: 1) [∀ (x : Int), x = x]
#blaster (solver: cvc5) (solver-mode: single) (only-optimize: 1) [∀ (x : Int), x = x]


/--
info: ✅ Expected Undetermined
-/
#guard_msgs in
#blaster (solver: cvc5) (only-smt-lib: 1) (solve-result: 2) [∀ (x : Int), x ≠ 3]

end Test.SolverModeConfiguration
