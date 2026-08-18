import Blaster

namespace Test.SolverSelection

/-! The two explicit selections run in one Lean process. This target requires both
    solver executables and verifies that selecting one backend does not disturb
    subsequent selection of the other. -/

#blaster (solver: cvc5) [∀ (x : Nat), 0 < x → 0^x = 0]
#blaster (solver: z3) [∀ (x : Nat), 0 < x → 0^x = 0]

end Test.SolverSelection
