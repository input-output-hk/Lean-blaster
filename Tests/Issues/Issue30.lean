import Lean
import Solver.Command.Tactic

namespace Tests.Issue30

-- Issue: Unexpected Valid
-- Diagnosis : Opaque should be handled as free variables. We should not reduce them
--             to their default value duirng optimization phase

opaque p : Nat → Prop
opaque q : Nat → Prop

#solve (gen-cex: 0) (solve-result: 1) [∀ (x : Nat), q x → p x]

opaque x : Prop

#solve (gen-cex: 0) (solve-result: 1) [x]

opaque n : Nat

#solve (gen-cex: 0) (solve-result: 1) [n = 0]

opaque m : Nat := 100

#solve (gen-cex: 0) (solve-result: 1) [m = 100]

axiom free_prop : Prop
-- checking that Prop axiom is handled as a free variable
#solve (gen-cex: 0) (solve-result: 1) [free_prop]


end Tests.Issue30
