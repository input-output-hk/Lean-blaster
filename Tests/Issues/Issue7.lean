import Lean
import Solver.Command.Syntax

namespace Tests.Issue7

-- Issue: optimizeExpr: unexpected meta variable
-- Diagnosis: There is a need to properly handle theorem with implicit arguments,
--            i.e., arguments within curly brackets

theorem dite_true {α : Sort u} {t : True → α} {e : ¬ True → α} : (dite True t e) = t True.intro := rfl
theorem dite_false {α : Sort u} {t : False → α} {e : ¬ False → α} : (dite False t e) = e not_false := rfl

#solve (only-optimize: 1) [dite_true]
#solve (only-optimize: 1) [dite_false]

end Tests.Issue7
