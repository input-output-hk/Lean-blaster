import Lean
import Solver.Command.Syntax

namespace Tests.Issue8

-- Issue: #solve not capturing ill-formed formulae
-- Diagnosis: There is a need to check if formula is well typed and does not contain any sorryAx

/--
error: Unknown identifier `y`
---
error: translate: ∀ (x : Int), x < sorry is not well-formed
-/
#guard_msgs in
#solve [∀ (x : Int), x < y]


/--
error: failed to synthesize
  LT α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: translate: (α : Type) → α → α → sorry is not well-formed
-/
#guard_msgs in
#solve [∀ (α : Type) (x y : α), if x < y then x else y]

end Tests.Issue8
