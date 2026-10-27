import Lean
import Blaster

namespace Tests.Issue8

-- Issue: #blaster not capturing ill-formed formulae
-- Diagnosis: There is a need to check if formula is well typed and does not contain any sorryAx

/--
error: Unknown identifier `y`
---
error: translate: ∀ (x : Int), x < sorry is not well-formed
-/
#guard_msgs in
#blaster [∀ (x : Int), x < y]


/--
error: failed to synthesize instance of type class
  LT α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: translate: (α : Type) → α → α → sorry is not well-formed
-/
#guard_msgs in
#blaster [∀ (α : Type) (x y : α), if x < y then x else y]

end Tests.Issue8
