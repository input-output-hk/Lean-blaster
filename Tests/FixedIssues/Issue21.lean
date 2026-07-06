import Lean
import Blaster

open Lean Meta
namespace Tests.Issue21

-- Issue: Unexpected counterexample
-- Diagnosis : We need to consider axioms in the current namespace

set_option warn.sorry false

variable {p : Prop}
variable {q : Prop}

axiom hp1 : (p : Prop)

theorem t2 : p → q := by blaster
theorem t2_cvc5 : p → q := by blaster (solver: cvc5)
#blaster [t2]
#blaster (solver: cvc5) [t2]

variable {x y : Nat}

axiom nat_pos : ∀ (n : Nat), n > 0

theorem x_add_y_gt_zero : x + y > 0 := by blaster
theorem x_add_y_gt_zero_cvc5 : x + y > 0 := by blaster (solver: cvc5)
#blaster [x_add_y_gt_zero]
#blaster (solver: cvc5) [x_add_y_gt_zero]


inductive Event where
 | Start
 | Step
 | End

axiom never_end : ∀ (e : Event), e ≠ End

theorem event_not_ending : ∀ (e : Event), e ≠ End := by blaster
theorem event_not_ending_cvc5 : ∀ (e : Event), e ≠ End := by blaster (solver: cvc5)
#blaster [event_not_ending]
#blaster (solver: cvc5) [event_not_ending]

end Tests.Issue21
