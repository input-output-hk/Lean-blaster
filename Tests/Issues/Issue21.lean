import Lean
import Solver.Command.Tactic

open Lean Meta
namespace Tests.Issue21

-- Issue: Unexpected counterexample
-- Diagnosis : We need to consider axioms in the current namespace

set_option warn.sorry false

variable {p : Prop}
variable {q : Prop}

axiom hp1 : (p : Prop)

theorem t2 : p → q := by blaster
#solve [t2]

variable {x y : Nat}

axiom nat_pos : ∀ (n : Nat), n > 0

theorem x_add_y_gt_zero : x + y > 0 := by blaster
#solve [x_add_y_gt_zero]


inductive Event where
 | Start
 | Step
 | End

axiom never_end : ∀ (e : Event), e ≠ End

theorem event_not_ending : ∀ (e : Event), e ≠ End := by blaster
#solve [event_not_ending]

end Tests.Issue21
