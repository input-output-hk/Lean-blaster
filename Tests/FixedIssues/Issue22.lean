import Lean
import Blaster

open Lean Meta
namespace Tests.Issue22

-- Issue: translateConst: only opaque/recursive functions and theorems expected but got
--        Lean.Expr.const `Tests.Issue22.x []
-- Diagnosis : We need to consider not prop axiom during smt translation to properly
--             generate global variables.

set_option warn.sorry false

axiom x : Nat
axiom y : Nat

axiom nat_pos : ∀ (n : Nat), n > 0

theorem x_add_y_gt_zero : x + y > 0 := by blaster
#blaster [x_add_y_gt_zero]

theorem x_add_y_gt_x : x + y > x := by blaster
#blaster [x_add_y_gt_x]

theorem x_add_y_gt_y : x + y > y := by blaster
#blaster [x_add_y_gt_y]

theorem x_add_y_gt_2x : x + y > 2 * x := by blaster
#blaster [x_add_y_gt_2x]


end Tests.Issue22
