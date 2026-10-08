import Blaster
import Tests.Proof.Support

/-! False statements about `Fin` that Blaster must refute. `Fin n` was once
translated as an unbounded `Int`, under which both hypotheses are false, so
the implications were valid. -/

#reject "Goal was falsified" in
theorem fin_pigeonhole_false : (∀ x y z : Fin 2, x = y ∨ y = z ∨ x = z) → False := by
  blaster (timeout: 10)

#reject "Goal was falsified" in
theorem fin_zero_false : (∀ x : Fin 0, x ≠ x) → False := by
  blaster (timeout: 10)
