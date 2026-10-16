import Blaster
import Tests.Proof.Support

/-! False statements about integer division that Blaster must refute. The
upstream optimizer folded `Int.tdiv`, `Int.tmod`, `Int.fdiv` and `Int.fmod` of
constants with `Int.ediv`/`Int.emod`, which differ for negative operands (the
true values are `-3`, `-1`, `-4` and `-1`). -/

#reject "Goal was falsified" in
theorem tdiv_false : Int.tdiv (-7) 2 = -4 := by blaster (timeout: 10)
#reject "Goal was falsified" in
theorem tmod_false : Int.tmod (-7) 2 = 1 := by blaster (timeout: 10)
#reject "Goal was falsified" in
theorem fdiv_false : Int.fdiv 7 (-2) = -3 := by blaster (timeout: 10)
#reject "Goal was falsified" in
theorem fmod_false : Int.fmod 7 (-2) = 1 := by blaster (timeout: 10)
