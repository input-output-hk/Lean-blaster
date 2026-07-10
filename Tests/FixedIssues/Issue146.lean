import Lean
import Blaster.StateMachine

open Blaster.StateMachine

namespace Tests.Issue146

-- Issue #146: #kind / #bmc give a wrong verdict when the transition state depends on the current
--            input: a spurious counterexample for a state-reading `assumptions`, and, more
--            seriously, a false Valid / No-counterexample when an `invariants` or `assumptions`
--            reads the current input alongside a state field (a real violation is missed).
-- Diagnosis: at depth k the state was built from the CURRENT input (next in_k prevState), so a
--            state-reading assumption (e.g. `i.x' ≥ s.x`) degenerated to a tautology and was
--            never enforced. Build each state from the PREVIOUS input (stᵢ₊₁ = next inᵢ stᵢ).

-- Assumption compares the next input to the current state. 1-inductive, so #kind proves Valid and
-- #bmc finds no counterexample. When the assumption was not enforced, both falsely reported a cex.
structure S where
  x : Int
structure I where
  x' : Int
instance sm : StateMachine I S where
  init _ := { x := 0 }
  next i _ := { x := i.x' }
  assumptions i s := i.x' ≥ s.x
  invariants _ s := s.x ≥ 0

/-- info: ✅ No counterexample up to Depth 4 -/
#guard_msgs in
#bmc (max-depth: 4) [sm]

/-- info: ✅ Valid -/
#guard_msgs in
#kind (max-depth: 2) [sm]

-- Multi-field carried state (v0 frozen) with a state-reading assumption: value never drops below
-- its initial value. Exercises multi-field threading.
structure VS where
  v : Int
  v0 : Int
structure VI where
  v' : Int
instance vsm : StateMachine VI VS where
  init _ := { v := 0, v0 := 0 }
  next i s := { v := i.v', v0 := s.v0 }
  assumptions i s := i.v' ≥ s.v
  invariants _ s := s.v ≥ s.v0

/-- info: ✅ Valid -/
#guard_msgs in
#kind (max-depth: 3) [vsm]

-- Soundness direction: the fix must NOT hide a real counterexample. The state-reading assumption
-- `i.x' = s.x + 1` forces every input, so the invariant `x ≤ 2` has a UNIQUE counterexample at
-- depth 3 (x reaches 3). The witness is deterministic, so it is safe to pin.
structure DS where
  x : Nat
structure DI where
  x' : Nat
instance dsm : StateMachine DI DS where
  init _ := { x := 0 }
  next i _ := { x := i.x' }
  assumptions i s := i.x' = s.x + 1
  invariants _ s := s.x ≤ 2

/--
error: ❌ Falsified
---
error: Counterexample detected at Depth 3:
---
error:  - «Tests.Issue146.dsm.input@0»: (Tests.Issue146.DI.mk 1)
---
error:  - «Tests.Issue146.dsm.input@1»: (Tests.Issue146.DI.mk 2)
---
error:  - «Tests.Issue146.dsm.input@2»: (Tests.Issue146.DI.mk 3)
---
error:  - «Tests.Issue146.dsm.input@3»: (Tests.Issue146.DI.mk 4)
-/
#guard_msgs in
#bmc (max-depth: 6) [dsm]

-- Multi-field #bmc for the carried-state machine (only #kind was covered above). Guards multi-field
-- threading in the BMC path. Under the bug this falsely reports a Depth-1 counterexample.
/-- info: ✅ No counterexample up to Depth 4 -/
#guard_msgs in
#bmc (max-depth: 4) [vsm]

-- Deeper induction: a state-reading assumption whose invariant is 2-inductive but NOT 1-inductive
-- (a two-step delay identity). Guards the deeper previous-input threading. gen-cex: 0 keeps the
-- solver-chosen counterexample-to-induction witness (z3-build-dependent) out of the golden.
structure IS where
  x  : Int
  p1 : Int
  p2 : Int
structure II where
  x' : Int
instance ism : StateMachine II IS where
  init _ := { x := 0, p1 := 0, p2 := 0 }
  next i s := { x := i.x', p1 := s.x, p2 := s.p1 }
  assumptions i s := i.x' = s.x
  invariants _ s := s.p2 = s.x

/-- warning: ⚠️ Failed to establish induction up to Depth 1 -/
#guard_msgs in
#kind (gen-cex: 0) (max-depth: 1) [ism]

/-- info: ✅ Valid -/
#guard_msgs in
#kind (gen-cex: 0) (max-depth: 2) [ism]

-- Multi-field soundness via #kind (the existing soundness case is single-field #bmc). Under the
-- bug the assumption self-contradicts and the real counterexample is hidden. gen-cex: 0 keeps the
-- witness out of the golden.
structure DVS where
  v  : Int
  v0 : Int
structure DVI where
  v' : Int
instance dvsm : StateMachine DVI DVS where
  init _ := { v := 0, v0 := 0 }
  next i s := { v := i.v', v0 := s.v0 }
  assumptions i s := i.v' = s.v + 1
  invariants _ s := s.v - s.v0 ≤ 2

/-- error: ❌ Falsified -/
#guard_msgs in
#kind (gen-cex: 0) (max-depth: 5) [dvsm]

-- Contradiction path: a state-reading assumption whose bound is exhausted as the reachable state
-- grows. Patched contradicts at Depth 2, the bug a step early.
structure CS where
  x : Nat
structure CI where
  x' : Nat
instance csm : StateMachine CI CS where
  init _ := { x := 0 }
  next i _ := { x := i.x' }
  assumptions i s := i.x' > s.x ∧ i.x' < 3
  invariants _ s := s.x ≤ 100

/-- error: ❌ Contradictory context at Depth 2 -/
#guard_msgs in
#bmc (max-depth: 6) [csm]

-- Soundness (false-Valid direction, the most severe): the invariant reads the current input
-- alongside a state field. Under the bug the state was built from the current input, so the
-- checked input was pinned to the state's own driver and a reachable violation was removed, making
-- #kind report a false Valid and #bmc a false No-counterexample. A real violation exists (previous
-- input 0 gives armed=1, x=0, then a positive current input violates), and both must find it.
-- gen-cex: 0 keeps the witness out.
structure ArmS where
  x : Int
  armed : Int
structure ArmI where
  y : Int
instance armsm : StateMachine ArmI ArmS where
  init _ := { x := 0, armed := 0 }
  next i _ := { x := i.y, armed := 1 }
  assumptions _ _ := True
  invariants i s := ¬ (s.armed = 1 ∧ i.y > 0 ∧ s.x = 0)

/-- error: ❌ Falsified -/
#guard_msgs in
#bmc (gen-cex: 0) (max-depth: 5) [armsm]

/-- error: ❌ Falsified -/
#guard_msgs in
#kind (gen-cex: 0) (max-depth: 3) [armsm]

end Tests.Issue146
