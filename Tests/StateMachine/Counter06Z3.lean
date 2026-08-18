import Tests.StateMachine.Counter06

namespace Test.Counter06

/--
info: ⚠️ Induction failed at Depth 1
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: Test.Counter06.CounterState.mk Test.Counter06.State.Delay 2 Test.Counter06.State.Busy Test.Counter06.Request.Tr 3
---
info: ⚠️ Induction failed at Depth 2
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: Test.Counter06.CounterState.mk Test.Counter06.State.Ready 2 Test.Counter06.State.Busy Test.Counter06.Request.Tr 3
---
info:  - «Test.Counter06.counterStateMachine.input@1»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.input@2»: Test.Counter06.Request.Tr
---
info: ⚠️ Induction failed at Depth 3
---
info: Counterexample to Induction:
---
info:  - «Test.Counter06.counterStateMachine.input@0»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.state@0»: Test.Counter06.CounterState.mk Test.Counter06.State.Ready 2 Test.Counter06.State.Busy Test.Counter06.Request.Tr 3
---
info:  - «Test.Counter06.counterStateMachine.input@1»: Test.Counter06.Request.Fa
---
info:  - «Test.Counter06.counterStateMachine.input@2»: Test.Counter06.Request.Tr
---
info:  - «Test.Counter06.counterStateMachine.input@3»: Test.Counter06.Request.Tr
---
warning: ⚠️ Failed to establish induction up to Depth 3
-/
-- Pinned to z3: the docstring above records exact counterexample-to-induction
-- models, and model values are solver-specific (cvc5 returns different valid CTIs).
#guard_msgs in
#kind (solver: z3) (max-depth: 3) [counterStateMachine]

end Test.Counter06
