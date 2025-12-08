import Blaster.StateMachine

open Blaster.StateMachine

namespace Test.BoolFlip

structure StateB where
  a : Bool
  b : Bool

structure Input where
  initState : StateB

instance boolFlip : StateMachine Input StateB where
  init i := i.initState
  next _ s :=
    { a := ¬ s.a
    , b := ¬ s.b}

  assumptions i _ := i.initState.a ≠ i.initState.b

  invariants _ s :=
    ¬ (s.a ∧ s.b)


#bmc (max-depth: 10) [boolFlip]

#kind (gen-cex: 0) (max-depth: 1) (solve-result: 2) [boolFlip] -- Will not work

-- Inductive established at Depth 2
#kind (gen-cex: 0) (max-depth: 2) [boolFlip]

end Test.BoolFlip
