import Blaster.StateMachine

open Blaster.StateMachine

/-!
Counter06 K-induction on BOTH backends, for FFI-vs-legacy parity of the engine
params (mbqi / macro_finder / auto_config / pull_nested_quantifiers). Machine copied
verbatim from `Tests/StateMachine/Counter06.lean`.

`gen-cex: 0` deliberately: the FFI counterexample string-formatting path is known to
diverge from the subprocess by one trailing character (documented in FFICounter.lean),
which is unrelated to the engine params under test. With cex off, only the STRUCTURAL
K-induction verdict is compared.
-/

namespace Test.FFICounter06

inductive Request where
  | Tr : Request
  | Fa : Request

inductive State where
  | Ready : State
  | Delay : State
  | Busy : State

structure CounterState where
  state : State
  timer : Nat
  prev_state : State
  prev_req : Request
  prev_timer : Nat

instance counterStateMachine : StateMachine Request CounterState where
  init i := { state := .Ready, timer := 0, prev_state := .Ready, prev_req := i, prev_timer := 0}
  next i s :=
    let s' := {s with prev_state := s.state, prev_req := i}
    match s.state with
    | .Ready =>
         match i with
         | .Tr => {s' with state := .Delay, timer := 0}
         | _ => s'
    | .Delay =>
         if s.timer < 3
         then {s' with timer := s.timer + 1}
         else {s' with state := .Busy }
    | .Busy =>
         match i with
         | .Fa => {s' with state := .Ready}
         | _ => s'
  assumptions _ _ := True
  invariants _i s :=
    (s.prev_state = .Delay ∧ s.prev_timer = 3) → s.state = .Busy

-- The invariant is genuinely NOT inductive (see the source comment in Counter06.lean:
-- "cannot be proved alone as not inductive"), so BOTH backends fail to establish it —
-- deepening a counterexample-to-induction at each depth up to the bound. With `gen-cex: 0`
-- the per-depth CTI models are suppressed, leaving only the final structural verdict,
-- which the FFI backend must match legacy on. (Before the engine-params wiring the FFI
-- K-induction step checks already resolved this identically; this pins that parity.)

-- FFI backend (engine params under test)
/-- warning: ⚠️ Failed to establish induction up to Depth 3 -/
#guard_msgs in
#kind (backend: ffi) (gen-cex: 0) (max-depth: 3) [counterStateMachine]

-- Legacy `.smtlib` subprocess (parity control)
/-- warning: ⚠️ Failed to establish induction up to Depth 3 -/
#guard_msgs in
#kind (gen-cex: 0) (max-depth: 3) [counterStateMachine]

end Test.FFICounter06
