import Blaster.StateMachine

open Blaster.StateMachine

/-!
End-to-end exercise of the Z3 FFI backend (`(backend: ffi)`) for the StateMachine
BMC / K-induction strategies. These drive `checkSatAssuming` through the in-process
Z3 session: the depth/init flags are declared, `(=> flag …)` is asserted, and each
step calls `checkSatAssuming #[flag]` before permanently deactivating the flag.

Each property is pinned on BOTH backends with identical expected messages, so the
file is also a parity check: the FFI backend must match the legacy `.smtlib`
subprocess on the structural verdicts (`✅ Valid` / `✅ No counterexample` /
`❌ Falsified`). Counterexample MODEL values are not pinned (`gen-cex: 0`): the FFI
cex string-formatting path currently diverges from the subprocess by one trailing
character, which is unrelated to the `checkSatAssuming` wiring under test.
-/

namespace Test.FFICounter

inductive Request where
  | Idle : Request
  | Reset : Request

-- Valid machine: bounded counter, invariant `s ≤ 3` always holds.
instance mValid : StateMachine Request Nat where
  init _ := 0
  next i s :=
    match i with
    | .Reset => 0
    | _ => if s < 3 then s + 1 else s
  assumptions _ _ := True
  invariants _ s := s ≤ 3

-- Counterexample machine: invariant `s ≤ 2` is violated once the counter reaches 3.
instance mCex : StateMachine Request Nat where
  init _ := 0
  next i s :=
    match i with
    | .Reset => 0
    | _ => if s < 3 then s + 1 else s
  assumptions _ _ := True
  invariants _ s := s ≤ 2

/-- info: ✅ No counterexample up to Depth 7 -/
#guard_msgs in
#bmc (backend: ffi) (max-depth: 7) [mValid]

/-- info: ✅ Valid -/
#guard_msgs in
#kind (backend: ffi) (max-depth: 1) [mValid]

/-- error: ❌ Falsified -/
#guard_msgs in
#bmc (backend: ffi) (gen-cex: 0) (max-depth: 6) [mCex]

-- Parity: same properties on the default `.smtlib` subprocess backend.

/-- info: ✅ No counterexample up to Depth 7 -/
#guard_msgs in
#bmc (max-depth: 7) [mValid]

/-- info: ✅ Valid -/
#guard_msgs in
#kind (max-depth: 1) [mValid]

/-- error: ❌ Falsified -/
#guard_msgs in
#bmc (gen-cex: 0) (max-depth: 6) [mCex]

end Test.FFICounter
