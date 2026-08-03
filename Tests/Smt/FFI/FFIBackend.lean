import Lean
import Blaster

/-!
# `#blaster (backend: ffi)` routing

These tests prove that `(backend: ffi)` routes a real `#blaster` query through the
in-process Z3 FFI session (`Blaster.Smt.FFI.Z3Session`) instead of the legacy `z3`
subprocess, and that the default backend stays `.smtlib` (legacy) so the existing
suite is unaffected.

Every solver-reaching goal first emits an opaque-type qualifier for its quantified
variables — e.g. `∀ n : Nat` emits `(define-sort Nat () Int)` and
`(define-fun @isNat ((@x Nat)) Bool (<= 0 @x))`. FFI routing of `define-sort` /
`define-fun` is deferred to a later task (`Z3Session.runCommand` handles only
`declare-const` / `declare-fun` / `declare-sort`). So a `(backend: ffi)` query on a
real goal is *expected* to surface the FFI session's
`runCommand: unhandled command (later tasks)` error. That error itself is the proof
of routing: it can only come from the FFI session, never from the subprocess path.
-/

namespace Tests.Smt.FFI.FFIBackend

-- FFI backend: the query reaches the in-process Z3 session, which throws on the
-- (not-yet-supported) `define-sort`/`define-fun` qualifier command. The error is
-- emitted by `Blaster.Smt.FFI.runCommand`, proving the query routed through the
-- FFI session rather than the legacy subprocess.
/-- error: runCommand: unhandled command (later tasks) -/
#guard_msgs (error) in
#blaster (backend: ffi) [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

-- Default backend stays `.smtlib` (legacy subprocess): the *same* goal is proved
-- `✅ Valid`, confirming the FFI path is strictly opt-in and the default is
-- unchanged.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

end Tests.Smt.FFI.FFIBackend
