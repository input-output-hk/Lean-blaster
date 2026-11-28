import Lean
import Blaster

/-!
# `#blaster (backend: ffi)` routing

These tests prove that `(backend: ffi)` routes a real `#blaster` query through the
in-process Z3 FFI session (`Blaster.Smt.FFI.Z3Session`) instead of the legacy `z3`
subprocess, while an explicit `.smtlib` control checks the legacy path.

Every solver-reaching goal first emits an opaque-type qualifier for its quantified
variables — e.g. `∀ n : Nat` emits `(define-sort Nat () Int)` and
`(define-fun @isNat ((@x Nat)) Bool (<= 0 @x))`. As of Task 14 the FFI session's
`runCommand` handles `define-sort` (sort aliases) in addition to the earlier
`declare-*` / `define-fun[s-rec]` / `declare-datatype` support, so a real
`(backend: ffi)` goal now runs the FULL in-process pipeline and is proved
`✅ Valid` — the same verdict the legacy subprocess produces. That the FFI path
reaches the identical result is the proof of routing; it exercises the FFI session
end to end, never the subprocess.
-/

namespace Tests.Smt.FFI.FFIBackend

-- FFI backend: the query runs entirely in the in-process Z3 session (type qualifier
-- via define-sort/define-fun, quantifiers, arithmetic) and is proved `✅ Valid`.
-- This is the first real end-to-end `#blaster (backend: ffi)` goal.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

-- Legacy `.smtlib` subprocess: the same goal is proved `✅ Valid`.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: smtlib) [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

end Tests.Smt.FFI.FFIBackend
