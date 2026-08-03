import Blaster
/-!
# First real end-to-end `#blaster (backend: ffi)`

With `define-sort` (Task 14) the FFI session's `runCommand` handles the full set of
declarative commands the translator emits, so a real `#blaster (backend: ffi)` query
now runs the ENTIRE in-process Z3 pipeline: opaque-type qualifiers
(`define-sort`/`define-fun`), quantifiers, and integer/boolean operators — no legacy
`z3` subprocess involved. Each goal below is proved `✅ Valid` through the FFI path.

The final query has no `(backend: …)` option, so it runs the legacy `.smtlib`
subprocess: a parity control showing the default path is unchanged and produces the
same verdict.
-/
namespace Test.FFIEndToEnd

-- Int + 0 = x : no `define-sort` needed (Int is a built-in sort in buildSort), so
-- this exercises quantifier + arithmetic through the FFI session.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x : Int), x + 0 = x]

-- Two binders + commutativity of +.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x y : Int), x + y = y + x]

-- Nat : the load-bearing goal for Task 14 — emits `(define-sort Nat () Int)` and
-- the `@isNat` qualifier `define-fun`, both now handled by the FFI `runCommand`.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x : Nat), x + 0 = x]

-- Bool : exercises the Bool qualifier plus `∨`/`=` over the built-in Bool sort.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (b : Bool), b = true ∨ b = false]

-- Legacy control (default `.smtlib` subprocess): same goal, same verdict.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster [∀ (x : Int), x + 0 = x]

end Test.FFIEndToEnd
