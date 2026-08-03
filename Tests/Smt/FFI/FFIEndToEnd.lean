import Blaster
/-!
# First real end-to-end `#blaster (backend: ffi)`

Each goal below is proved through the ENTIRE in-process Z3 FFI pipeline — opaque-type
qualifiers (`define-sort`/`define-fun`), quantifiers, and integer operators — with no
legacy `z3` subprocess.

**Crucially, every goal is verified to actually reach the solver**, not be discharged
by the pre-SMT optimizer. For each goal we pin TWO results:

* `(only-optimize: 1)` ⇒ `⚠️ Undetermined` — the optimizer alone CANNOT close it, so the
  SMT solver is genuinely required (if the optimizer solved it, this would be `✅ Valid`
  and no Z3 call would happen).
* `(backend: ffi)` ⇒ `✅ Valid` — the in-process FFI Z3 closes it.

The two together prove the FFI solver did the work. A plain (default `.smtlib`) control
shows subprocess/FFI parity.
-/
namespace Test.FFIEndToEnd

/-! ## Int implication (linear arithmetic; reaches the solver) -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x y : Int), x ≤ y → x - 1 < y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x y : Int), x ≤ y → x - 1 < y]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster [∀ (x y : Int), x ≤ y → x - 1 < y]  -- legacy `.smtlib` parity control

/-! ## Int transitivity -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x y z : Int), x < y → y < z → x < z]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (x y z : Int), x < y → y < z → x < z]

/-! ## Nat — the load-bearing goal: emits `(define-sort Nat () Int)` and the `@isNat`
     qualifier `define-fun`, both handled by the FFI `runCommand`, AND genuinely needs
     the solver (Undetermined under only-optimize). -/
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) [∀ (n m x : Nat), n = m → m = n + x → 0 = x]

end Test.FFIEndToEnd
