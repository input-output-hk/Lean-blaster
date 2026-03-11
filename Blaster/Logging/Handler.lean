import Lean

open Lean Meta

namespace Blaster

/-- A logging backend that handles output dispatch.
    To add a new output mode, create a new `mkXxxLogger` factory function
    that returns a `BlasterLogger` with the desired behavior.
-/
structure BlasterLogger where
  /-- Emit an info-level message. -/
  emitInfo     : Syntax → MessageData → List (String × Json) → Option Nat → MetaM Unit
  /-- Emit a warning-level message. -/
  emitWarning  : Syntax → MessageData → List (String × Json) → Option Nat → MetaM Unit
  /-- Emit an error-level message. -/
  emitError    : Syntax → MessageData → List (String × Json) → Option Nat → MetaM Unit
  /-- Emit a progress message (e.g., BMC depth step). -/
  emitProgress : String → Option Nat → MetaM Unit
  /-- Emit a profiling result (task name + duration in seconds). -/
  emitProfile  : String → Float → MetaM Unit

instance : Inhabited BlasterLogger where
  default := {
    emitInfo     := fun _ _ _ _ => pure ()
    emitWarning  := fun _ _ _ _ => pure ()
    emitError    := fun _ _ _ _ => pure ()
    emitProgress := fun _ _ => pure ()
    emitProfile  := fun _ _ => pure ()
  }

end Blaster
