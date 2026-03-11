import Lean

open Lean Meta

namespace Blaster

/-- Typeclass for monads that support structured logging.
    To add a new output format, extend the `OutputRepr` enum and
    add the corresponding branches in the `TranslateEnvT` instance. -/
class MonadBlasterLog (m : Type → Type) where
  /-- Emit an info-level message. -/
  emitInfo     : Syntax → MessageData → List (String × Json) → Option Nat → m Unit
  /-- Emit a warning-level message. -/
  emitWarning  : Syntax → MessageData → List (String × Json) → Option Nat → m Unit
  /-- Emit an error-level message. -/
  emitError    : Syntax → MessageData → List (String × Json) → Option Nat → m Unit
  /-- Emit a progress message (e.g., BMC depth step). -/
  emitProgress : String → Option Nat → m Unit
  /-- Emit a profiling result (task name + duration in seconds). -/
  emitProfile  : String → Float → m Unit

end Blaster
