import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt

/-- info: env-empty -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let st ← BuildState.mk ctx
  IO.println s!"env-{if st.sorts.isEmpty then "empty" else "nonempty"}"
