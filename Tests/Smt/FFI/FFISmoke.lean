import Blaster.Smt.FFI

open Blaster.Smt.FFI

/-- info: FFI check-sat(true) = 2 -/
#guard_msgs in
#eval do IO.println s!"FFI check-sat(true) = {← smokeCheckTrue}"

/-- info: ctx ok, err=0 -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let _s ← ctx.mkSolver
  IO.println s!"ctx ok, err={← ctx.errorCode}"
