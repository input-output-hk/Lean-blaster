import Blaster.Smt.FFI

open Blaster.Smt.FFI

/-- info: FFI check-sat(true) = 2 -/
#guard_msgs in
#eval do IO.println s!"FFI check-sat(true) = {← smokeCheckTrue}"
