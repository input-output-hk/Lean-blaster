import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt

/-- info: env-empty -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let st ← BuildState.mk ctx
  IO.println s!"env-{if st.sorts.isEmpty then "empty" else "nonempty"}"

/-- info: sorts-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildSort Blaster.Smt.intSort
    let _ ← buildSort Blaster.Smt.boolSort
    let _ ← buildSort (Blaster.Smt.arraySort #[Blaster.Smt.intSort, Blaster.Smt.boolSort])
    IO.println "sorts-ok"

/-- info: uninterp-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  BuildM.run ctx do
    let _ ← buildSort (.SymbolSort (Blaster.Smt.mkNormalSymbol "MySort"))
    let _ ← buildSort (.SymbolSort (Blaster.Smt.mkNormalSymbol "MySort"))
    IO.println "uninterp-ok"
