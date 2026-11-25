import Blaster.Smt.FFI
open Blaster.Smt.FFI

private def expectRejected {α : Type} (label : String) (action : IO α) : IO Unit := do
  let rejected ← try
    let _ ← action
    pure false
  catch _ => pure true
  unless rejected do throw (IO.userError s!"{label}: malformed arrays were accepted")

/-- info: datatype-shape-guards-ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let placeholder ← ctx.mkBoolSort
  expectRejected "constructor names" <|
    ctx.mkDatatype "BadSingle" #["C"] #[] #[#[]] #[#[]]
  expectRejected "field sorts" <|
    ctx.mkDatatypeRec "BadRec" #["C"] #["isC"]
      #[#["next"]] #[#[]] #[#[1]]
  expectRejected "recursive reference" <|
    ctx.mkDatatypeRec "BadRef" #["C"] #["isC"]
      #[#["next"]] #[#[placeholder]] #[#[2]]
  expectRejected "mutual sort arrays" <|
    ctx.mkDatatypes #["BadMutual"] #[#["C"]] #[]
      #[#[#[]]] #[#[#[]]] #[#[#[]]]
  expectRejected "polymorphic field refs" <|
    ctx.mkPolyDatatype "BadPoly" #[] #["C"] #["isC"]
      #[#["value"]] #[#[placeholder]] #[#[]]
  IO.println "datatype-shape-guards-ok"
