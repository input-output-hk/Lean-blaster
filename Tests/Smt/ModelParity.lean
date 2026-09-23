import Blaster.Smt.Model

open Blaster.Smt

private def sameEvidence (expected actual : String) : Bool :=
  match Sexp.parseMany expected, Sexp.parseMany actual with
  | .ok wanted, .ok found =>
      !wanted.isEmpty && wanted.map Sexp.normalizeValue == found.map Sexp.normalizeValue
  | _, _ => false

#guard !sameEvidence "sat\n((x 3))" "sat"
#guard !sameEvidence "sat\n((x 3))" "sat\n((x 3)"
#guard sameEvidence "sat\n((x 3))" "sat\n((x (let ((v 3)) v)))"

def main (args : List String) : IO UInt32 := do
  let [expectedPath, actualPath] := args
    | throw <| IO.userError "expected: ModelParity.lean EXPECTED ACTUAL"
  let expected ← IO.FS.readFile expectedPath
  let actual ← IO.FS.readFile actualPath
  if sameEvidence expected actual then return 0
  IO.eprintln s!"Incomplete, malformed or incorrect model evidence\nexpected: {expected}\nactual: {actual}"
  return 1
