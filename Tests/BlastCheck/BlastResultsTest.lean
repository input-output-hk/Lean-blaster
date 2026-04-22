import Blaster.BlastResults
open Blaster.BlastResults

-- ── JSON round-trip tests ─────────────────────────────────────────────────────

private def check (label : String) (cond : Bool) : IO Unit :=
  if cond then pure ()
  else throw (IO.userError s!"BlastResults test FAILED: {label}")

-- StartRecord round-trip
#eval show IO Unit from do
  let r : StartRecord := { name := "myThm", desc := "Proves foo", decl := "theorem myThm : True",
                           moduleName := "My.Module", line := 42 }
  let json := startRecordJson r
  match parseRecord json with
  | .start s =>
    check "name"   (s.name == "myThm")
    check "line"   (s.line == 42)
    check "module" (s.moduleName == "My.Module")
  | _ => throw (IO.userError "StartRecord round-trip: wrong variant")

-- EndRecord proved round-trip
#eval show IO Unit from do
  let r : EndRecord := { name := "myThm", status := "proved", time_ms := 1234 }
  let json := endRecordJson r
  match parseRecord json with
  | .end_ e =>
    check "status"   (e.status == "proved")
    check "time_ms"  (e.time_ms == 1234)
    check "cex empty" e.cex.isEmpty
  | _ => throw (IO.userError "EndRecord proved round-trip: wrong variant")

-- EndRecord with counterexample
#eval show IO Unit from do
  let r : EndRecord := { name := "bad", status := "falsified", time_ms := 99,
                         cex := ["x = 1", "y = 2"] }
  let json := endRecordJson r
  match parseRecord json with
  | .end_ e => check "cex" (e.cex == ["x = 1", "y = 2"])
  | _ => throw (IO.userError "EndRecord cex round-trip: wrong variant")

-- Special characters in strings should round-trip
#eval show IO Unit from do
  let r : StartRecord := { name := "has\"quote", desc := "line1\nline2", decl := "d",
                           moduleName := "M", line := 1 }
  let json := startRecordJson r
  match parseRecord json with
  | .start s =>
    check "escaped quote" (s.name == "has\"quote")
    check "escaped newline" (s.desc == "line1\nline2")
  | _ => throw (IO.userError "Special chars round-trip: wrong variant")

-- Malformed lines return .unknown
#eval show IO Unit from do
  match parseRecord "not json" with
  | .unknown => pure ()
  | _ => throw (IO.userError "Malformed line should return .unknown")
