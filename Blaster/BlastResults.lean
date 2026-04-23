import Lean
open Lean System

namespace Blaster.BlastResults

-- ── JSON helpers ──────────────────────────────────────────────────────────────

private def jsonEscape (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c    => acc.push c) "" ++ "\""

-- In Lean 4.26.0, Json.obj uses Std.TreeMap.Raw String Json (not RBMap).
-- Lookup is via .get? (not .find?).

private def getStr (j : Json) (key : String) : Option String :=
  match j with
  | .obj fields => match fields.get? key with | some (.str s) => some s | _ => none
  | _ => none

private def getNat (j : Json) (key : String) : Option Nat :=
  match j with
  | .obj fields => match fields.get? key with
    -- JsonNumber: mantissa : Int, exponent : Nat
    -- For integer JSON values, exponent = 0 and mantissa is the value.
    | some (.num ⟨m, 0⟩) => if m ≥ 0 then some m.toNat else none
    | _ => none
  | _ => none

private def getStrList (j : Json) (key : String) : List String :=
  match j with
  | .obj fields => match fields.get? key with
    | some (.arr elems) => elems.toList.filterMap (fun e => match e with | .str s => some s | _ => none)
    | _ => []
  | _ => []

-- ── Record types ──────────────────────────────────────────────────────────────

structure StartRecord where
  name       : String
  desc       : String
  decl       : String
  moduleName : String
  line       : Nat

structure EndRecord where
  name         : String
  status       : String   -- "proved" | "falsified" | "undetermined" | "timeout"
  time_ms      : Nat
  memory_bytes : Option Nat := none
  cex          : List String := []

inductive Record where
  | start (r : StartRecord)
  | end_  (r : EndRecord)
  | unknown

-- ── Serialisation ─────────────────────────────────────────────────────────────

def startRecordJson (r : StartRecord) : String :=
  s!"\{\"event\":\"start\",\"name\":{jsonEscape r.name},\"desc\":{jsonEscape r.desc}," ++
  s!"\"decl\":{jsonEscape r.decl},\"module\":{jsonEscape r.moduleName},\"line\":{r.line}}"

def endRecordJson (r : EndRecord) : String :=
  let base := s!"\{\"event\":\"end\",\"name\":{jsonEscape r.name}," ++
              s!"\"status\":{jsonEscape r.status},\"time_ms\":{r.time_ms}"
  let withMem := match r.memory_bytes with
    | none   => base
    | some b => base ++ s!",\"memory_bytes\":{b}"
  let withCex :=
    if r.cex.isEmpty then withMem
    else withMem ++ ",\"cex\":[" ++ (",".intercalate (r.cex.map jsonEscape)) ++ "]"
  withCex ++ "}"

-- ── Deserialisation ───────────────────────────────────────────────────────────

def parseRecord (line : String) : Record :=
  match Json.parse line with
  | .error _ => .unknown
  | .ok json =>
    match getStr json "event" with
    | some "start" =>
      match getStr json "name", getStr json "desc", getStr json "decl",
            getStr json "module", getNat json "line" with
      | some name, some desc, some decl, some modName, some ln =>
        .start { name, desc, decl, moduleName := modName, line := ln }
      | _, _, _, _, _ => .unknown
    | some "end" =>
      match getStr json "name", getStr json "status", getNat json "time_ms" with
      | some name, some status, some time_ms =>
        .end_ { name, status, time_ms,
                memory_bytes := getNat json "memory_bytes",
                cex := getStrList json "cex" }
      | _, _, _ => .unknown
    | _ => .unknown

-- ── File I/O ──────────────────────────────────────────────────────────────────

private def resultsDir : FilePath := ".lake" / "blast-results"

def resultsPath (moduleName : String) : FilePath :=
  resultsDir / (moduleName ++ ".ndjson")

-- Safe under Lean 4's snapshot elaboration: commands in a module are elaborated
-- sequentially (wrapAsyncAsSnapshot queues, not truly parallel within a module),
-- so the check-and-set in writeStart is not subject to a TOCTOU race.
private initialize truncatedModules : IO.Ref (List String) ← IO.mkRef []

def writeStart (r : StartRecord) : IO Unit := do
  IO.FS.createDirAll resultsDir
  let path := resultsPath r.moduleName
  let truncated ← truncatedModules.get
  if !truncated.contains r.moduleName then
    IO.FS.writeFile path ""
    truncatedModules.set (r.moduleName :: truncated)
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn (startRecordJson r)
  h.flush

def writeEnd (r : EndRecord) (moduleName : String) : IO Unit := do
  IO.FS.createDirAll resultsDir
  let h ← IO.FS.Handle.mk (resultsPath moduleName) .append
  h.putStrLn (endRecordJson r)
  h.flush

/-- Read all lines from the results file. Returns empty array if file absent. -/
def readAllLines (moduleName : String) : IO (Array String) := do
  let path := resultsPath moduleName
  if !(← path.pathExists) then return #[]
  let content ← IO.FS.readFile path
  return content.splitOn "\n" |>.filter (· ≠ "") |>.toArray

/-- Read lines added after `lastCount` lines. Returns new lines and new total. -/
def readNewLines (moduleName : String) (lastCount : Nat) : IO (Array String × Nat) := do
  let all ← readAllLines moduleName
  return (all.extract lastCount all.size, all.size)

end Blaster.BlastResults
