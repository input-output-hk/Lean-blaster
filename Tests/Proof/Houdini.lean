import Blaster.Proof.Explore.Houdini

/-!
# Invariant search on hand-written Horn queries

Each query mirrors what the explorer encodes for a program: a loop that adds
the elements of a list to an accumulator, and a procedure whose summary relates
its entry observation to its result. The checks fix the invariants the search
must find (after minimization), and the failures it must report: a goal that
does not follow, and a clause that z3 cannot read.
-/

namespace Tests.Houdini
open Lean Blaster.Proof.Explore.Houdini

/-- An observation of the integer variable `x`: the program value itself
(`var`), or the observer `head` applied to it. -/
def intKind (head : String) (role : Role) (x : Name) : Kind :=
  {sort := .int, head, role, ids := #[x]}

/-- A loop head over `(acc, rest, total)`: the accumulator, the sum of the
list still to walk, and the sum of the whole input (fixed for the run). The
loop adds the next element to the accumulator; at the end of the list it
checks `10 ≤ acc`, and the goal is `goal` over the input's sum `t`. -/
def loopQuery (goal : String) (step : Array String := #["(= r (+ x r2))"]) : Query where
  preamble := ""
  relations := #[{
    sorts := #["Int", "Int", "Int"]
    kinds := #[intKind "var" .var `acc, intKind "total" .var `rest, intKind "total" .root `input] }]
  clauses := #[
    -- entry: nothing added yet, the whole input to walk
    {vars := #[("t", "Int")], premises := #[], facts := #[],
     head := .app {rel := 0, args := #["0", "t", "t"]}},
    -- step: `rest = x :: rest2`
    {vars := #[("a", "Int"), ("r", "Int"), ("t", "Int"), ("x", "Int"), ("r2", "Int")],
     premises := #[{rel := 0, args := #["a", "r", "t"]}], facts := step,
     head := .app {rel := 0, args := #["(+ a x)", "r2", "t"]}},
    -- end of the list, check passed: the goal
    {vars := #[("a", "Int"), ("r", "Int"), ("t", "Int")],
     premises := #[{rel := 0, args := #["a", "r", "t"]}], facts := #["(= r 0)", "(>= a 10)"],
     head := .goal goal}]

/-- A procedure summing its argument's list: an inner loop over
`(entry, acc, rest)` (the entry observation is a ghost, fixed per call) and the
summary relation `(entry, result)` (its first argument is the entry). A caller
passes `t` and needs `result = t`. -/
def procedureQuery : Query where
  preamble := ""
  relations := #[
    {sorts := #["Int", "Int", "Int"]
     kinds := #[intKind "total" .ghost `entry, intKind "var" .var `acc, intKind "total" .var `rest]},
    {sorts := #["Int", "Int"], entry := 1
     kinds := #[intKind "total" .var `rest, intKind "var" .var `acc]}]
  clauses := #[
    {vars := #[("g", "Int")], premises := #[], facts := #[],
     head := .app {rel := 0, args := #["g", "0", "g"]}},
    {vars := #[("g", "Int"), ("a", "Int"), ("r", "Int"), ("x", "Int"), ("r2", "Int")],
     premises := #[{rel := 0, args := #["g", "a", "r"]}], facts := #["(= r (+ x r2))"],
     head := .app {rel := 0, args := #["g", "(+ a x)", "r2"]}},
    -- the procedure returns at the end of the list
    {vars := #[("g", "Int"), ("a", "Int"), ("r", "Int")],
     premises := #[{rel := 0, args := #["g", "a", "r"]}], facts := #["(= r 0)"],
     head := .app {rel := 1, args := #["g", "a"]}},
    -- the caller, after the call returned `res`
    {vars := #[("t", "Int"), ("res", "Int")],
     premises := #[{rel := 1, args := #["t", "res"]}], facts := #[],
     head := .goal "(= res t)"}]

def contains (s part : String) : Bool := (s.splitOn part).length > 1

/-- The invariants the search finds for `q`. -/
def invariants (q : Query) : IO (Array (Array String)) := do
  match ← search q 4 60000 fun _ => pure () with
  | .ok invariants => return invariants
  | .error why => throw (IO.userError s!"the search failed: {why}")

/-- Why the search finds no invariants for `q`, and its progress log. -/
def failure (q : Query) : IO (String × Array String) := do
  let log ← IO.mkRef #[]
  match ← search q 4 60000 fun line => log.modify (·.push line) with
  | .ok invariants => throw (IO.userError s!"the search proposed {invariants}")
  | .error why => return (why, ← log.get)

-- Minimal invariants: of the loop, `total = acc + rest` alone; of the
-- procedure, `entry = acc + rest` for its inner loop and `entry = result` for
-- its summary.
#eval show IO Unit from do
  let loop ← invariants (loopQuery "(>= t 10)")
  unless loop == #[#["(= p2 (+ p0 p1))"]] do
    throw (IO.userError s!"loop invariants {loop}")
  let procedure ← invariants procedureQuery
  unless procedure == #[#["(= p0 (+ p1 p2))"], #["(= p0 p1)"]] do
    throw (IO.userError s!"procedure invariants {procedure}")

-- Failures are reported, not hidden. The checks do not imply `11 ≤ total`,
-- although every clause gets an answer. A step z3 cannot read gets no answer,
-- is asked once more, and then its head's candidates are dropped: the goal
-- fails too.
#eval show IO Unit from do
  let (why, _) ← failure (loopQuery "(>= t 11)")
  unless contains why "1 of 1 goal clauses do not hold" && contains why "(0 without an answer)" do
    throw (IO.userError why)
  let (why, log) ← failure (loopQuery "(>= t 10)" (step := #["(this is not smt)"]))
  unless contains why "goal clauses do not hold" && log.any (contains · ", 2 unknown") do
    throw (IO.userError s!"{why}; log {log}")

end Tests.Houdini
