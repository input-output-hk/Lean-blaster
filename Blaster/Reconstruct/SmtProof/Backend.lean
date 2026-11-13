import Lean
import Blaster.Reconstruct.SmtProof.Z3

/-!
# Backends of the replay of SMT proofs

The Z3 proof-producing backend with legacy proof objects: its command line, the
commands of Blaster's query they don't support, and their runs (with a portfolio of random seeds, and a cache of the
results on the last query).
-/

open Lean

namespace Blaster.Reconstruct.SmtProof

/-! ## Backends -/

def isZ3SpecificCommand (c : SExpr) : Bool :=
  match c with
  | .list xs =>
      match xs[0]?, xs[1]? with
      | some (SExpr.atom "set-simplifier"), _ => true
      | some (SExpr.atom "set-option"), some (SExpr.atom o) =>
          -- options set by the backend preamble, and options incompatible with proofs
          o == ":print-success" || o == ":produce-models" || o == ":produce-proofs" ||
          o == ":smt.macro_finder" || o == ":timeout" ||
          -- version specific options
          o.startsWith ":smt.arith.nl"
      | _, _ => false
  | _ => false

/-- Commands of Blaster's query that are set by the backend preamble or version specific (the simplifiers
    of the query, e.g., `recfun-finder`, are kept). -/
def isZ3PreambleCommand (c : SExpr) : Bool :=
  match c with
  | .list xs =>
      match xs[0]?, xs[1]? with
      | some (SExpr.atom "set-option"), some (SExpr.atom o) =>
          o == ":print-success" || o == ":produce-models" || o == ":produce-proofs" || o == ":timeout" ||
          o.startsWith ":smt.arith.nl"
      | _, _ => false
  | _ => false

/-- Z3 with legacy proof objects. With `simplifiers`, the simplifiers of Blaster's query (e.g., `recfun-finder`,
    `macro_finder`) are kept, which may be needed to find a proof, but produce coarser proofs. -/
def z3Backend (cmd : String) (timeoutSec : Nat) (simplifiers := false) : Backend where
  name := if simplifiers then "z3+" else "z3"
  cmd := cmd
  args := #["-smt2", s!"-T:{timeoutSec}"]
  -- NOTE: `pp.simplify_implies` prints `(=> a (=> b c))` as `(=> (and a b) c)` by default
  preamble := #["(set-option :produce-proofs true)", "(set-option :pp.simplify_implies false)"]
  dropCommand := if simplifiers then isZ3PreambleCommand else isZ3SpecificCommand
  parseProof := Z3.parseProof

/-- Guard the top-level universally quantified assertions over `Nat` (e.g., the definitions of recursive
    functions `∀ x, f x = f_LRec x`) with `0 ≤ x`, such that they hold for the interpretation of `Nat`
    functions in Lean (see `Interp.lean`). This only weakens the query. -/
def guardNatQuantifiers (c : SExpr) : SExpr :=
  match c with
  | .list #[.atom "assert", .list #[.atom "forall", .list vars, body]] =>
      let natVars := vars.filterMap fun v => match v with
        | .list #[.atom x, .atom "Nat"] => some x
        | _ => none
      if natVars.isEmpty then c else
      let guard (b : SExpr) : SExpr :=
        natVars.foldr (fun x acc => .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom x], acc]) b
      let body' := match body with
        | .list xs => if xs[0]? == some (.atom "!") then .list (xs.set! 1 (guard xs[1]!)) else guard body
        | _ => guard body
      .list #[.atom "assert", .list #[.atom "forall", .list vars, body']]
  | c => c

/-- The input of `backend` for the query `cmds`. -/
def backendInput (backend : Backend) (cmds : Array SExpr) : String :=
  String.intercalate "\n" (backend.preamble.toList ++
    (cmds.filter (!backend.dropCommand ·)).toList.map toString ++ ["(check-sat)", "(get-proof)", "(exit)"])

/-- The proof output of `backend` given its standard output (the output following `unsat`), or the reason of the
    failure. -/
def backendResult (backend : Backend) (stdout stderr : String) : Except String String :=
  -- the first line among `sat`, `unsat` and `unknown` (e.g., after warnings on unsupported options)
  let lines := stdout.splitOn "\n"
  -- errors on the query (e.g., unsupported declarations): its verdict and proof are not used
  let errors := lines.filter (·.trimLeft.startsWith "(error")
  if !errors.isEmpty then
    .error s!"{backend.name}: {String.intercalate " " (errors.take 3) |>.take 600}"
  else match lines.findIdx? (fun l => ["sat", "unsat", "unknown"].contains l.trim) with
    | some i =>
        if lines[i]!.trim == "unsat" then .ok (String.intercalate "\n" (lines.drop (i + 1)))
        else .error s!"{backend.name}: {lines[i]!.trim}"
    | none => .error s!"{backend.name}: {stdout.take 300} {stderr.take 300}"

/-- Run `backend` on the query `cmds`, returning the raw proof output. The query is written to a
    temporary file (no interaction with the solver's pipes during the run). -/
def runBackend (backend : Backend) (cmds : Array SExpr) : IO (Except String String) := do
  let query := backendInput backend cmds
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f query
  let (h, path) ← IO.FS.createTempFile
  try
    h.putStr query
    h.flush
    let out ← IO.Process.output { cmd := backend.cmd, args := backend.args.push path.toString }
    return backendResult backend out.stdout out.stderr
  finally
    IO.FS.removeFile path

/-- Whether `c` sets Z3's random seed. -/
def isSeedCommand (c : SExpr) : Bool :=
  match c with
  | .list #[.atom "set-option", .atom o, _] => o == ":smt.random-seed" || o == ":random-seed" || o == ":sat.random_seed"
  | _ => false

/-- Random seed of Z3 set by the query `cmds` (`0` by default). -/
def querySeed (cmds : Array SExpr) : Nat := Id.run do
  for c in cmds do
    if let .list #[.atom "set-option", .atom ":smt.random-seed", .atom n] := c then
      if let some k := n.toNat? then return k
  return 0

/-- The query `cmds` with Z3's random seed set to `seed`. -/
def withSeed (cmds : Array SExpr) (seed : Nat) : Array SExpr :=
  #[SExpr.list #[.atom "set-option", .atom ":smt.random-seed", .atom (toString seed)]] ++ cmds.filter (!isSeedCommand ·)

/-- Standard streams of the solver runs of a portfolio (see `runPortfolio`). -/
abbrev PortfolioStdio : IO.Process.StdioConfig := { stdin := .null, stdout := .piped, stderr := .null }

/-- Run `backend` (Z3, with its timeout given by an argument `-T:n`) on the queries `variants` concurrently (e.g., the
    query with different random seeds, whose time to find a proof may vary by an order of magnitude on the CEK
    evaluation of validators): the variant `i` is started after `i * delayMs` ms when no proof was found yet, with
    the timeout reduced accordingly (the portfolio takes at most the timeout of `backend`). Returns the first proof
    output (the other runs are then killed), or the result of the first variant when no variant finds a proof. -/
def runPortfolio (backend : Backend) (variants : Array (Array SExpr)) (delayMs : Nat) : IO (Except String String) := do
  if variants.size ≤ 1 then return ← runBackend backend (variants.getD 0 #[])
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_DUMP" then IO.FS.writeFile f (backendInput backend variants[0]!)
  let timeoutMs := (backend.args.findSome? fun a => if a.startsWith "-T:" then (a.drop 3).toNat? else none).getD 0 * 1000
  let start ← IO.monoMsNow
  let mut runs : Array (IO.Process.Child PortfolioStdio × Task (Except IO.Error String) × System.FilePath) := #[]
  let mut results : Array (Option (Except String String)) := #[]
  let mut proof := none
  try
    repeat
      let now ← IO.monoMsNow
      -- the next variant, unless its reduced timeout would be less than a second
      let i := runs.size
      if i < variants.size && now - start ≥ i * delayMs && (i == 0 || timeoutMs ≥ i * delayMs + 1000) then
        let (h, path) ← IO.FS.createTempFile
        h.putStr (backendInput backend variants[i]!)
        h.flush
        let args := backend.args.map fun a =>
          if a.startsWith "-T:" && i > 0 then s!"-T:{(timeoutMs - i * delayMs) / 1000}" else a
        let child ← IO.Process.spawn { toStdioConfig := PortfolioStdio, cmd := backend.cmd, args := args.push path.toString }
        let task ← IO.asTask (prio := .dedicated) do
          let out ← child.stdout.readToEnd
          discard <| child.wait
          return out
        runs := runs.push (child, task, path)
        results := results.push none
      for j in [:runs.size] do
        if results[j]!.isSome then continue
        let some (_, task, _) := runs[j]? | continue
        if !(← IO.hasFinished task) then continue
        let r : Except String String := match task.get with
          | Except.ok out => backendResult backend out ""
          | Except.error e => .error s!"{backend.name}: {e}"
        results := results.set! j (some r)
        if r matches .ok _ then proof := some r
      if proof.isSome then break
      if runs.size == variants.size && results.all (·.isSome) then break
      -- no other variant to start (its timeout would be too short): the remaining runs only
      if runs.size < variants.size && results.all (·.isSome) && timeoutMs < runs.size * delayMs + 1000 then break
      IO.sleep 20
  finally
    for (child, task, path) in runs do
      if !(← IO.hasFinished task) then try child.kill catch _ => pure ()
      try IO.FS.removeFile path catch _ => pure ()
  if let some r := proof then return r
  return (results[0]?.bind id).getD (.error s!"{backend.name}: no result")

/-- Results of the backends on the last query, reused by the replays of a goal with the different interpretations
    of the polymorphic encoding (see `proveBySmtProof`). -/
initialize backendRuns : IO.Ref (String × Std.HashMap String (Except String String)) ← IO.mkRef ("", {})

/-- `runBackend`, reusing the result of a previous run of `backend` on the same query. With `seeds > 1`, a portfolio
    of `seeds` runs of Z3 with consecutive random seeds from the seed of the query (see `runPortfolio`). -/
def runBackendCached (backend : Backend) (cmds : Array SExpr) (seeds := 1) (delayMs := 0) :
    IO (Except String String) := do
  let query := String.intercalate "\n" (cmds.toList.map toString)
  let (q, runs) ← backendRuns.get
  let runs := if q == query then runs else {}
  if let some r := runs.get? backend.name then return r
  -- debugging: the proof output of each backend written to the file `BLASTER_SMTPROOF_PROOFDUMP` suffixed with the name
  -- of the backend (e.g., `proof.z3rec`), and read from the file `BLASTER_SMTPROOF_PROOFFILE` suffixed likewise (when
  -- it exists) instead of a run of the solver, e.g., to replay the same proof again
  let proofFile? ← (← IO.getEnv "BLASTER_SMTPROOF_PROOFFILE").filterM fun f =>
    System.FilePath.pathExists s!"{f}.{backend.name}"
  let r ← if let some f := proofFile? then pure (.ok (← IO.FS.readFile s!"{f}.{backend.name}"))
    else if seeds ≤ 1 then runBackend backend cmds else
      let seed := querySeed cmds
      let queries := (List.range seeds).toArray.map fun k => if k == 0 then cmds else withSeed cmds (seed + k)
      runPortfolio backend queries delayMs
  if let some f ← IO.getEnv "BLASTER_SMTPROOF_PROOFDUMP" then
    if let .ok out := r then IO.FS.writeFile s!"{f}.{backend.name}" out
  backendRuns.set (query, runs.insert backend.name r)
  return r

end Blaster.Reconstruct.SmtProof
