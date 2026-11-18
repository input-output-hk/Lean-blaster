import Blaster
import Blaster.Smt.FFI
/-!
# Solver options on the in-process Z3 FFI backend (`(backend: ffi)`)

Task 17. Before this task the FFI backend silently ignored every solver option.
This file proves that the two options
that affect observable results — **timeout** and **random-seed** — now actually take
effect on the FFI backend, by installing them directly on the in-process Z3 solver
via `Z3_params` / `Z3_solver_set_params` (see `Solver.setTimeout` / `Solver.setRandomSeed`
and their shims in `c/z3_shim_solver.c`, wired from `Env.setTimeout`/`setRandomSeed`).

## What each test proves

* **Routing / acceptance** (`#blaster`): `(backend: ffi) (random-seed: N)` and
  `(backend: ffi) (timeout: N)` are parsed, routed to the FFI setters, and a
  solver-reaching goal still proves `✅ Valid`. The paired `(only-optimize: 1) ⇒
  ⚠️ Undetermined` control shows the goal genuinely reaches the solver.

* **random-seed flows through the full `#blaster` pipeline and reaches Z3's search**:
  the same false goal (whose counterexample is any `x ∈ {1..20}`) is solved under two
  distinct seeds through `setBlasterProcess → setDefaultSmtOptions → setRandomSeed →
  Solver.setRandomSeed`; the two runs return **different** counterexamples (`x: 5` vs
  `x: 9`), which is only possible if the seed reached Z3. (Note: Z3 silently ignores an
  *unknown* param key without raising an error, so an `errorCode == 0` check has no
  teeth — a behavioral difference is the real evidence.) These pinned cex values are
  Z3-version-coupled, like the models pinned elsewhere in the FFI suite.

* **random-seed reaches Z3's search** (session level, value-robust): a disjunctive goal
  with many models is solved under several seeds; the returned models are not all
  identical. This survives Z3-version changes to the specific values above.

* **timeout takes effect** (session level): the pigeonhole formula PHP(8) (9 pigeons,
  8 holes) is UNSAT and Z3 proves it in ~90 ms, but a **1 ms** timeout forces
  `Undetermined`. The pair `tiny(1ms)=Undetermined` vs `big=Valid` on the *same*
  formula is the proof the timeout was honored: without it the tiny run would also be
  `Valid`; on an unsolvable-in-time formula both would be `Undetermined`. `Env.setTimeout`
  installs the timeout via the identical `if let some sess := …` branch that the
  `#blaster` seed tests above exercise end to end.
-/

namespace Test.FFIOptions
open Blaster.Smt.FFI Blaster.Smt

/-! ## Routing / acceptance via `#blaster` -/

-- Control: the goal genuinely reaches the solver (optimizer alone cannot close it).
/-- warning: ⚠️ Undetermined -/
#guard_msgs (warning) in
#blaster (only-optimize: 1) [∀ (x y : Int), x ≤ y → x - 1 < y]

-- random-seed is parsed, routed to the FFI random-seed setter, and the goal proves Valid.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) (random-seed: 7) [∀ (x y : Int), x ≤ y → x - 1 < y]

-- timeout is parsed, routed to the FFI timeout setter, and a generous limit still proves Valid.
/-- info: ✅ Valid -/
#guard_msgs (info) in
#blaster (backend: ffi) (timeout: 10) [∀ (x y : Int), x ≤ y → x - 1 < y]

/-! ## random-seed flows through the full `#blaster` pipeline (different seed ⇒ different cex).
     The goal is false; its counterexample is any `x ∈ {1..20}`. Seeds 1 and 42 pick
     different witnesses, which can only happen if the seed reached Z3's search.
     The load-bearing invariant is that the two pinned witnesses DIFFER — not that they
     are specifically 5 and 9. Those exact values are coupled to the Z3 version AND to
     the optimizer's encoding of `x ≠ 1 ∧ … ∧ x ≠ 20`; if a rewrite-rule or Z3 change
     shifts them, update the two values (they should still differ), don't suspect the
     FFI option wiring. The legacy `.smtlib` backend can pick other witnesses;
     verdicts match, while model choices need not.) -/

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: (5 : Int)
-/
#guard_msgs (info) in
#blaster (backend: ffi) (solve-result: 1) (random-seed: 1)
  [∀ (x : Int), x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 4 ∧ x ≠ 5 ∧ x ≠ 6 ∧ x ≠ 7 ∧ x ≠ 8 ∧ x ≠ 9 ∧ x ≠ 10 ∧
                x ≠ 11 ∧ x ≠ 12 ∧ x ≠ 13 ∧ x ≠ 14 ∧ x ≠ 15 ∧ x ≠ 16 ∧ x ≠ 17 ∧ x ≠ 18 ∧ x ≠ 19 ∧ x ≠ 20]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - x: (9 : Int)
-/
#guard_msgs (info) in
#blaster (backend: ffi) (solve-result: 1) (random-seed: 42)
  [∀ (x : Int), x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 4 ∧ x ≠ 5 ∧ x ≠ 6 ∧ x ≠ 7 ∧ x ≠ 8 ∧ x ≠ 9 ∧ x ≠ 10 ∧
                x ≠ 11 ∧ x ≠ 12 ∧ x ≠ 13 ∧ x ≠ 14 ∧ x ≠ 15 ∧ x ≠ 16 ∧ x ≠ 17 ∧ x ≠ 18 ∧ x ≠ 19 ∧ x ≠ 20]

/-! ## Shared helpers for the session-level demonstrations -/

private def app (o : String) (as : Array SmtTerm) : SmtTerm :=
  .AppTerm (.SimpleIdent (.ReservedSymbol o)) as

private def showR : Result → String
  | .Valid => "Valid" | .Falsified _ => "Falsified" | .Undetermined => "Undetermined"

/-! ## random-seed reaches Z3's search (value-robust session-level check) -/

private def xref : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))

-- Solve `x ∈ {1..30}` (many models) under `seed`; return x's model value.
private def modelUnderSeed (seed : UInt32) : IO String := do
  let s ← Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "x") intSort)
  s.solver.setRandomSeed seed
  let mut disj := #[]
  for k in [1:31] do disj := disj.push (app "=" #[xref, .NumTerm k])
  s.assert (app "or" disj)
  let topVars : Array (List TopLevelVar) := #[[⟨.NormalSymbol "x", `x, Lean.mkConst ``Int, ⟨`x⟩⟩]]
  match ← s.checkSat topVars true with
  | .Falsified cex => return String.intercalate "," cex.messages
  | r => return showR r

-- Distinct seeds do NOT all yield the same model ⇒ the seed reaches Z3's search.
/-- info: random-seed reaches Z3: models-vary=true -/
#guard_msgs (info) in
#eval do
  let seeds : Array UInt32 := #[1, 2, 7, 42, 100]
  let models ← seeds.mapM modelUnderSeed
  IO.println s!"random-seed reaches Z3: models-vary={models.any (· != models.getD 0 "")}"

/-! ## timeout is honored on the FFI solver -/

-- Pigeonhole PHP(n): n+1 pigeons into n holes. UNSAT (⇒ Valid), hard for larger n.
private def php (n : Nat) : IO Z3Session := do
  let s ← Z3Session.create
  let pv := fun (i j : Nat) => (SmtTerm.SmtIdent (.SimpleIdent (.NormalSymbol s!"p_{i}_{j}")))
  for i in [0:n+1] do
    for j in [0:n] do
      s.runCommand (.declareConst (.NormalSymbol s!"p_{i}_{j}") boolSort)
  for i in [0:n+1] do             -- each pigeon occupies some hole
    let mut disj := #[]
    for j in [0:n] do disj := disj.push (pv i j)
    s.assert (app "or" disj)
  for j in [0:n] do               -- no two pigeons share a hole
    for i in [0:n+1] do
      for i' in [i+1:n+1] do
        s.assert (app "not" #[app "and" #[pv i j, pv i' j]])
  return s

private def runPhp (n : Nat) (timeoutMs : UInt32) : IO String := do
  let s ← php n
  s.solver.setTimeout timeoutMs
  return showR (← s.checkSat #[] false)

-- Same UNSAT formula: solvable within a generous limit (Valid) but not within 1 ms
-- (Undetermined) ⇒ the timeout param was honored by the in-process solver.
/-- info: timeout honored: tiny(1ms)=Undetermined big(30s)=Valid -/
#guard_msgs (info) in
#eval do
  let tiny ← runPhp 8 1
  let big  ← runPhp 8 30000
  IO.println s!"timeout honored: tiny(1ms)={tiny} big(30s)={big}"

end Test.FFIOptions
