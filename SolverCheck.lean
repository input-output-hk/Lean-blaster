/-
  This program checks that the backend SMT solvers supported by Blaster
  are installed correctly and prints their versions.

  To run this program, ensure that the solver(s) are installed and accessible
  from your system's PATH (see the instructions in the README); then, compile
  and execute this Lean code as follows:

     lake build solvercheck
     lake exe solvercheck          # checks every supported solver
     lake exe solvercheck z3       # checks z3 only
     lake exe solvercheck cvc5     # checks cvc5 only

  If a solver is installed correctly, you will see output like:

     ✅ Successfully ran cvc5:
     <cvc5 first-line version banner>

  otherwise, it will print an error message and exit with a non-zero code.
-/

import Blaster

open Blaster.Options Blaster.Smt IO

def checkSolver (solver : SmtSolver) : IO Bool := do
  let desc := solver.descriptor
  let mut attemptLogs := #[]
  for candidate in desc.candidates do
    -- shares the discovery acceptance policy (version parsing, minimal
    -- version, fail-closed on unparseable banners) with Blaster itself
    let outcome ← probeSolverCandidate desc candidate
    match evalCandidateProbe desc candidate outcome with
    | .ok () =>
        IO.println s!"✅ Successfully ran {candidate.display}:"
        -- only the first line: cvc5 --version is followed by a long license notice
        IO.println outcome.banner
        return true
    | .error log => attemptLogs := attemptLogs.push log
  IO.eprintln s!"❌ Could not find a working {desc.name} ≥ {desc.minVersion}. Tried:"
  attemptLogs.forM (IO.eprintln s!"   {·}")
  return false

def main (args : List String) : IO UInt32 := do
  let solvers ←
    match args with
    | [] => pure #[SmtSolver.z3, SmtSolver.cvc5]
    | [s] =>
        match SmtSolver.ofString? s with
        | some solver => pure #[solver]
        | none => do
            IO.eprintln s!"Unknown solver '{s}' (expected 'z3' or 'cvc5')."
            return 1
    | _ => do
        IO.eprintln "usage: solvercheck [z3|cvc5]"
        return 1
  let mut allFound := true
  for solver in solvers do
    allFound := (← checkSolver solver) && allFound
  return (if allFound then 0 else 1)
