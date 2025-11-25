/-
  This program checks if the Z3 SMT solver is installed correctly
  and prints its version.

  To run this program, ensure that Z3 is installed and accessible
  from your system's PATH. (See the instructions in CONTRIBUTING);
  then, compile and execute this Lean code as follows:

     lake build z3check
     lake exe z3check

  If Z3 is installed correctly, you will see

     Successfully ran z3:
     Z3 version 4.15.2 - 64 bit

  otherwise, it will print an error message.
-/

import Lean

open IO

def main : IO Unit := do
  let proc ← IO.Process.output { cmd := "z3", args := #["--version"] }
  if proc.exitCode == 0 then
    IO.println "Successfully ran z3:"
    IO.println proc.stdout
  else
    IO.eprintln "Failed to run z3:"
    IO.eprintln proc.stderr
