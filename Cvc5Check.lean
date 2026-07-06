/-
  This program checks if the cvc5 SMT solver is installed correctly
  and prints its version.

  To run this program, ensure that cvc5 is installed and accessible
  from your system's PATH; then, compile and execute this Lean code
  as follows:

     lake build cvc5check
     lake exe cvc5check

  If cvc5 is installed correctly, you will see

     Successfully ran cvc5:
     cvc5 1.3.4 [...]

  otherwise, it will print an error message.
-/

import Lean

open IO

def main : IO Unit := do
  let proc ← IO.Process.output { cmd := "cvc5", args := #["--version"] }
  if proc.exitCode == 0 then
    IO.println "Successfully ran cvc5:"
    IO.println proc.stdout
  else
    IO.eprintln "Failed to run cvc5:"
    IO.eprintln proc.stderr
