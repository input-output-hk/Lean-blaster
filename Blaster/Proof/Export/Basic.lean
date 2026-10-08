import Lean

/-!
# Exported proofs: option and declarations

With `blaster.induction.export` set, a proof that `blaster (induction: auto)`
finds is also written as a Lean file (see `Blaster.Proof.Export`). This module
holds what the provers contribute to that file: the declarations of a proof's
structure, such as the statements of an explorer replay, which the kernel term
of the proof otherwise keeps inside one large term.
-/
namespace Blaster.Proof.Export
open Lean

register_option blaster.induction.export : String := {
  defValue := ""
  descr := "Also write each proof found by `blaster (induction: auto)` as a Lean file: to this \
    path when it ends in `.lean`, otherwise into this directory, named after the declaration" }

register_option blaster.induction.exportTextAbove : Nat := {
  defValue := 100000
  descr := "In an exported proof, give terms longer than this many characters to `kernel%` as \
    string literals, which it reads in linear time (Lean's parser takes time quadratic in the \
    size of a command)" }

/-- The file or directory to export proofs to, if any (`blaster.induction.export`). -/
def target? [Monad m] [MonadOptions m] : m (Option String) := do
  let path := blaster.induction.export.get (← getOptions)
  return if path.isEmpty then none else some path

/-- Where a declaration is listed in an exported file. Each declaration comes
after those it uses; among those that can come next, the earlier group first. -/
inductive Group where
  /-- Definitions derived by the tactic (observed functions, splitters). -/
  | definitions
  /-- Propositions proved by Blaster's SMT translation. -/
  | solver
  /-- Theorems of the imported libraries: those that rely on Blaster's SMT
  translation, and those a file cannot name. -/
  | library
  /-- Lemmas derived and proved by the tactic (equations, facts about observers). -/
  | lemmas
  /-- Verification conditions of a replay. -/
  | conditions
  /-- The statements of a replay. -/
  | statements
  /-- The proofs of a replay's statements. -/
  | proofs
  /-- A replay, and the theorem itself. -/
  | result
  deriving BEq, Inhabited

/-- The order of the groups in a file. -/
def Group.rank : Group → Nat
  | .definitions => 0 | .solver => 1 | .library => 2 | .lemmas => 3 | .conditions => 4
  | .statements => 5 | .proofs => 6 | .result => 7

/-- A declaration of an exported proof. -/
structure Decl where
  name : Name
  levelParams : List Name := []
  /-- A definition, otherwise a theorem. -/
  isDef : Bool := false
  type : Expr
  value : Expr
  group : Group
  deriving Inhabited

/-- The structure of one replayed proof: declarations that together prove what
the constant `replaces` states, which the export uses instead of it. -/
structure Replay where
  replaces : Name
  decls : Array Decl
  /-- The declaration among `decls` with the type of `replaces`. -/
  result : Name

end Blaster.Proof.Export
