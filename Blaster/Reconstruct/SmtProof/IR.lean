import Blaster.Reconstruct.SmtProof.Term

/-!
# Proof IR

Backend independent representation of SMT proofs: a DAG of inference steps. Each step concludes
a formula from the conclusions of its premises (earlier steps). Backend adapters translate the
proofs of each solver into this representation (see `Z3.lean` and `Alethe.lean`), and the replay
(see `Replay.lean`) reconstructs a Lean proof step by step.

Clausal conclusions (e.g., Alethe's `(cl l₁ ... lₙ)`) are represented as disjunctions
`(or l₁ ... lₙ)`, the empty clause as `false`, and unit clauses as their literal.
-/

namespace Blaster.Reconstruct.SmtProof

structure Step where
  /-- rule name, as printed by the solver (e.g., `mp`, `quant-inst`, `resolution`) -/
  rule : String
  /-- indices of the premise steps (always smaller than the index of the step) -/
  premises : Array Nat := #[]
  /-- term arguments of the rule (e.g., the instantiation terms of `quant-inst`) -/
  args : Array STerm := #[]
  /-- other rule arguments (e.g., `arith farkas 1 1` for Z3's `th-lemma`) -/
  attrs : Array SExpr := #[]
  /-- conclusion (formula) -/
  concl : STerm
  /-- steps whose conclusion is assumed in the derivation of this step's premises and
      discharged by this step (e.g., Z3's `lemma`, Alethe's `subproof`) -/
  discharged : Array Nat := #[]
  /-- literals of the conclusion when it is a clause given explicitly (e.g., Alethe's `(cl l₁ ... lₙ)`),
      which disambiguates a unit clause whose literal is a disjunction -/
  clause? : Option (Array STerm) := none
  deriving Inhabited

/-- Function defined by the backend in the proof output (e.g., Z3's `define-funs-rec` header listing the
    recursive functions of the query and the auxiliary `fold-rec-n` functions it introduces). -/
structure FunDef where
  name : String
  params : Array (String × SExpr)
  sort : SExpr
  body : STerm
  deriving Inhabited

structure Proof where
  /-- name of the backend that produced the proof (e.g., `z3`, `cvc5`) -/
  backend : String
  steps : Array Step
  /-- index of the step deriving `false` -/
  root : Nat
  /-- functions defined in the proof output -/
  defs : Array FunDef := #[]
  deriving Inhabited

namespace Proof

/-- Number of uses of each rule. -/
def ruleStats (p : Proof) : Std.HashMap String Nat :=
  p.steps.foldl (fun m s => m.insert s.rule (m.getD s.rule 0 + 1)) {}

/-- Steps reachable from the root. -/
def reachable (p : Proof) : Array Bool := Id.run do
  let mut seen := Array.replicate p.steps.size false
  let mut todo := #[p.root]
  while !todo.isEmpty do
    let i := todo.back!
    todo := todo.pop
    if seen[i]! then continue
    seen := seen.set! i true
    for j in p.steps[i]!.premises do todo := todo.push j
    for j in p.steps[i]!.discharged do todo := todo.push j
  return seen

end Proof

/-- Interface of an SMT backend able to produce proofs. -/
structure Backend where
  name : String
  /-- command to spawn the solver (reading SMT-LIB commands on its standard input) -/
  cmd : String
  args : Array String
  /-- commands emitted before the query (e.g., options enabling proof production) -/
  preamble : Array String
  /-- whether a command of Blaster's query must be dropped for this backend (e.g., z3 specific options) -/
  dropCommand : SExpr → Bool
  /-- parse the output of `(get-proof)` -/
  parseProof : String → Except String Proof

end Blaster.Reconstruct.SmtProof
