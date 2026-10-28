import Lean
import Blaster.Smt.Syntax

namespace Blaster.Smt

/-- Polarity of the source assertion submitted to the solver, not of an
    individual occurrence or generated declaration. -/
inductive AssertionPolarity where
  | positive
  | negated
  deriving Inhabited, BEq, Repr

/-- Identity of an auxiliary inverse graph in one opened query scope. The
denominator is interpreted in the association's retained local context. Its
graph is asserted positively; the enclosing source query is negated. -/
structure InverseGraphWitness where
  scope : Lean.Name
  denominator : Lean.Expr
  graphPolarity : AssertionPolarity := .positive

/-- A solver symbol's typed Lean source association. The retained context and
    local instances include opened theorem parameters, so `source` and `type`
    remain meaningful after the translation telescope closes. `modulus` is the
    normalized residue modulus when recognized; it does not certify primality.
    Ordinary symbols retain the same source information with `modulus := none`. -/
structure SourceAssociation where
  symbol : SmtSymbol
  userName : Lean.Name
  source : Lean.Expr
  type : Lean.Expr
  modulus : Option Nat
  polarity : AssertionPolarity
  localContext : Lean.LocalContext
  localInstances : Lean.LocalInstances
  inverseGraph : Option InverseGraphWitness := none

end Blaster.Smt
