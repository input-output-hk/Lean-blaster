import Lean
import Blaster.Smt.Syntax

namespace Blaster.Smt

/-- Polarity of the source assertion submitted to the solver, not of an
    individual occurrence or generated declaration. -/
inductive AssertionPolarity where
  | positive
  | negated
  deriving Inhabited, BEq, Repr

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

end Blaster.Smt
