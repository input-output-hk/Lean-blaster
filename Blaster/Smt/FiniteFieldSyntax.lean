import Blaster.Smt.Syntax

namespace Blaster.Smt

/-!
Pure syntax for the solving profile in `docs/finite-fields/solver-manifest.json`:
its protocol fixtures use `(_ FiniteField P)` and `#fNmP`.
These constructors do not recognize Lean carriers, check primality, select a
backend, authorize a native query, or provide proof support.
-/

/-- Construct a native finite-field sort for a positive modulus. Positivity is
only a syntax precondition; checked prime admission remains the caller's job. -/
def finiteFieldSort (modulus : Nat) : Option SortExpr :=
  if modulus == 0 then none
  else some (.IndexedSort (.ReservedSymbol "FiniteField") #[modulus])

/-- Construct `#fNmP` using the Euclidean residue of `value`, so `0 ≤ N < P`.
Reject zero rather than applying Lean's totalized remainder at zero. Positive
composite moduli and one are accepted as syntax, not admitted as native fields.
The reserved identifier keeps this solver token unquoted in both printers. -/
def finiteFieldLit (value : Int) (modulus : Nat) : Option SmtTerm :=
  if modulus == 0 then none
  else
    let residue := value % (modulus : Int)
    some (.SmtIdent (.SimpleIdent (.ReservedSymbol s!"#f{residue}m{modulus}")))

end Blaster.Smt
