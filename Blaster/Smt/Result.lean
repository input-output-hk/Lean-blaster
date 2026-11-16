import Lean
import Blaster.Smt.Syntax

namespace Blaster.Smt

/-- A quantified variable with the Lean type used to validate a model value. -/
structure TopLevelVar where
  symbol : SmtSymbol
  userName : Lean.Name
  type : Lean.Expr

/-- Result of an Smt query. -/
inductive Result where
  | Valid  : Result
  | Falsified (cex : List String) : Result
  | Undetermined : Result
deriving Repr

end Blaster.Smt
