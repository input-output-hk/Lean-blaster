namespace Blaster.Smt

/-- Result of an Smt query. -/
inductive Result where
  | Valid  : Result
  | Falsified (cex : List String) : Result
  | Undetermined : Result
deriving Repr

end Blaster.Smt
