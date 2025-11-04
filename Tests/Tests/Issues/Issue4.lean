import Lean
import PlutusCore.ByteString
import Solver.Command.Syntax

namespace Tests.Issue4

open PlutusCore.ByteString (ByteString)

-- Issue: removeNamedPatternExpr: unexpected pattern expression
-- Diagnosis: There is a need to skip implicit/instance parameters (if any) of inductive datatype
--            when removing named pattern in pattern expression in retrieveAltsArgs
--            or when translating match to smt
-- E.g.,
-- def List.get {α : Type u} : (as : List α) → Fin as.length → α
--   | cons a _,  ⟨0, _⟩ => a
--   | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩
-- `as.length` will implicitly appear in the pattern matching on `Fin`.

#solve (only-optimize: 1)
  [ ∀ (x y : ByteString), (if x < y then 1 else 2) > 0 ]

end Tests.Issue4
