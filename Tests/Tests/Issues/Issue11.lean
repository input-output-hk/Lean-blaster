import Lean
import Solver.Command.Syntax
import Tests.Smt.Benchmarks.UPLC.CekValue
import PlutusCore.Data.Basic

namespace Tests.Issue11

open PlutusCore.Data (Data)
open UPLC.CekValue (CekValue)
open UPLC.Uplc (Const)

-- Issue: Match expression not reduced
-- Diagnosis: It seems that reduceMatcher? is not able to discriminate
-- complex constructors when withReducible is used.


def matchExpr (a : Prop) (b : Prop) : Prop :=
  match [CekValue.VCon (Const.Data (Data.Constr 7 []))] with
  | [CekValue.VCon (Const.Data (Data.Constr 0 [Data.I _allowed, Data.I _actual]))] => a ∧ b
  | _ => False

#solve [∀ (a b : Prop), matchExpr a b = False]

end Tests.Issue11
