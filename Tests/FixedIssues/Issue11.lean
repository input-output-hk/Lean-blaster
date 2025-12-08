import Lean
import Blaster

namespace Tests.Issue11


-- Issue: Match expression not reduced
-- Diagnosis: It seems that reduceMatcher? is not able to discriminate
-- complex constructors when withReducible is used.

inductive Data where
  | Constr : Int → List Data → Data
  | Map : List (Data × Data) → Data
  | List : List Data → Data
  | I : Int → Data
  | B : ByteArray → Data


def matchExpr (a : Prop) (b : Prop) : Prop :=
  match [some (some (Data.Constr 7 []))] with
  | [some (some (Data.Constr 0 [Data.I _allowed, Data.I _actual]))] => a ∧ b
  | _ => False

#blaster [∀ (a b : Prop), matchExpr a b = False]

end Tests.Issue11
