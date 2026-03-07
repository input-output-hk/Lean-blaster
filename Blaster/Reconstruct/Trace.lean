import Lean

open Lean

namespace Blaster.Reconstruct

inductive RewriteStep where
  | Rewrite (lemmaName : Name)
  | Unfold  (fname : Name)
  | RewriteWithHyp (hyp : Expr)

abbrev RewriteTrace := List RewriteStep

end Blaster.Reconstruct
