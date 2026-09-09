import Blaster

/-! Large, reproducible let-chain queries. Run the companion Python script for
    isolated processes, phase timings and exact serialized query sizes. -/
open Lean in
macro "emissionChain%" n:num seed:term : term => do
  let depth := n.getNat
  if depth == 0 then Macro.throwError "depth must be positive"
  let ids := (Array.range depth).map fun i => mkIdent (Name.mkSimple s!"a{i}")
  let mut e : Term ← `(0 ≤ $(ids[depth-1]!))
  for i in (List.range depth).reverse do
    let v : Term ← if i == 0 then `(($seed : Int) + $seed)
      else `($(ids[i-1]!) + $(ids[i-1]!))
    e ← `(let $(ids[i]!) := $v; $e)
  return e
