import Tests.Utils
import Blaster.Optimize.Env.HashConsing

open Lean Meta Elab Command Blaster.Optimize
namespace Tests.Issue249
set_option maxHeartbeats 0

/-- A linear-sized, physically shared, well-typed Nat expression. The first
identity seeds the canonical binder name; the shared graph uses another name. -/
private def input (depth : Nat) : Expr := Id.run do
  let nat := mkConst ``Nat
  let zero := mkNatLit 0
  let canonical := mkApp (.lam `canonical nat (.bvar 0) .default) zero
  let mut shared := mkApp (.lam `renamed nat (.bvar 0) .default) zero
  for _ in [:depth] do
    shared := mkApp2 (mkConst ``Nat.add) shared shared
  return mkApp2 (mkConst ``Nat.add) canonical shared

-- The allocation budget is deliberately much larger than a linear walk
-- needs. Before the fix, depth 20 requires about 39.8 million allocation
-- heartbeats while producing only 114 intern entries. This is not a wall-time
-- threshold and includes a second call on the same original graph.
run_cmd liftTermElabM do
  let check : TranslateEnvT Unit := do
    let e := input 20
    let mut previous : Option Expr := none
    for _ in [:2] do
      let started ← IO.getNumHeartbeats
      let result ← hashcons e
      let allocated := (← IO.getNumHeartbeats) - started
      unless allocated < 1000000 do
        throwError "hash-consing revisited a shared input graph: {allocated} allocation heartbeats"
      unless (← inferType result).isConstOf ``Nat do throwError "wrong result type"
      if let some old := previous then
        unless exprEq old result do throwError "canonical result changed between calls"
      previous := some result
      logInfo m!"Issue249 DAG allocation heartbeats: {allocated}"
  check.run' (default : TranslateEnv)

elab "hashcons_diamond " n:num : term => pure (input n.getNat)

#testOptimize ["Issue249SharedInputDAG"] (norm-result: 1)
  (hashcons_diamond 20) ===> (0 : Nat)

end Tests.Issue249
