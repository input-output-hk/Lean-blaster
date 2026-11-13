import Blaster

/-! Template used by `benchmark_reconstruction.py`. Each process elaborates one real
`blaster (gen-proof: 1)` theorem, including optimizer certificates and kernel checks. -/
open Lean Meta Elab Term Command Blaster.Reconstruct

-- BENCHMARK_DEFINITIONS

elab "#reconstruction_bench " p:term : command => do
  let base ← getEnv
  let start ← IO.monoMsNow
  let name := mkIdent `benchmarkProof
  elabCommand (← `(theorem $name : $p := by
    blaster (gen-proof: 1) (timeout: BENCHMARK_TIMEOUT)))
  if (← get).messages.hasErrors then return
  liftTermElabM do
    let info ← getConstInfo `benchmarkProof
    let proof := info.value!
    -- `getConstInfo` waits for asynchronous theorem elaboration. Include that
    -- wait rather than timing only the scheduling of the theorem command.
    let elapsed := (← IO.monoMsNow) - start
    let start ← IO.monoMsNow
    if let some err ← kernelCheck info.type proof then throwError err
    let recheckMs := (← IO.monoMsNow) - start
    let axioms ← match ← checkProofAxioms proof with
      | .ok axioms => pure axioms
      | .error err => throwError err
    -- Count the reachable new declarations as a shared forest (including types).
    -- Imported library lemmas remain references. Unused generated helpers are excluded.
    let mut todo := proof.getUsedConstants
    let mut seen : NameSet := {}
    let mut forest := #[info.type, proof]
    let mut auxiliaries := 0
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if base.contains n || seen.contains n then continue
      seen := seen.insert n
      let i ← getConstInfo n
      forest := forest.push i.type
      todo := todo ++ i.type.getUsedConstants
      if let some v := i.value? then
        forest := forest.push v
        todo := todo ++ v.getUsedConstants
      auxiliaries := auxiliaries + 1
    let expanded ← SmtProof.Local.inlineNewConstants base proof
    let output := Json.mkObj [
      ("generation_ms", toJson elapsed), ("root_recheck_ms", toJson recheckMs),
      ("expanded_dag_nodes", toJson (SmtProof.dagStats expanded).1),
      ("stored_forest_nodes", toJson (SmtProof.dagStats (forest.foldl (mkApp2 (mkConst ``And)) (mkConst ``True))).1),
      ("reachable_auxiliaries", toJson auxiliaries),
      ("axioms", toJson (axioms.toList.map toString))]
    let some path ← IO.getEnv "BLASTER_BENCH_OUTPUT" | throwError "missing benchmark output path"
    IO.FS.writeFile path output.pretty

-- BENCHMARK_THEOREM
