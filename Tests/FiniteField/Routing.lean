import Tests.Pure
import Blaster.Smt.FiniteFieldPreflight

namespace Test.FiniteFieldRouting

open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def rejects (fragment : String) (action : TranslateEnvT α) : TranslateEnvT Unit := do
  let message? ← try
    discard action
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some message := message? | throwError "expected rejection: {fragment}"
  unless contains message fragment do throwError "wrong diagnostic: {message}"

private def noProbe : IO SolverCandidate :=
  throw <| IO.userError "unexpected capability subprocess"


private def capabilitySummary (missing : String := "") (failed : String := "") : Json :=
  let observation (name : String) := Json.mkObj [("passed", toJson (name != failed))]
  Json.mkObj [
    ("profile", toJson "solving"), ("passed", toJson true),
    ("configuration", Json.mkObj [("version", observation "version"), ("config", observation "config")]),
    ("capabilities", Json.mkObj <|
      (["setup", "solving", "model", "proof_export"].filter (· != missing)).map fun name =>
        (name, if name == "proof_export" then Json.mkObj [("passed", toJson false)] else observation name)),
    ("executable", toJson "/qualified/cvc5"),
    ("argv", toJson #["--lang", "smt2", "--incremental"])]

run_meta do
  -- An absent or failed proof exporter must not obstruct solving.
  for summary in #[capabilitySummary, capabilitySummary "proof_export"] do
    let .ok candidate := parseFiniteFieldCapability summary.compress
      | throwError "solving qualification incorrectly required proof support"
    unless candidate.cmd == "/qualified/cvc5" &&
        candidate.spawnArgs? == some #["--lang", "smt2", "--incremental"] do
      throwError "qualification lost executable/argv identity"
  for name in #["setup", "solving", "model"] do
    for summary in #[capabilitySummary name, capabilitySummary "" name] do
      let .error _ := parseFiniteFieldCapability summary.compress
        | throwError "missing/failed {name} capability accepted"
  for name in #["version", "config"] do
    let .error _ := parseFiniteFieldCapability (capabilitySummary "" name).compress
      | throwError "failed {name} qualification accepted"
  let .error _ := parseFiniteFieldCapability "not JSON"
    | throwError "malformed capability response accepted"
private def options (solver : SmtSolver) (dry := false) : TranslateEnv :=
  { (default : TranslateEnv) with
    optEnv.options.solverOptions := { solver := some solver, onlySmtLib := dry, timeout := some 1 } }

private def field := mkApp (mkConst ``Residue) (mkRawNatLit 7)
private def evidence := mkApp (mkConst ``PrimeModulus) (mkRawNatLit 7)

-- The definition's public type contains no field occurrence. Only optimization
-- exposes its theorem parameters and carrier.
private def introduced : Prop := ∀ (x y : Residue 7), x + y = x
private def removed (p : Prop) : Prop := p ∧ ((∀ (x : Residue 7), x = x) ∨ True)
private def scopedQuery : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7), x = y
private def nested : Prop := (∃ x : Residue 7, x = x)
private opaque packaged : List (Residue 7) := []
private opaque convertField (_ : Residue 11) : Residue 7 := 0

run_meta do
  withLocalDeclD `hp evidence fun _ => do
    let check : TranslateEnvT Unit := do
      withNativeFieldRequirements (mkConst ``packaged) fun fields => do
        let some admitted := fields[0]? | throwError "opaque result type hid a field"
        unless admitted.residue.modulusValue == 7 do throwError "wrong packaged field"
      withLocalDeclD `x (mkApp (mkConst ``Residue) (mkRawNatLit 11)) fun x => do
        rejects "PrimeModulus 11" <|
          withNativeFieldRequirements (mkApp (mkConst ``convertField) x) fun _ => pure ()
    discard <| check.run (options .cvc5 true)

run_meta do
  for (opts, environment, expected) in #[
      ({ solver := some .cvc5 }, none, SmtSolver.cvc5),
      ({}, some " cvc5 ", .cvc5),
      ({ solver := some .cvc5 }, some "z3", .cvc5)] do
    let .ok actual := finiteFieldBackendPolicy opts environment
      | throwError "cvc5 backend selection failed"
    unless actual == expected do throwError "wrong resolved backend"
  for (opts, environment, source) in #[
      ({ solver := some .z3 }, none, "explicit solver option"),
      ({}, none, "default"), ({}, some "z3", "BLASTER_SOLVER"),
      ({ solver := some .z3 }, some "cvc5", "explicit solver option")] do
    let .error message := finiteFieldBackendPolicy opts environment
      | throwError "z3 route accepted"
    unless contains message "backend z3" && contains message source && contains message "solver: cvc5" do
      throwError "backend diagnostic lacks resolved source: {message}"
  for mode in #[SolverMode.first, .agree] do
    let .error _ := finiteFieldBackendPolicy { solverMode := mode, onlySmtLib := true } none
      | throwError "concurrent dry run accepted"

run_meta do
  withLocalDeclD `hp evidence fun hp => do
    withLocalDeclD `x field fun x => do
      withLocalDeclD `y field fun y => do
        let query ← mkEq x y
        let check : TranslateEnvT Unit := do
          withNativeFieldRequirements query fun fields => do
            unless fields.size == 1 do throwError "missing field requirement"
            let some admitted := fields[0]? | throwError "missing admission"
            unless admitted.residue.type == field && admitted.residue.modulusValue == 7 &&
                admitted.evidence == hp do throwError "lost exact scoped admission"
          rejects "backend z3" (preflightFiniteFields query noProbe)
          unless (← get).smtEnv.smtCommands.isEmpty do throwError "rejection emitted a declaration"
        discard <| check.run (options .z3)
        let dry : TranslateEnvT Unit := do
          unless (← preflightFiniteFields query noProbe).isNone do throwError "dry run selected executable"
          setBlasterProcess
          let env ← get
          unless env.smtEnv.sessions.isEmpty && env.smtEnv.solverRecords.size == 1 do
            throwError "dry run spawned a process or lost setup record"
          let some record := env.smtEnv.solverRecords[0]? | throwError "missing setup record"
          unless record.solver == .cvc5 && record.version == "not probed (only-smt-lib)" &&
              record.setupCommands.map toString == (solverSetupCommands .cvc5 env.optEnv.options.solverOptions).map toString do
            throwError "dry run changed ordinary cvc5 setup"
        discard <| dry.run (options .cvc5 true)
        let live : TranslateEnvT Unit := do
          rejects "capability preflight failed" (preflightFiniteFields query
            (throw <| IO.userError "missing solving capability"))
          let candidate : SolverCandidate := { cmd := "/qualified/cvc5" }
          unless (← preflightFiniteFields query (pure candidate)) == some candidate do
            throwError "successful capability probe lost executable binding"
          unless (← get).smtEnv.sessions.isEmpty && (← get).smtEnv.smtCommands.isEmpty do
            throwError "preflight emitted or started a solver"
        discard <| live.run (options .cvc5)
  -- Identical carrier in the same process, but outside the proof's scope.
  withLocalDeclD `x field fun x => do
    let query ← mkEq x x
    discard <| (rejects "missing checked PrimeModulus" (preflightFiniteFields query noProbe)).run (options .cvc5)

run_meta do
  let .defnInfo info ← getConstInfo ``scopedQuery | throwError "missing scoped fixture"
  let check : TranslateEnvT Unit := do
    withNativeFieldRequirements info.value fun fields => do
      let some admitted := fields[0]? | throwError "missing admission"
      unless fields.size == 1 && admitted.residue.modulusValue == 7 do
        throwError "top-level theorem parameters lost their field evidence"
      let .ok _ := Kernel.check (← getEnv) (← getLCtx) admitted.evidence
        | throwError "admission evidence escaped its local scope"
    let optimized ← Optimize.main info.value
    withNativeFieldRequirements optimized fun fields => do
      unless fields.size == 1 do throwError "optimization lost scoped field admission"
    let .defnInfo nestedInfo ← getConstInfo ``nested | throwError "missing quantified fixture"
    rejects "residual quantified" (preflightFiniteFields nestedInfo.value noProbe)
  discard <| check.run (options .cvc5 true)

run_meta do
  withLocalDeclD `hp evidence fun _ => do
    withLocalDeclD `p (mkSort levelZero) fun p => do
      let check : TranslateEnvT Unit := do
        let before := mkConst ``introduced
        withNativeFieldRequirements before fun fields => do
          unless fields.isEmpty do throwError "preflight unfolded a term definition before optimization"
        let after ← Optimize.main before
        unless isUndeterminedResult (toResult after) do throwError "introduced fixture was settled"
        rejects "backend z3" (preflightFiniteFields after noProbe)
        rejects "backend z3" (Translate.main before)
        let removedQuery := mkApp (mkConst ``removed) p
        let residual ← Optimize.main removedQuery
        unless residual == p do throwError "optimizer did not remove irrelevant field occurrence: {residual}"
        unless (← preflightFiniteFields residual noProbe).isNone do
          throwError "removed field still required native routing"
      discard <| check.run (options .z3)

-- These go through the real optimization/dispatch entry point: a settled FF
-- query must not discover cvc5, require primality, or enter native translation.
#blaster (solver: z3) [∀ (x : Residue 7), x = x]
#blaster (solver: cvc5) [∀ (x : Residue 7), x = x]


-- Real environment resolution with an empty executable search path. Both the
-- default probe and ordinary setup would fail if the dry branch tried discovery.
private def testBinaryFreeEnvironment : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr "import Blaster\n\
      open Lean Meta Blaster.Options Blaster.Optimize Blaster.Smt Blaster.FiniteField\n\
      run_meta do\n\
      \x20 let field := mkApp (mkConst ``Residue) (mkRawNatLit 7)\n\
      \x20 let proofType := mkApp (mkConst ``PrimeModulus) (mkRawNatLit 7)\n\
      \x20 withLocalDeclD `hp proofType fun _ => do\n\
      \x20   withLocalDeclD `x field fun x => do\n\
      \x20     let query ← mkEq x x\n\
      \x20     let action : TranslateEnvT Unit := do\n\
      \x20       discard <| preflightFiniteFields query\n\
      \x20       setBlasterProcess\n\
      \x20       unless (← get).smtEnv.singleSolver == some .cvc5 && (← get).smtEnv.sessions.isEmpty do\n\
      \x20         throwError \"wrong dry-run route\"\n\
      \x20     let env := { (default : TranslateEnv) with optEnv.options.solverOptions := { onlySmtLib := true } }\n\
      \x20     discard <| action.run env\n"
    handle.flush
    let output ← IO.Process.output {
      cmd := (← IO.appPath).toString, args := #[path.toString]
      env := #[("PATH", some "/no-solver-or-python"), ("BLASTER_SOLVER", some "cvc5"),
        ("BLASTER_TIMEOUT", none), ("BLASTER_STRICT_CVC5_RESULTS", none)] }
    unless output.exitCode == 0 do
      throw <| IO.userError s!"binary-free environment route failed:\n{output.stdout}\n{output.stderr}"

#eval testBinaryFreeEnvironment

end Test.FiniteFieldRouting
