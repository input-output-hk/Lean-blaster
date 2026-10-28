import Tests.Pure

namespace Test.FiniteFieldInterfaces

open Lean Meta Blaster.Optimize Blaster.Smt

private def zeroModulus : Nat := 0
private def oneModulus : Nat := 1
private def compositeModulus : Nat := 2 * 3
private def smallModulus : Nat := 2 * 3 + 1
private def sameModulus : Nat := 3 + 4
private def largeModulus : Nat := 2 ^ 381 - 19
private opaque unknownModulus : Nat := 7
private unsafe def unsafeModulus : Nat := 7

/-! Closed Nat recognition is not a primality check. Cache keys are the original
    expressions, not normalized values, and only successful nonliteral lookups
    belong in the modulus cache. No solver process is needed by these checks. -/
private def expectModulus (e : Expr) (n : Nat) (cached : Bool) : TranslateEnvT Unit := do
  let before := (← get).optEnv.modulusCache
  unless (← getNatModulus? e) == some n do
    throwError "incorrect closed Nat modulus for {e}; expected {n}"
  let after := (← get).optEnv.modulusCache
  let expectedSize := before.size + if cached && !(before.contains e) then 1 else 0
  unless after.size == expectedSize do
    throwError "unexpected modulus cache growth for {e}"
  if cached then
    unless after.get? e == some n do
      throwError "original nonliteral expression missing from modulus cache: {e}"
  else
    unless (after.get? e).isNone do
      throwError "literal unexpectedly stored in modulus cache: {e}"

private def expectRejected (e : Expr) : TranslateEnvT Unit := do
  let before := (← get).optEnv.modulusCache.size
  unless (← getNatModulus? e).isNone do
    throwError "unsupported modulus accepted: {e}"
  unless (← get).optEnv.modulusCache.size == before do
    throwError "failed modulus lookup changed cache size"
  unless ((← get).optEnv.modulusCache.get? e).isNone do
    throwError "failed modulus lookup entered the cache"

private def expectCachePreserved (change : TranslateEnvT Unit) : TranslateEnvT Unit := do
  let before := (← get).optEnv.modulusCache
  change
  let after := (← get).optEnv.modulusCache
  unless after.size == before.size do
    throwError "environment update changed modulus cache size"
  for (e, n) in before.toList do
    unless after.get? e == some n do
      throwError "environment update lost cached modulus for {e}"

run_meta do
  let check : TranslateEnvT Unit := do
    unless (← get).optEnv.modulusCache.isEmpty do
      throwError "default modulus cache is not empty"
    -- Initialize recursive optimizer definitions once, just as translation does.
    discard <| Optimize.main (mkRawNatLit 0)
    for n in #[0, 1, 6, 7, 11, 2 ^ 381 - 19] do
      expectModulus (mkRawNatLit n) n false
    unless (← get).optEnv.modulusCache.isEmpty do
      throwError "literal-only lookups populated the modulus cache"

    let aliases := #[(mkConst ``zeroModulus, 0), (mkConst ``oneModulus, 1),
      (mkConst ``compositeModulus, 6), (mkConst ``smallModulus, 7),
      (mkConst ``sameModulus, 7), (mkConst ``largeModulus, 2 ^ 381 - 19)]
    for (e, n) in aliases do
      expectModulus e n true
    -- Equal values with different expressions retain separate original keys.
    for (e, n) in aliases.reverse do
      expectModulus e n true
    expectModulus (mkRawNatLit 7) 7 false
    expectModulus (mkRawNatLit 11) 11 false
    -- Lean's mkNatLit builds an elaborated OfNat application, not a raw literal.
    expectModulus (mkNatLit 7) 7 true
    for n in #[0, 1, 6, 7, 2 ^ 381 - 19] do
      let projected := mkProj ``OfNat 0 (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))
      expectModulus projected n true
      expectModulus projected n true

    expectRejected (mkConst ``Bool.true)
    expectRejected (mkApp (mkConst ``Int.ofNat) (mkNatLit 7))
    expectRejected (mkStrLit "7")
    expectRejected (mkConst ``Nat)
    expectRejected (mkBVar 0)
    expectRejected (mkApp2 (mkConst ``Nat.sub) (mkBVar 0) (mkBVar 0))
    -- A well-typed closed Nat may still have no computable literal value.
    expectRejected (mkConst ``unknownModulus)
    expectRejected (mkConst ``unknownModulus)
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      expectRejected n
      expectRejected (mkApp2 (mkConst ``Nat.sub) n n)
    let unknown ← mkFreshExprMVar (mkConst ``Nat)
    expectRejected unknown
    expectRejected (mkApp2 (mkConst ``Nat.sub) unknown unknown)
    unknown.mvarId!.assign (mkConst ``smallModulus)
    -- Assignment alone does not remove metavariables from the input syntax.
    expectRejected unknown
    expectModulus (← instantiateMVars unknown) 7 true
    let literalUnknown ← mkFreshExprMVar (mkConst ``Nat)
    literalUnknown.mvarId!.assign (mkRawNatLit 13)
    expectRejected literalUnknown
    expectModulus (← instantiateMVars literalUnknown) 13 false

    let env ← get
    expectCachePreserved (updateHypothesis env.optEnv.hypothesisContext env.optEnv.localRewriteCache)
    expectCachePreserved (updateMatchContext env.optEnv.matchInContext env.optEnv.localRewriteCache)
    expectCachePreserved (updateLocalContext (← mkLocalContext))
    expectCachePreserved (setNormalizeFunCall false)
    expectCachePreserved (setNormalizeFunCall true)
    expectCachePreserved (setInFunApp true)
    expectCachePreserved (setInFunApp false)
    expectCachePreserved setRestart
    expectCachePreserved resetRestart
    expectCachePreserved (updateGlobalRewriteCache (mkNatLit 17) (mkNatLit 17))
    expectCachePreserved (updateLocalRewriteCache (mkNatLit 19) (mkNatLit 19))
    for (e, n) in aliases do
      expectModulus e n true

    -- A closed, well-typed unsafe definition reaches the optimizer's existing
    -- error path. The helper must not turn this error into an ordinary miss.
    let unsafeExpr := mkConst ``unsafeModulus
    let before := (← get).optEnv.modulusCache.size
    let error : Option String ←
      try
        discard <| getNatModulus? unsafeExpr
        pure none
      catch ex => pure (some (← ex.toMessageData.toString))
    let some message := error
      | throwError "optimizer error was swallowed by modulus recognition"
    unless (message.splitOn "unsafe definition not supported").length > 1 do
      throwError "unexpected optimizer error: {message}"
    unless (← get).optEnv.modulusCache.size == before &&
        ((← get).optEnv.modulusCache.get? unsafeExpr).isNone do
      throwError "optimizer failure entered the modulus cache"
  discard <| check.run (default : TranslateEnv)

/-! Preserve the existing opaque sort mappings and declaration-cache behavior.
    A fully applied, non-opaque indexed type reaches the dispatch boundary as an
    Expr and returns none; this does not introduce a finite-field encoding. -/
run_meta do
  let check : TranslateEnvT Unit := do
    let cases := #[(mkConst ``Bool, boolSort), (mkConst ``Empty, emptySort),
      (mkConst ``Int, intSort), (mkConst ``Nat, natSort),
      (mkConst ``PEmpty [levelOne], pemptySort), (mkConst ``String, stringSort)]
    for (e, expected) in cases do
      unless (← translateOpaqueType e) == some expected do
        throwError "opaque sort mapping changed for {e}"
      let some decl := (← get).smtEnv.indTypeInstCache.get? e
        | throwError "opaque sort missing its original cache key: {e}"
      unless decl.instSort == expected do
        throwError "wrong cached opaque sort for {e}"
      let commandCount := (← get).smtEnv.smtCommands.size
      unless (← translateTypeAux (fun e => translateExpr e) e) == expected do
        throwError "type translation changed opaque sort for {e}"
      unless (← translateOpaqueType e) == some expected do
        throwError "repeated opaque sort lookup changed result for {e}"
      unless (← get).smtEnv.smtCommands.size == commandCount do
        throwError "repeated opaque sort lookup emitted duplicate declarations"
    let before := (← get).smtEnv.smtCommands.size
    let applied := mkApp (mkConst ``Fin) (mkNatLit 7)
    unless (← translateOpaqueType applied).isNone do
      throwError "non-opaque applied type unexpectedly received an opaque sort"
    unless (← get).smtEnv.smtCommands.size == before do
      throwError "non-opaque dispatch emitted declarations"
    unless (← get).smtEnv.sessions.isEmpty do
      throwError "interface checks unexpectedly started a solver"
  let env : TranslateEnv := default
  let env := { env with optEnv.options.solverOptions.onlySmtLib := true }
  discard <| check.run env

end Test.FiniteFieldInterfaces
