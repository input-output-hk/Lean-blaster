import Tests.Pure
import Blaster.FiniteField.Recognize

namespace Test.FiniteFieldOpaque

open Lean Meta Blaster.Optimize Blaster.Smt Blaster.FiniteField

private def modulusAlias : Nat := 3 + 4
private instance modulusNonzero : NeZero modulusAlias := ⟨by decide⟩
private abbrev RingAlias := Residue modulusAlias
private opaque unknownModulus : Nat := 7

private def add7 (x y : Residue 7) := x + y
private def mul7 (x y : Residue 7) := x * y
private def neg7 (x : Residue 7) := -x
private def sub7 (x y : Residue 7) := x - y
private def literal7 : Residue 7 := 19
private def power7 (x : Residue 7) (n : Nat) := x ^ n
private def add11 (x y : Residue 11) := x + y
private def aliasAdd (x y : RingAlias) := x + y
private def aliasLiteral : RingAlias := 19
private def symbolicAdd {p : Nat} [NeZero p] (x y : Residue p) := x + y
private def partialAdd : Residue 7 → Residue 7 → Residue 7 := HAdd.hAdd
private def nested (x y : Residue 7) := -(x + y) * (x - y) + x ^ 3
private def directAdd (x y : Residue 7) := Add.add x y
private def directMul (x y : Residue 7) := Mul.mul x y
private def directSub (x y : Residue 7) := Sub.sub x y
private def literalIndex : Nat := 19
private def indexedLiteral : Residue 7 := @OfNat.ofNat _ literalIndex inferInstance
private def natCast (n : Nat) : Residue 7 := n
private def intCast (n : Int) : Residue 7 := n
private def addDictionary : Add (Residue 7) := inferInstance
private def dictionaryAlias (x y : Residue 7) :=
  @HAdd.hAdd _ _ _ (@instHAdd _ addDictionary) x y
private def localDictionary [Add (Residue 7)] (x y : Residue 7) := x + y

private def unrelatedAdd : Add (Residue 7) := ⟨fun x _ => x⟩
private def unrelatedMul : Mul (Residue 7) := ⟨fun _ y => y⟩
private def unrelatedNeg : Neg (Residue 7) := ⟨fun x => x⟩
private def unrelatedSub : Sub (Residue 7) := ⟨fun x _ => x⟩
private def unrelatedLiteral : OfNat (Residue 7) 19 := ⟨0⟩
private def unrelatedPower : HPow (Residue 7) Nat (Residue 7) := ⟨fun x _ => x⟩
private def customAdd (x y : Residue 7) := @HAdd.hAdd _ _ _ (@instHAdd _ unrelatedAdd) x y
private def customMul (x y : Residue 7) := @HMul.hMul _ _ _ (@instHMul _ unrelatedMul) x y
private def customNeg (x : Residue 7) := @Neg.neg _ unrelatedNeg x
private def customSub (x y : Residue 7) := @HSub.hSub _ _ _ (@instHSub _ unrelatedSub) x y
private def customLiteral : Residue 7 := @OfNat.ofNat _ 19 unrelatedLiteral
private def customPower (x : Residue 7) (n : Nat) := @HPow.hPow _ _ _ unrelatedPower x n

private def expectUnsupported (action : TranslateEnvT α) : TranslateEnvT Unit := do
  let error ← try
    discard action
    pure none
  catch ex => pure (some (← ex.toMessageData.toString))
  let some message := error | throwError "Residue unexpectedly translated before native emission is implemented"
  unless (message.splitOn "Residue").length > 1 do
    throwError "wrong translation boundary failure: {message}"
  unless (← get).smtEnv.smtCommands.isEmpty do
    throwError "unsupported Residue translation emitted SMT commands"

private def expectPreserved (body : Expr) : TranslateEnvT Unit := do
  updateLocalContext (← mkLocalContext)
  let f := body.getAppFn
  let args := body.getAppArgs
  unless (← isOpaqueFunExpr f args) do
    throwError "canonical operation is not opaque: {body}"
  unless (← isNotFoldable f args) do
    throwError "generic unfolding guard missed canonical operation: {body}"
  unless (← getUnfoldFunDef? f args).isNone do
    throwError "generic unfolding exposed the representation: {body}"
  unless (← reduceApp? f args).isNone do
    throwError "application reduction exposed the representation: {body}"
  let normalized ← Optimize.main body
  unless normalized.getAppFn == f do
    throwError "optimizer changed canonical operation head: {body} became {normalized}"
  unless (← isOpaqueFunExpr normalized.getAppFn normalized.getAppArgs) do
    throwError "optimized operation lost its instantiated dictionary: {normalized}"
  unless ← isDefEq (← inferType normalized) (← inferType body) do
    throwError "optimizer changed the instantiated operation type"
  expectUnsupported (translateApp normalized (fun e => translateExpr e))
  expectUnsupported (translateOpaqueFun f f.constName! args)

/-! Exercise the generic optimizer and translator, not just the opacity predicate.
    Every case uses the elaborated dictionary, including aliases and symbolic p. -/
run_meta do
  for name in #[``add7, ``mul7, ``neg7, ``sub7, ``literal7, ``power7,
      ``add11, ``aliasAdd, ``aliasLiteral, ``symbolicAdd, ``partialAdd,
      ``directAdd, ``directMul, ``directSub, ``indexedLiteral,
      ``natCast, ``intCast, ``dictionaryAlias] do
    let .defnInfo info ← getConstInfo name | throwError "expected operation fixture"
    Lean.Meta.lambdaTelescope info.value fun _ body => do
      discard <| (expectPreserved body).run (default : TranslateEnv)
  for name in #[``customAdd, ``customMul, ``customNeg, ``customSub,
      ``customLiteral, ``customPower, ``localDictionary] do
    let .defnInfo info ← getConstInfo name | throwError "expected custom fixture"
    Lean.Meta.lambdaTelescope info.value fun _ body => do
      let check : TranslateEnvT Unit := do
        updateLocalContext (← mkLocalContext)
        if ← isOpaqueFunExpr body.getAppFn body.getAppArgs then
          throwError "unrelated operation dictionary was treated as canonical: {body}"
        if ← isNotFoldable body.getAppFn body.getAppArgs then
          throwError "unrelated operation dictionary was blocked by the unfolding guard"
        unless (← getUnfoldFunDef? body.getAppFn body.getAppArgs).isSome do
          throwError "custom dictionary cannot unfold"
      discard <| check.run (default : TranslateEnv)

-- Even a canonical dictionary for another modulus must not match.
run_meta do
  let .defnInfo info ← getConstInfo ``add7 | throwError "expected addition fixture"
  Lean.Meta.lambdaTelescope info.value fun _ body => do
    let otherType := mkApp (mkConst ``Residue) (mkRawNatLit 11)
    let other ← synthInstance (← mkAppM ``HAdd #[otherType, otherType, otherType])
    if ← isOpaqueResidueOperation body.getAppFn.constName! (body.getAppArgs.set! 3 other) then
      throwError "dictionary for modulus eleven matched modulus seven"

private partial def checkResidueTree (e : Expr) : TranslateEnvT Nat := do
  if let .const n _ := e.getAppFn then
    if ← isOpaqueResidueOperation n e.getAppArgs then
      let mut count := 1
      for arg in e.getAppArgs do
        count := count + (← checkResidueTree arg)
      return count
  return 0

run_meta do
  let .defnInfo info ← getConstInfo ``nested | throwError "expected nested fixture"
  Lean.Meta.lambdaTelescope info.value fun _ body => do
    let check : TranslateEnvT Unit := do
      let before ← checkResidueTree body
      let normalized ← Optimize.main body
      let after ← checkResidueTree normalized
      unless before == 6 && after == before do
        throwError "nested operation tree was unfolded: {before} → {after}: {normalized}"
    discard <| check.run (default : TranslateEnv)

private def residueType (p : Expr) := mkApp (mkConst ``Residue) p

run_meta do
  let check : TranslateEnvT Unit := do
    discard <| Optimize.main (mkRawNatLit 0)
    for (p, value) in #[(mkRawNatLit 0, 0), (mkRawNatLit 1, 1),
        (mkRawNatLit 2, 2), (mkRawNatLit 6, 6), (mkRawNatLit 7, 7),
        (mkRawNatLit 11, 11), (mkConst ``modulusAlias, 7)] do
      let t := residueType p
      let some descriptor ← getResidueDescriptor? t
        | throwError "closed residue descriptor rejected: {t}"
      unless descriptor.type == t && descriptor.modulus == p && descriptor.modulusValue == value do
        throwError "descriptor erased the applied type or modulus: {t}"
      if isCompatibleRelationalType t then
        throwError "Residue must not be registered as ordered"
      expectUnsupported (translateOpaqueType t)
      expectUnsupported (translateTypeAux (fun e => translateExpr e) t)
    let aliasType := mkConst ``RingAlias
    let some descriptor ← getResidueDescriptor? aliasType
      | throwError "carrier alias rejected"
    unless descriptor.type == aliasType && descriptor.modulusValue == 7 do
      throwError "carrier alias lost its original type"
    for t in #[mkConst ``Residue, mkConst ``Nat, mkApp (mkConst ``Fin) (mkRawNatLit 7),
        residueType (mkConst ``unknownModulus), residueType (mkBVar 0)] do
      unless (← getResidueDescriptor? t).isNone do
        throwError "unsupported descriptor accepted: {t}"
    withLocalDeclD `p (mkConst ``Nat) fun p => do
      unless (← getResidueDescriptor? (residueType p)).isNone do
        throwError "open modulus admitted as concrete"
    let p ← mkFreshExprMVar (mkConst ``Nat)
    p.mvarId!.assign (mkRawNatLit 7)
    unless (← getResidueDescriptor? (residueType p)).isNone do
      throwError "uninstantiated metavariable admitted"
    let typeUnknown ← mkFreshExprMVar (mkSort levelOne)
    typeUnknown.mvarId!.assign (residueType (mkRawNatLit 7))
    unless (← getResidueDescriptor? typeUnknown).isNone do
      throwError "uninstantiated type metavariable admitted"
    let seven := residueType (mkRawNatLit 7)
    let eleven := residueType (mkRawNatLit 11)
    let some a ← getResidueDescriptor? seven | throwError "missing modulus seven"
    let some b ← getResidueDescriptor? eleven | throwError "missing modulus eleven"
    if a.type == b.type || a.modulusValue == b.modulusValue then
      throwError "different residue moduli collapsed"
    for (t, expected) in #[(mkConst ``Nat, natSort), (mkConst ``Int, intSort)] do
      unless (← translateOpaqueType t) == some expected do
        throwError "existing opaque numeric sort changed"
    unless (← translateOpaqueType (mkApp (mkConst ``Fin) (mkRawNatLit 7))).isNone do
      throwError "Fin acquired a nominal opaque sort"
    unless (← isOpaqueFun ``Nat.add #[]) && (← isOpaqueFun ``Int.mul #[]) do
      throwError "existing numeric opacity changed"
    unless isCompatibleRelationalType (mkConst ``Nat) && isCompatibleRelationalType (mkConst ``Int) do
      throwError "existing ordered types changed"
    unless (← get).smtEnv.sessions.isEmpty do
      throwError "pure opacity checks started a solver"
  discard <| check.run (default : TranslateEnv)

run_cmd do
  for axiomName in ← Lean.collectAxioms ``modulusNonzero do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected modulus proof axiom: {axiomName}"

end Test.FiniteFieldOpaque
