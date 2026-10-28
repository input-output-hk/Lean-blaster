import Tests.Pure
import Blaster.FiniteField.Admission

namespace Test.FiniteFieldPrimality

open Lean Meta Blaster.Optimize Blaster.FiniteField

private theorem prime2 : Prime 2 :=
  prime_of_bounded 2 1 (by decide) (by decide) (by decide)
private theorem prime7 : Prime 7 :=
  prime_of_bounded 7 2 (by decide) (by decide) (by decide)
private theorem prime11 : Prime 11 :=
  prime_of_bounded 11 3 (by decide) (by decide) (by decide)

private theorem evidence2 : PrimeModulus 2 := ⟨prime2⟩
private theorem evidence7 : PrimeModulus 7 := ⟨prime7⟩
private theorem evidence11 : PrimeModulus 11 := ⟨prime11⟩
private def seven : Nat := 3 + 4
private abbrev SevenRing := Residue seven
private theorem aliasEvidence : PrimeModulus seven := ⟨prime7⟩
private opaque unknown : Nat := 7

/-- Nonzeroness and the field lower bound follow from the mathematical proof. -/
theorem checkedConsequences (p : Nat) [PrimeModulus p] : p ≠ 0 ∧ 2 ≤ p :=
  ⟨PrimeModulus.ne_zero p, PrimeModulus.two_le p⟩

/-- Prime evidence supplies the existing ring's nonzero requirement. -/
theorem checkedNonzeroInstance (p : Nat) [PrimeModulus p] : NeZero p := inferInstance

/-- Composite rings still have their original zero divisors, without admission. -/
theorem compositeRing : (2 : Residue 6) ≠ 0 ∧ (3 : Residue 6) ≠ 0 ∧
    (2 : Residue 6) * 3 = 0 := by decide

/-- Characteristic two is a valid prime characteristic. -/
theorem characteristicTwo (a : Residue 2) : a + a = 0 := by grind

private def descriptor (n : Nat) : TranslateEnvT ResidueDescriptor := do
  let some result ← getResidueDescriptor? (mkApp (mkConst ``Residue) (mkRawNatLit n))
    | throwError "concrete residue recognition failed for {n}"
  return result

private def rejects (category : String) (action : TranslateEnvT α) : TranslateEnvT Unit := do
  let message? ← try
    discard action
    pure none
  catch ex => pure (some (← ex.toMessageData.toString))
  let some message := message? | throwError "admission unexpectedly accepted: {category}"
  unless (message.splitOn category).length > 1 do
    throwError "wrong admission diagnostic, expected {category}: {message}"

private def accepts (d : ResidueDescriptor) (proof? : Option Expr := none) :
    TranslateEnvT NativeFieldAdmission := do
  let admitted ← admitNativeField d proof?
  unless admitted.residue.type == d.type && admitted.residue.modulus == d.modulus &&
      admitted.residue.modulusValue == d.modulusValue do
    throwError "admission changed the original residue descriptor"
  let expected := mkApp (mkConst ``PrimeModulus) (mkRawNatLit d.modulusValue)
  let .ok type := Kernel.check (← getEnv) (← getLCtx) admitted.evidence
    | throwError "admission returned unchecked evidence"
  unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx) type expected do
    throwError "admission returned evidence for another modulus"
  return admitted

run_meta do
  let check : TranslateEnvT Unit := do
    discard <| Optimize.main (mkRawNatLit 0)
    for n in #[0, 1] do
      rejects "below 2" (admitNativeField (← descriptor n))
    -- Recognition succeeds even for composites; it is not field admission.
    for n in #[6, 9, 15, 7, 11] do
      rejects "missing checked PrimeModulus" (admitNativeField (← descriptor n))
    for (n, proof) in #[(2, ``evidence2), (7, ``evidence7), (11, ``evidence11)] do
      discard <| accepts (← descriptor n) (some (mkConst proof))
      rejects "missing checked PrimeModulus" (admitNativeField (← descriptor n))
    rejects "evidence type/modulus mismatch"
      (admitNativeField (← descriptor 6) (some (mkConst ``evidence7)))
    let d7 ← descriptor 7
    let d11 ← descriptor 11
    let some aliasD ← getResidueDescriptor? (mkConst ``SevenRing)
      | throwError "reducible residue alias was not recognized"
    discard <| accepts aliasD (some (mkConst ``evidence7))
    discard <| accepts d7 (some (mkConst ``aliasEvidence))
    rejects "missing checked PrimeModulus" (admitNativeField aliasD)
    rejects "evidence type/modulus mismatch" (admitNativeField d7 (some (mkConst ``evidence11)))
    rejects "evidence type/modulus mismatch" (admitNativeField d7 (some (mkConst ``prime7)))
    rejects "evidence type/modulus mismatch" (admitNativeField d7 (some (mkConst ``True.intro)))
    rejects "evidence type/modulus mismatch" (admitNativeField d7 (some (mkConst ``Bool.true)))
    rejects "descriptor mismatch" (admitNativeField { d7 with modulusValue := 11 }
      (some (mkConst ``evidence7)))
    rejects "descriptor mismatch" (admitNativeField { d7 with modulus := mkRawNatLit 11 }
      (some (mkConst ``evidence7)))
    rejects "concrete closed Residue" (admitNativeField
      { d7 with type := mkApp (mkConst ``Fin) (mkRawNatLit 7) } (some (mkConst ``evidence7)))
    rejects "concrete closed Residue" (admitNativeField
      { d7 with type := mkApp (mkConst ``Residue) (mkConst ``unknown), modulus := mkConst ``unknown })
    withLocalDeclD `p (mkConst ``Nat) fun p => do
      rejects "concrete closed Residue" (admitNativeField
        { type := mkApp (mkConst ``Residue) p, modulus := p, modulusValue := 7 })
      -- Even a locally assumed prime cannot enable symbolic native solving.
      withLocalDeclD `hp (mkApp (mkConst ``PrimeModulus) p) fun hp => do
        rejects "concrete closed Residue" (admitNativeField
          { type := mkApp (mkConst ``Residue) p, modulus := p, modulusValue := 7 } (some hp))
    for p in #[mkBVar 0, ← mkFreshExprMVar (mkConst ``Nat)] do
      rejects "concrete closed Residue" (admitNativeField
        { type := mkApp (mkConst ``Residue) p, modulus := p, modulusValue := 7 })
    let expected := mkApp (mkConst ``PrimeModulus) (mkRawNatLit 7)
    let unresolved ← mkFreshExprMVar expected
    rejects "unresolved metavariables" (admitNativeField d7 (some unresolved))
    rejects "failed kernel checking" (admitNativeField d7
      (some (mkApp (mkConst ``True.intro) (mkConst ``True.intro))))
    -- Same translation state, including numeric recognition caches, crosses
    -- the scope boundary. Neither automatic lookup nor explicit stale evidence leaks.
    let escaped ← withLocalDeclD `hp expected fun hp => do
      let a ← accepts d7
      discard <| accepts aliasD
      rejects "missing checked PrimeModulus" (admitNativeField d11)
      discard <| accepts d7 (some hp)
      return a.evidence
    rejects "missing checked PrimeModulus" (admitNativeField d7)
    rejects "failed kernel checking" (admitNativeField d7 (some escaped))
    withLocalDecl `hp .instImplicit expected fun _ => do
      discard <| accepts d7
    rejects "missing checked PrimeModulus" (admitNativeField d7)
    -- A local let must be audited through its value, not accepted merely by type.
    let solverClaim := mkApp (mkConst ``Blaster.Tactic.blasterProven [levelZero]) expected
    rejects "forbidden axiom" (admitNativeField d7 (some solverClaim))
    withLetDecl `hp expected solverClaim fun _ => do
      rejects "forbidden axiom" (admitNativeField d7)
    -- Exercise the existing compiler/native trust axioms without adding an axiom
    -- or declaring a theorem that depends on them. Even unused proof arguments
    -- in the supplied expression are conservatively audited.
    for name in #[``Lean.trustCompiler, ``Lean.ofReduceBool] do
      let c := mkConst name
      let type ← inferType c
      let wrapped := mkApp (mkLambda `native .default type (mkConst ``evidence7)) c
      rejects "forbidden axiom" (admitNativeField d7 (some wrapped))
    withLetDecl `hp expected (mkConst ``evidence7) fun _ => do
      discard <| accepts d7
    rejects "missing checked PrimeModulus" (admitNativeField d7)
    -- Inside `theorem t : PrimeModulus 7 := by ...` the local context holds an
    -- auxiliary declaration for `t` itself. Using it would be circular evidence.
    withAuxDecl `self expected `Test.FiniteFieldPrimality.self fun _ => do
      rejects "missing checked PrimeModulus" (admitNativeField d7)
    unless (← get).smtEnv.smtCommands.isEmpty && (← get).smtEnv.sessions.isEmpty do
      throwError "pure admission emitted solver commands or created a solver session"
  discard <| check.run (default : TranslateEnv)
  -- A fresh call/state also has no admission history.
  let fresh : TranslateEnvT Unit := do
    rejects "missing checked PrimeModulus" (admitNativeField (← descriptor 7))
  discard <| fresh.run (default : TranslateEnv)

run_cmd do
  for declaration in #[``prime2, ``prime7, ``prime11, ``evidence2, ``evidence7,
      ``evidence11, ``aliasEvidence, ``checkedConsequences, ``checkedNonzeroInstance,
      ``compositeRing, ``characteristicTwo, ``PrimeModulus.two_le,
      ``PrimeModulus.pos, ``PrimeModulus.ne_zero] do
    for axiomName in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected primality axiom in {declaration}: {axiomName}"

end Test.FiniteFieldPrimality
