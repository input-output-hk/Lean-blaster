import Blaster.FiniteField.InverseGraph
import Tests.FiniteField.Field
import Lean.Util.CollectAxioms

namespace Test.FiniteFieldAxiomAudit

open Lean Blaster.FiniteField

-- Unlike collectAxioms alone, this guard also rejects a missing audit target.
-- The same throwing guard is exercised by every negative control below.
run_cmd Lean.Elab.Command.liftCoreM do
  let audit : Name → CoreM Unit := fun declaration => do
    unless ((← getEnv).checked.get.find? declaration).isSome do
      throwError "missing field axiom audit declaration: {declaration}"
    for axiomName in ← collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected field axiom in {declaration}: {axiomName}"

  let declarations := #[
    ``Residue.instInv, ``Residue.instDiv, ``Residue.instZPow, ``Residue.instField,
    ``Residue.rep_pow, ``Residue.inv_eq_pow, ``Residue.coprime_rep,
    ``Residue.inv_zero, ``Residue.zero_ne_one, ``Residue.mul_inv_cancel,
    ``Residue.eq_inv_of_mul_eq_one, ``Residue.inv_one, ``Residue.inv_inv,
    ``Residue.zpow_natCast, ``Residue.zpow_neg, ``Residue.div_eq_mul_inv,
    ``Residue.InverseGraph, ``Residue.inverseGraph_iff,
    ``Residue.inverseGraph_total, ``Residue.inverseGraph_functional,
    ``Residue.div_eq_mul_of_inverseGraph,
    ``Test.FiniteFieldField.primeTwo, ``Test.FiniteFieldField.primeSeven,
    ``Test.FiniteFieldField.primeModulusTwo, ``Test.FiniteFieldField.primeModulusSeven,
    ``Test.FiniteFieldField.inverseZero, ``Test.FiniteFieldField.inverseOne,
    ``Test.FiniteFieldField.inverseInvolution, ``Test.FiniteFieldField.inverseCancel,
    ``Test.FiniteFieldField.divisionDefinition, ``Test.FiniteFieldField.divisionZero,
    ``Test.FiniteFieldField.zeroDivision, ``Test.FiniteFieldField.zeroByZero,
    ``Test.FiniteFieldField.selfDivision, ``Test.FiniteFieldField.divisionMulCancel,
    ``Test.FiniteFieldField.naturalZeroZero, ``Test.FiniteFieldField.naturalZeroPositive,
    ``Test.FiniteFieldField.integerNaturalAgreement, ``Test.FiniteFieldField.integerNegative,
    ``Test.FiniteFieldField.integerNegation, ``Test.FiniteFieldField.integerZeroNegative,
    ``Test.FiniteFieldField.characteristicTwo, ``Test.FiniteFieldField.characteristicSeven,
    ``Test.FiniteFieldField.concreteTwo, ``Test.FiniteFieldField.concreteSeven,
    ``Test.FiniteFieldField.divisionNotFinDivision, ``Test.FiniteFieldField.compositeRingOnly,
    ``Test.FiniteFieldField.compositeArithmetic,
    ``Test.FiniteFieldField.nonzeroModulusNotField,
    ``Test.FiniteFieldField.compatibilityCarrier,
    ``Test.FiniteFieldField.compatibilityDivision]
  for declaration in declarations do
    audit declaration

  let expectRejection : Name → CoreM Unit := fun declaration => do
    let rejected ← try
      audit declaration
      pure false
    catch _ => pure true
    unless rejected do
      throwError "field axiom audit accepted negative control: {declaration}"

  let arbitrary := `Test.FiniteFieldAxiomAudit.temporaryArbitraryAxiom
  let inner := `Test.FiniteFieldAxiomAudit.temporaryDependency
  let outer := `Test.FiniteFieldAxiomAudit.temporaryWrapper
  let missing := `Test.FiniteFieldAxiomAudit.missingAuditTarget
  let temporaryNames := #[arbitrary, inner, outer, missing]
  for declaration in temporaryNames do
    if (← getEnv).contains declaration then
      throwError "field audit negative-control name already exists: {declaration}"
  expectRejection missing

  -- Preserve the constant's universes and type, so even polymorphic trust
  -- declarations can be tested without constructing any untrusted proof.
  let addWrapper : Name → Name → CoreM Unit := fun name dependency => do
    let info ← getConstInfo dependency
    addDecl (.defnDecl {
      name := name
      levelParams := info.levelParams
      type := info.type
      value := mkConst dependency (info.levelParams.map Level.param)
      hints := .abbrev
      safety := .safe
    })

  -- Every control is two definitions away from its forbidden axiom. Both the
  -- presence of that transitive dependency and rejection by the actual guard
  -- are checked. withEnv restores the environment even if a check throws.
  for forbidden in #[``sorryAx, ``Lean.trustCompiler, ``Lean.ofReduceBool, arbitrary] do
    withEnv (← getEnv) do
      if forbidden == arbitrary then
        addDecl (.axiomDecl {
          name := arbitrary
          levelParams := []
          type := mkConst ``True
          isUnsafe := false
        })
      addWrapper inner forbidden
      addWrapper outer inner
      unless (← collectAxioms outer).contains forbidden do
        throwError "field audit failed to follow dependency from {outer} to {forbidden}"
      expectRejection outer

  -- No synthetic wrapper or arbitrary axiom may escape the scoped controls.
  for declaration in temporaryNames do
    if (← getEnv).contains declaration then
      throwError "field audit leaked temporary declaration: {declaration}"

end Test.FiniteFieldAxiomAudit
