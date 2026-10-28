import Blaster.FiniteField.Prime
import Blaster.FiniteField.Recognize

open Lean Meta

namespace Blaster.FiniteField

/-- Admission retains the exact recognized carrier and a checked `PrimeModulus`
proof. Local free variables in the evidence belong to the current Lean context;
this value is not a context-independent capability or a cache entry. -/
structure NativeFieldAdmission where
  residue : ResidueDescriptor
  evidence : Expr

/-- Check the complete proof dependency closure, including the values of local
lets. Abstracting only used locals prevents unrelated hypotheses from affecting
admission. Only Lean's three ordinary foundational axioms are allowed. -/
private def checkEvidenceAxioms (proof : Expr) : MetaM Unit := do
  let closed ← mkLambdaFVars (← getLCtx).getFVars proof
    (usedOnly := true) (generalizeNondepLet := false)
  if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
    throwError "native field admission: evidence is open or belongs to a different local context"
  match Kernel.check (← getEnv) {} closed with
  | .error _ => throwError "native field admission: evidence failed kernel checking"
  | .ok _ => pure ()
  let mut visited : NameSet := {}
  for constant in closed.getUsedConstants do
    for axiomName in ← collectAxioms constant do
      unless visited.contains axiomName do
        visited := visited.insert axiomName
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "native field admission: evidence depends on forbidden axiom {axiomName}; supply a kernel-checked primality proof without solver or native-decision trust"

/-- Admit a recognized concrete residue carrier only with matching mathematical
primality evidence. Callers may supply a `PrimeModulus p` proof explicitly, or
place one in the current local context (an ordinary hypothesis or local instance).

The descriptor is revalidated, including kernel equality of its modulus and full
carrier to the normalized numeral. No Boolean primality result, solver response,
global instance search, admission cache, solver discovery, or SMT command is used.
Every call checks the current context anew; a saved result must be readmitted if
used in another context. Numeric recognition alone never grants admission. -/
def admitNativeField (residue : ResidueDescriptor) (evidence? : Option Expr := none) :
    Optimize.TranslateEnvT NativeFieldAdmission := do
  let some actual ← getResidueDescriptor? residue.type
    | throwError "native field admission: expected a concrete closed Residue modulus; symbolic, open, or unsupported carriers are not admitted"
  let env ← getEnv
  let lctx ← getLCtx
  let numeral := mkRawNatLit actual.modulusValue
  let expectedCarrier := mkApp (mkConst ``Residue) numeral
  if residue.modulus.hasFVar || residue.modulus.hasMVar || residue.modulus.hasLooseBVars ||
      residue.modulusValue != actual.modulusValue ||
      !(Kernel.isDefEqGuarded env lctx residue.modulus numeral) ||
      !(Kernel.isDefEqGuarded env lctx actual.modulus numeral) ||
      !(Kernel.isDefEqGuarded env lctx residue.type expectedCarrier) then
    throwError "native field admission: residue type/modulus descriptor mismatch; use getResidueDescriptor? for this exact carrier"
  match Kernel.check env lctx residue.type with
  | .error _ => throwError "native field admission: residue carrier failed kernel checking"
  | .ok _ => pure ()
  if actual.modulusValue < 2 then
    throwError "native field admission: modulus {actual.modulusValue} is below 2 and cannot be prime"
  let expected := mkApp (mkConst ``PrimeModulus) numeral
  let mut candidate := evidence?
  if candidate.isNone then
    for declaration in lctx do
      if Kernel.isDefEqGuarded env lctx declaration.type expected then
        candidate := some declaration.toExpr
        break
  let some proof := candidate
    | throwError "native field admission: missing checked PrimeModulus {actual.modulusValue} evidence; supply a proof explicitly or in the current local context (composite Residue rings remain usable without native admission)"
  if proof.hasMVar || proof.hasLooseBVars then
    throwError "native field admission: evidence contains unresolved metavariables or loose bound variables"
  let proofType ← match Kernel.check env lctx proof with
    | .error _ => throwError "native field admission: evidence failed kernel checking in the current local context"
    | .ok type => pure type
  unless Kernel.isDefEqGuarded env lctx proofType expected do
    throwError "native field admission: evidence type/modulus mismatch; expected PrimeModulus {actual.modulusValue}, got {proofType}"
  checkEvidenceAxioms proof
  return { residue, evidence := proof }

end Blaster.FiniteField
