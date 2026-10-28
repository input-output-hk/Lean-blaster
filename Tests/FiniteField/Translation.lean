import Tests.Pure
import Tests.FiniteField.LargePrime
import Blaster.Smt.Translate.FiniteField

/-! Solver-independent end-to-end polynomial transcript and scope regressions.
The direct path deliberately bypasses optimization, so identities and literal
powers must really be translated rather than discharged by simplification. -/
namespace Test.FiniteFieldTranslation

open Lean Meta Blaster.FiniteField Blaster.Optimize Blaster.Smt

private def options : TranslateEnv :=
  { (default : TranslateEnv) with
    optEnv.options.solverOptions := {
      solver := some .cvc5
      onlySmtLib := true
      timeout := some 1 } }

private def body (name : Name) : MetaM Expr := do
  let .defnInfo info ← getConstInfo name | throwError "missing query definition {name}"
  return info.value

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def transcript (env : TranslateEnv) : String :=
  String.intercalate "\n" (env.smtEnv.smtCommands.toList.map toString)

private def require (text fragment : String) : MetaM Unit := do
  unless contains text fragment do throwError "missing transcript fragment {fragment}:\n{text}"

private def direct (query : Expr) : MetaM TranslateEnv := do
  let action : TranslateEnvT Unit := do
    let candidate ← preflightFiniteFields query
    unless candidate.isNone do throwError "dry translation selected an executable"
    setBlasterProcess candidate
    let some term ← translatePolynomial query | throwError "native query fell through"
    assertTerm (notSmt term)
  let (_, env) ← action.run options
  unless env.smtEnv.sessions.isEmpty do throwError "pure translation started a solver"
  return env

private def rejects (fragment : String) (action : TranslateEnvT α) : MetaM Unit := do
  let message ← try
    discard <| action.run options
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some message := message | throwError "accepted unsupported query: {fragment}"
  unless contains message fragment do
    throwError "wrong rejection; expected {fragment}, got {message}"

private def rejectQuery (name : Name) (fragment : String) : MetaM Unit := do
  let query ← body name
  rejects fragment do
    let candidate ← preflightFiniteFields query
    setBlasterProcess candidate
    discard <| translatePolynomial query

private def arithmetic : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7),
  (x + y) * (-x) - y = (-9 : Residue 7) ∧
  ((x ≠ y ∨ x = 16) ↔ ¬ (x = y ∧ y = 0))

private def booleans : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7) (b : Bool),
  (if x = y then x + y else x * y) = x ∧ (b = true → x ≠ y)

private def twoFields : Prop :=
  ∀ (_ : PrimeModulus 7) (_ : PrimeModulus 11)
    (x y : Residue 7) (z w : Residue 11),
    x + y = y + x ∧ z + w = w + z

private def modulusAlias : Nat := 3 + 4
private instance : NeZero modulusAlias := ⟨by decide⟩
private def aliasFields : Prop := ∀ (_ : PrimeModulus 7)
    (x : Residue modulusAlias) (y : Residue 7),
    x + x = x ∧ y + y = y ∧ x * x = x ∧ y * y = y

private def characteristicTwo : Prop := ∀ (_ : PrimeModulus 2) (x : Residue 2),
  2 * x = 0 → x = 0

private def powers : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7),
  (0 : Residue 7) ^ (0 : Nat) = 1 ∧ (0 : Residue 7) ^ (3 : Nat) = 0 ∧
  x ^ (6 : Nat) = y ∧ x ^ (7 : Nat) = y ∧
  x ^ (1048575 : Nat) = y ^ (1048575 : Nat)

private def largeField : Prop :=
  ∀ (_ : PrimeModulus Test.FiniteFieldLargePrime.curve25519)
    (x : Residue Test.FiniteFieldLargePrime.curve25519), x + 1 = -x

private def mainQuery : Prop := ∀ (_ : PrimeModulus 7) (x y : Residue 7), x + y = x

run_meta do
  let env ← direct (← body ``arithmetic)
  let text := transcript env
  for fragment in #["(define-sort @FF7", "(_ FiniteField 7)",
      "(define-fun @FF7.add", "(define-fun @FF7.mul", "(define-fun @FF7.neg",
      "(define-fun @FF7.sub", "ff.add", "ff.mul", "ff.neg", "#f5m7", "#f2m7",
      "(assert (not ", "(and ", "(or ", "(not ", "(= "] do
    require text fragment
  unless occurrences text "(define-sort @FF7" == 1 do
    throwError "repeated arithmetic redeclared its sort"
  for fragment in #["(declare-datatypes", "(to_int", "(mod "] do
    if contains text fragment then throwError "native arithmetic escaped to another theory"
  let booleanText := transcript (← direct (← body ``booleans))
  for fragment in #["(ite ", "(=> ", " Bool)", "(not (= "] do
    require booleanText fragment
  let text := transcript (← direct (← body ``twoFields))
  for p in (#[7, 11] : Array Nat) do
    unless occurrences text s!"(define-sort @FF{p} " == 1 &&
        occurrences text s!"(define-fun @FF{p}.add " == 1 do
      throwError "modulus {p} did not have exactly one separate sort and operation"
    require text s!"(_ FiniteField {p})"
  let aliases ← direct (← body ``aliasFields)
  unless occurrences (transcript aliases) "(define-sort @FF7 " == 1 &&
      occurrences (transcript aliases) "(define-fun @FF7.add " == 1 do
    throwError "reducible numeral alias duplicated its sort or operation"
  unless aliases.smtEnv.sourceAssociations.all (·.modulus == some 7) do
    throwError "reducible alias did not retain normalized modulus"
  let characteristic ← direct (← body ``characteristicTwo)
  require (transcript characteristic) "(_ FiniteField 2)"
  require (transcript characteristic) "#f0m2"
  if contains (transcript characteristic) "#f2m2" then
    throwError "characteristic-two coefficient was not reduced"

run_meta do
  let env ← direct (← body ``powers)
  let text := transcript env
  for n in (#[0, 3, 6, 7, 1048575] : Array Nat) do
    unless occurrences text s!"(define-fun @FF7.pow{n} " == 1 do
      throwError "power {n} was omitted or defined more than once"
  require text "(define-fun @FF7.pow0 ((@x @FF7)) @FF7 #f1m7)"
  require text "(@FF7.pow0 #f0m7)"
  require text "(@FF7.pow3 #f0m7)"
  let some definition := (env.smtEnv.smtCommands.map toString).find?
      (fun command => contains command "(define-fun @FF7.pow1048575 ")
    | throwError "missing large exponent definition"
  -- Twenty one-bits: twenty accumulations and nineteen shared squares.
  unless occurrences definition "(let " == 39 &&
      occurrences definition "(ff.mul " == 39 && definition.length < 5000 do
    throwError "large power is not logarithmic shared square-and-multiply: {definition}"
  require definition "@square0 @square0"
  unless occurrences text "(@FF7.pow1048575 " == 2 do
    throwError "two bases did not share the same exponent wrapper"

run_meta do
  let env ← direct (← body ``arithmetic)
  let variables := env.smtEnv.sourceAssociations.filter (·.source.isFVar)
  unless variables.size == 2 && env.smtEnv.topLevelVars.size == 2 do
    throwError "opened theorem parameters were not retained exactly once"
  for entry in env.smtEnv.sourceAssociations do
    unless entry.polarity == .negated && entry.modulus == some 7 do
      throwError "lost native source modulus or query polarity"
    withLCtx entry.localContext entry.localInstances do
      let .ok _ := Kernel.check (← getEnv) (← getLCtx) entry.source
        | throwError "retained source is not kernel-checkable in its saved scope"
      unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx)
          (← inferType entry.source) entry.type do
        throwError "retained metadata type does not describe its source"
      let mut evidenceFound := false
      for declaration in entry.localContext do
        if declaration.type == mkApp (mkConst ``PrimeModulus) (mkNatLit 7) then
          let .ok _ := Kernel.check (← getEnv) (← getLCtx) declaration.toExpr
            | throwError "opened prime evidence is not kernel-checkable"
          evidenceFound := true
      unless evidenceFound do throwError "metadata dropped the opened primality parameter"
  for name in #[`x, `y] do
    unless variables.any (·.userName == name) do throwError "lost source name {name}"
  let large ← direct (← body ``largeField)
  require (transcript large)
    s!"(_ FiniteField {Test.FiniteFieldLargePrime.curve25519})"
  unless large.smtEnv.sourceAssociations.all
      (·.modulus == some Test.FiniteFieldLargePrime.curve25519) do
    throwError "large modulus metadata was truncated"

private def missingEvidence : Prop := ∀ (x y : Residue 7), x = y
private def zeroModulus : Prop := ∀ (x y : Residue 0), x = y
private def oneModulus : Prop := ∀ (x y : Residue 1), x = y
private def compositeModulus : Prop := ∀ (x y : Residue 9), x = y
private def quantified : Prop := ∀ (_ : PrimeModulus 7),
  (∃ x : Residue 7, x = 0)
private def lambdaQuery : Prop := ∀ (_ : PrimeModulus 7),
  (fun x : Residue 7 => x + 1) = (fun x => x)
private def variablePower : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7) (n : Nat),
  x ^ n = x
private def representation : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7), x.rep.val = 0
private def naturalCast : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7) (n : Nat),
  x = (n : Residue 7)
private def mixedNatural : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7) (n : Nat),
  x = 0 ∧ n = 1
private def orderQuery : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7),
  x.rep.val < 3
private def representationCast : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7),
  x = Residue.mk (3 : Fin 7)

-- This is a real implementation, not an axiom or an admitted integer-power law.
-- Its only purpose is to construct the unsupported, well-typed source syntax.
private def integerPowerInstance : HPow (Residue 7) Int (Residue 7) :=
  ⟨fun x _ => x⟩

private def integerPower : Prop := ∀ (_ : PrimeModulus 7) (x : Residue 7),
  @HPow.hPow (Residue 7) Int (Residue 7) integerPowerInstance x (-1) = x

run_meta do
  rejectQuery ``missingEvidence "missing checked PrimeModulus"
  for name in #[``zeroModulus, ``oneModulus, ``compositeModulus] do
    rejectQuery name "native field admission"
  for name in #[``quantified, ``lambdaQuery] do
    rejectQuery name "residual quantified"
  for name in #[``variablePower, ``representation, ``naturalCast, ``mixedNatural,
      ``integerPower, ``orderQuery, ``representationCast] do
    rejectQuery name "unsupported"
  for name in #[``representation, ``orderQuery, ``representationCast, ``integerPower] do
    rejects "unsupported" (Translate.main (mkConst name) false)
  let query ← body ``arithmetic
  rejects "approved cvc5 preflight route" (translatePolynomial query)
  -- A preceding accepted query cannot lend its local prime evidence to this one.
  discard <| direct query
  rejectQuery ``missingEvidence "missing checked PrimeModulus"

run_meta do
  let ((result, _), env) ← (Translate.main (mkConst ``mainQuery) false).run options
  unless isUndeterminedResult result do throwError "dry native query claimed a verified outcome"
  let text := transcript env
  require text "(_ FiniteField 7)"
  require text "(define-fun @FF7.add"
  require text "(assert (not "
  unless env.smtEnv.sessions.isEmpty do throwError "Translate.main dry path started a solver"
  let ((_, _), booleanEnv) ← (Translate.main (mkConst ``booleans) false).run options
  require (transcript booleanEnv) "(ite "

-- Kernel semantics distinguish the nominal ring from raw Fin's truncating division.
example : (0 : Residue 7) ^ (0 : Nat) = 1 := by decide
example : (0 : Residue 7) ^ (7 : Nat) = 0 := by decide
example : (3 : Residue 7) ^ (6 : Nat) = 1 := by decide
example : (3 : Residue 7) ^ (7 : Nat) = 3 := by decide
example : (-9 : Residue 7) = 5 := by decide
example : (3 : Fin 7) / 2 = 1 := by decide
example : ¬ (∀ x : Residue 2, 2 * x = 0 → x = 0) := by
  intro h
  have impossible := h 1 (by decide)
  exact (by decide : (1 : Residue 2) ≠ 0) impossible

end Test.FiniteFieldTranslation
