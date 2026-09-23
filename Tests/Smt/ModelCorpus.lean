import Blaster

namespace Test.ModelCorpus
open Lean Elab Command Term Blaster.Options Blaster.Optimize Blaster.Smt

structure Point where
  x : Int
  y : Int

inductive QuotedKind where
  | «with value» (value : Int)

private def completeModel (accept : List String → Bool) : Result → Bool
  | .Falsified values => accept values
  | _ => false

#guard !completeModel (· == ["x: 3"]) (.Falsified [])
#guard !completeModel (· == ["x: 3"]) (.Falsified ["x: <counterexample unavailable>"])

private def recordCase (label : String) (result : Result) (accept : List String → Bool) : IO Bool := do
  let (verdict, actual) := match result with
    | .Falsified values => ("falsified", values)
    | .Valid => ("valid", [])
    | .Undetermined => ("unknown", [])
  let complete := completeModel accept result
  IO.println <| "MODEL_CASE:" ++ (Json.mkObj [
    ("case", toJson label), ("verdict", toJson verdict),
    ("complete", toJson complete), ("values", toJson actual)]).compress
  return complete

elab "#model_case " label:str goal:term " => " expected:str : command => do
  liftTermElabM do
    let goal ← instantiateMVars (← withSynthesize (postpone := .partial) <| elabTerm goal none)
    let base : TranslateEnv := default
    let env := { base with optEnv.options.solverOptions := {
      generateCex := true, solveResult := .ExpectedFalsified } }
    let ((result, _), _) ← Translate.main goal |>.run env
    unless ← recordCase label.getString result (· == [expected.getString]) do
      throwError "required model evidence is incomplete or incorrect: {label.getString}"

-- Forced witnesses reuse the previous pass's complete supported-value corpus.
#model_case "none" (∀ (o : Option Int), o ≠ none) => "o: Option.none"
#model_case "int" (∀ (x : Int), x ≠ 3) => "x: 3"
#model_case "structure" (∀ (p : Point), p ≠ Point.mk 1 (-2)) =>
  "p: Test.ModelCorpus.Point.mk 1 (-2)"
#model_case "some" (∀ (o : Option Int), o ≠ some 5) => "o: Option.some 5"
#model_case "tuple" (∀ (t : Int × Bool), t ≠ (5, true)) => "t: (5, true)"
#model_case "list" (∀ (l : List Int), l ≠ [1, 2]) => "l: [1, 2]"
#model_case "string" (∀ (s : String), s ≠ "a\"b") => "s: \"a\\\"b\""
#model_case "nat" (∀ (value : Nat), value ≠ 7) => "value: 7"
#model_case "quoted-constructor" (∀ (value : QuotedKind), value ≠ QuotedKind.«with value» 7) =>
  "value: Test.ModelCorpus.QuotedKind.«with value» 7"

#eval show MetaM Unit from do
  let expected := "a\"b\\c\nd\r"
  let base : TranslateEnv := default
  let env := { base with optEnv.options.solverOptions := {
    solver := some (← resolveSolver base.optEnv.options.solverOptions), generateCex := true } }
  let symbol := mkNormalSymbol "quoted (text"
  let (result, _) ← (do
    try
      setBlasterProcess
      declareConst symbol stringSort
      assertTerm (eqSmt (smtSimpleVarId symbol) (strLitSmt expected))
      modify fun (env : TranslateEnv) => { env with smtEnv.topLevelVars := #[[(symbol, `text)]] }
      checkSat
    finally discard exitSmt).run env
  unless ← recordCase "escaped-quoted-identifier" result (· == [s!"text: {expected.quote}"]) do
    throwError "required escaped model evidence is incomplete or incorrect"

-- The first/second counterexample predicates from SmtPredQualifier, without its
-- unrelated quantified laws. Decode proof fields and recheck the Lean predicate.
inductive NatGroup where
  | first (n : Nat) (h1 : n ≥ 10) (h2 : n < 100)
  | second (n : Nat) (h1 : n > 100) (h2 : n < 200)
  | next (n : NatGroup)

def isFirst : NatGroup → Bool | .first .. => true | _ => false
def isSecond : NatGroup → Bool | .second .. => true | _ => false
def toFirst : NatGroup → Nat | .first n .. => n | _ => 0
def toSecond : NatGroup → Nat | .second n .. => n | _ => 0

abbrev firstClaim (x : NatGroup) := isFirst x → let r := toFirst x; r > 20 ∧ r < 100
abbrev secondClaim (x : NatGroup) := isSecond x → let r := toSecond x; r > 200 ∧ r < 300
def firstGoal := ∀ x, firstClaim x
def secondGoal := ∀ x, secondClaim x

private def decodeNatGroup (text : String) : Option NatGroup := do
  let ["x:", ctor, number, "true", "true"] := text.splitOn " " | none
  let n ← number.toNat?
  if ctor == "Test.ModelCorpus.NatGroup.first" then
    if h : n ≥ 10 ∧ n < 100 then some (.first n h.1 h.2) else none
  else if ctor == "Test.ModelCorpus.NatGroup.second" then
    if h : n > 100 ∧ n < 200 then some (.second n h.1 h.2) else none
  else none

#guard (decodeNatGroup "x: Test.ModelCorpus.NatGroup.first 100 true true").isNone
#guard (decodeNatGroup "x: Test.ModelCorpus.NatGroup.second 300 true true").isNone

private def qualifierCase (label : String) (goal : Name) (falsifies : NatGroup → Bool) : MetaM Unit := do
  if (← IO.getEnv "BLASTER_CVC5_BUILD").map String.trim != some "patched" then return
  let base : TranslateEnv := default
  let env := { base with optEnv.options.solverOptions := {
    generateCex := true, solveResult := .ExpectedFalsified } }
  let ((result, _), _) ← Translate.main (mkConst goal) |>.run env
  let accept : List String → Bool := fun values => match values with
    | [value] => (decodeNatGroup value).any falsifies
    | _ => false
  unless ← recordCase label result accept do
    throwError "required qualifier model evidence is incomplete or incorrect: {label}"

#eval qualifierCase "natgroup-first" ``firstGoal (fun x => !decide (firstClaim x))
#eval qualifierCase "natgroup-second" ``secondGoal (fun x => !decide (secondClaim x))

end Test.ModelCorpus
