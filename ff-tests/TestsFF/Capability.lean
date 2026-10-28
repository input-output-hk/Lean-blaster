import Blaster

namespace TestsFF.Capability

/-! Native IO capability checks for the separately staged solving profile.
The parent runner verifies the pinned executable before supplying BLASTER_FF_CVC5.
These are solver observations, not Lean proofs or a proof-export qualification.
The setup and cases mirror fixtures/finite-fields/protocol and its manifest. -/

private def setup : List String := [
  "(set-option :print-success true)",
  "(set-option :produce-models true)",
  -- Preserve the affirmed production setup; no case requests or trusts a proof.
  "(set-option :produce-proofs true)",
  "(set-option :mbqi true)",
  "(set-option :macros-quant true)",
  "(set-logic ALL)",
  "(get-option :ff-field-polys)",
  "(get-option :ff-solver)"
]

private inductive Expected where
  | unsat
  | linearModel

private structure Case where
  name : String
  commands : List String
  expected : Expected

private def cases : List Case := [
  { name := "f7-product-unsat"
    commands := [
      "(declare-fun x () (_ FiniteField 7))",
      "(declare-fun y () (_ FiniteField 7))",
      "(assert (= (ff.mul x y) #f0m7))",
      "(assert (not (= x #f0m7)))",
      "(assert (not (= y #f0m7)))"
    ]
    expected := .unsat },
  { name := "f3-square-unsat"
    commands := [
      "(declare-fun x () (_ FiniteField 3))",
      "(assert (= (ff.add (ff.mul x x) #f1m3) #f0m3))"
    ]
    expected := .unsat },
  { name := "f7-linear-model"
    commands := [
      "(declare-fun x () (_ FiniteField 7))",
      "(assert (= (ff.add x #f1m7) #f0m7))"
    ]
    expected := .linearModel },
  { name := "f7-linear-model-typed"
    commands := [
      "(declare-fun x () (_ FiniteField 7))",
      "(assert (= (ff.add x (as ff1 (_ FiniteField 7))) (as ff0 (_ FiniteField 7))))"
    ]
    expected := .linearModel }
]

-- Tokenize only the response grammar used below. Parentheses remain tokens, so
-- malformed nesting, extra responses, errors, and unknown cannot pass a match.
private def tokenize (text : String) : List String := Id.run do
  let mut tokens := []
  let mut word := ""
  for c in text.toList do
    if c.isWhitespace || c == '(' || c == ')' then
      if !word.isEmpty then
        tokens := word :: tokens
        word := ""
      if c == '(' || c == ')' then
        tokens := String.singleton c :: tokens
    else
      word := word.push c
  if !word.isEmpty then tokens := word :: tokens
  return tokens.reverse

-- Both SMT-LIB finite-field spellings carry a signed representative and modulus.
private def fieldValue : List String → Option (Int × Nat)
  | [literal] => do
    if !literal.startsWith "#f" then none else do
      let [value, modulus] := (literal.drop 2).splitOn "m" | none
      return (← value.toInt?, ← modulus.toNat?)
  | ["(", "as", literal, "(", "_", "FiniteField", modulus, ")", ")"] => do
    if !literal.startsWith "ff" then none else
      return (← (literal.drop 2).toInt?, ← modulus.toNat?)
  | _ => none

private def validLinearModel (tokens : List String) : Bool := Id.run do
  -- Exactly one get-value binding for x, with no trailing output.
  let "sat" :: "(" :: "(" :: "x" :: rest := tokens | return false
  let ")" :: ")" :: reversedValue := rest.reverse | return false
  let some (value, modulus) := fieldValue reversedValue.reverse | return false
  -- Check the asserted equation in F_7, not a solver-specific representative.
  return modulus == 7 && (value + 1) % 7 == 0

private def validate (test : Case) (output : IO.Process.Output) : IO Unit := do
  unless output.exitCode == 0 do
    throw <| IO.userError s!"{test.name}: solver exited {output.exitCode}\n{output.stdout}\n{output.stderr}"
  unless output.stderr.isEmpty do
    throw <| IO.userError s!"{test.name}: unexpected stderr\n{output.stderr}"
  let tokens := tokenize output.stdout
  let expectedSetup := List.replicate 6 "success" ++ ["false", "gb"] ++
    List.replicate test.commands.length "success"
  unless tokens.take expectedSetup.length == expectedSetup do
    throw <| IO.userError s!"{test.name}: setup/options/command response mismatch\n{output.stdout}"
  let response := tokens.drop expectedSetup.length
  let valid := match test.expected with
    | .unsat => response == ["unsat"]
    | .linearModel => validLinearModel response
  unless valid do
    throw <| IO.userError s!"{test.name}: SAT/UNSAT/model response mismatch\n{output.stdout}"

private def runCase (executable : String) (test : Case) : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    let query := match test.expected with
      | .unsat => ["(check-sat)"]
      | .linearModel => ["(check-sat)", "(get-value (x))"]
    handle.putStr <| String.intercalate "\n" (setup ++ test.commands ++ query) ++ "\n"
    handle.flush
    let output ← IO.Process.output {
      cmd := executable
      args := #[
        "--lang", "smt2", "--incremental", "--parsing-mode=lenient",
        "--dt-nested-rec", path.toString
      ]
    }
    validate test output

private def runCapabilities : IO Unit := do
  let some executable ← IO.getEnv "BLASTER_FF_CVC5"
    | throw <| IO.userError "BLASTER_FF_CVC5 must name the verified staged solver; run make test-cvc5-ff"
  unless executable.startsWith "/" do
    throw <| IO.userError "BLASTER_FF_CVC5 must be an absolute executable path; PATH fallback is forbidden"
  unless (← (System.FilePath.mk executable).pathExists) do
    throw <| IO.userError s!"BLASTER_FF_CVC5 does not exist: {executable}"
  let mut executed := 0
  for test in cases do
    runCase executable test
    executed := executed + 1
  unless executed > 0 do
    throw <| IO.userError "TestsFF.Capability executed zero live cases"
  IO.println s!"TestsFF.Capability: executed {executed} live finite-field cases"

#eval runCapabilities

end TestsFF.Capability
