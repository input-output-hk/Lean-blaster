import Blaster.Smt

open Lean Meta Elab Command
open Blaster.Counterexample

namespace Tests.Counterexample

structure Payload where
  amount : Int
  enabled : Bool
  tags : List String
  deriving Repr

-- This custom exporter must be selected over the structural fallback.
instance : ToCEX Payload := ⟨fun p => .constructor "Payload" "source-payload"
  [("amount", toCEX p.amount), ("enabled", toCEX p.enabled), ("tags", toCEX p.tags)]⟩

inductive Odd where
  | «has.dot» (value : Int)

inductive Tree where
  | leaf (value : Int)
  | node (left right : Tree)

run_cmd liftTermElabM do
  let ty := mkConst ``Payload
  let raw := "(Tests.Counterexample.Payload.mk (- 123456789012345678901234567890) true (List.cons \"a(\\u{e9})\" (as List.nil (@List String))))"
  let b ← decode `payload₀ `payload ty raw
  unless b.error.isNone do throwError "record reconstruction failed: {b.error}"
  let json ← b.toJson
  let value ← ofExcept (json.getObjVal? "value")
  unless (value.getObjValAs? String "constructor").toOption == some "source-payload" do
    throwError "custom ToCEX instance was not used: {json}"
  let xs ← ofExcept (value.getObjValAs? (Array Json) "fields")
  unless ((← ofExcept (xs[0]!.getObjVal? "value")).getObjValAs? String "value").toOption ==
      some "-123456789012345678901234567890" do throwError "integer precision lost"
  let tags ← ofExcept (xs[2]!.getObjVal? "value")
  unless (tags.getObjValAs? String "kind").toOption == some "list" do throwError "nested ToCEX instance ignored"
  let values ← ofExcept (tags.getObjValAs? (Array Json) "values")
  unless (values[0]!.getObjValAs? String "value").toOption == some "a(é)" do throwError "SMT Unicode/string decoding failed"
  let tree ← decode `tree₀ `tree (mkConst ``Tree)
    "(Tests.Counterexample.Tree.node (Tests.Counterexample.Tree.leaf 1) (Tests.Counterexample.Tree.leaf (- 2)))"
  unless tree.value.isSome do throwError "recursive value reconstruction failed: {tree.error}"
  let odd ← decode `odd₀ `odd (mkConst ``Odd)
    s!"(|{``Odd.«has.dot»}| 7)"
  unless odd.value.isSome do throwError "quoted constructor name failed to reconstruct"
  let sameName ← decode `payload₁ `payload ty raw
  unless sameName.id != b.id && sameName.name == b.name do throwError "shadowed assignments lost identity"
  let letValue ← ofExcept (parse "(let ((a 1)) (let ((a 2) (b a)) b))")
  let (n, _) ← reconstruct (mkConst ``Int) letValue
  unless ← isDefEq n (toExpr (1 : Int)) do throwError "SMT simultaneous let binding semantics changed"
  for (type, raw) in [
      (mkConst ``Int, "false"),
      (mkConst ``Nat, "(- 1)"),
      (mkConst ``Payload, "(Tests.Counterexample.Tree.leaf 0)"),
      (mkConst ``Payload, "(Tests.Counterexample.Payload.mk 1 true)"),
      (mkApp (mkConst ``Fin) (toExpr (3 : Nat)), "(Fin.mk 1 true)"),
      (mkConst ``String, "\"\\u{d800}\""),
      (mkConst ``String, "\"unclosed"),
      (mkConst ``Int, "1 2")] do
    let b ← decode `bad `bad type raw
    unless b.value.isNone && b.error.isSome do throwError "unsupported/invalid model was fabricated: {raw}"
  logInfo "PASS typed records, recursive values, Unicode, large integers, ToCEX overrides, identity and decoding failures"

-- This asks the actual solver for a model, without fixing its choice of witness.
run_cmd liftTermElabM do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term "∀ (x y : Int), x < y → y < x")
  let expr ← Term.elabTermAndSynthesize stx (some (mkSort .zero))
  let env := {(default : Blaster.Optimize.TranslateEnv) with
    optEnv.options.solverOptions.solveResult := .ExpectedFalsified}
  let ((result, _), _) ← Blaster.Smt.Translate.main expr |>.run env
  let .Falsified model := result | throwError "expected a real solver counterexample"
  unless model.bindings.size == 2 do throwError "missing typed assignments"
  let mut vals : Array Int := #[]
  for binding in model.bindings do
    unless binding.error.isNone do throwError "failed decoding: {binding.error}"
    let some value := binding.value | throwError "missing model value"
    vals := vals.push (← evalExpr Int (mkConst ``Int) value)
  unless vals[0]! < vals[1]! do throwError "model does not falsify original proposition"
  logInfo "PASS solver assignments reconstruct and falsify the original proposition"

end Tests.Counterexample

#guard Blaster.Counterexample.responseComplete "(ctor \"(\" |symbol)|)\n"
#guard !(Blaster.Counterexample.responseComplete "(ctor \"(\"\n")

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term
    "∀ (p : Tests.Counterexample.Payload), p.tags = [\"(\"] → p.amount < 0")
  let expr ← Term.elabTermAndSynthesize stx (some (mkSort .zero))
  let env := {(default : Blaster.Optimize.TranslateEnv) with
    optEnv.options.solverOptions.solveResult := .ExpectedFalsified}
  let ((result, _), _) ← Blaster.Smt.Translate.main expr |>.run env
  let .Falsified model := result | throwError "expected a structured solver counterexample"
  unless model.bindings.size == 1 do throwError "missing record assignment"
  let some b := model.bindings[0]? | throwError "missing binding"
  unless b.error.isNone && b.value.isSome do throwError "record model decode failed"
  logInfo "PASS actual solver record model with parentheses inside a string"
