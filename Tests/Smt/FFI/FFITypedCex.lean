import Blaster
import Blaster.CEX.Decode

namespace Tests.Smt.FFI.FFITypedCex

open Lean Meta Elab Command Blaster.CEX

structure Point where
  x : Nat
  y : Bool

elab "#test_typed_cex" : command => do
  runTermElabM fun _ => do
    let pointType := mkConst ``Point
    let pointValue : Value := .app "Tests.Smt.FFI.FFITypedCex.Point.mk"
      #[.numeral "3", .bool true]
    let some point ← decode? pointType pointValue
      | throwError "failed to reconstruct Point"
    unless ← isDefEq (← inferType point) pointType do
      throwError "Point has the wrong Lean type"

    let listType := mkApp (mkConst ``List [0]) pointType
    let some _nil ← decode? listType (.app "List.nil" #[])
      | throwError "failed to reconstruct List.nil Point"
    let listValue : Value := .app "List.cons"
      #[pointValue, .app "List.nil" #[]]
    let some list ← decode? listType listValue
      | throwError "failed to reconstruct List Point"
    unless ← isDefEq (← inferType list) listType do
      throwError "List Point has the wrong Lean type"

    let bvType := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let some bv ← decode? bvType (.numeral "255")
      | throwError "failed to reconstruct BitVec"
    unless ← isDefEq (← inferType bv) bvType do
      throwError "BitVec has the wrong Lean type"

    if (← decode? (mkConst ``Nat) (.numeral "-1")).isSome then
      throwError "negative Nat was incorrectly accepted"
    if (← decode? pointType (.app "Point.mk" #[.numeral "3", .bool true])).isSome then
      throwError "wrong constructor name was incorrectly accepted"
    if (← decode? pointType (.app "Tests.Smt.FFI.FFITypedCex.Point.mk" #[.numeral "3"])).isSome then
      throwError "wrong field count was incorrectly accepted"
    if (← decode? pointType (.raw "unknown")).isSome then
      throwError "raw model text was incorrectly accepted as a Lean value"

#test_typed_cex

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - n: (1 : Nat)
-/
#guard_msgs (info) in
#blaster (backend: ffi) (solve-result: 1) [∀ (n : Nat), n = 0]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - xs: ([2] : List Int)
-/
#guard_msgs (info) in
#blaster (backend: ffi) (solve-result: 1) [∀ (xs : List Int), xs = []]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - n: (1 : Nat)
---
info: ✅ Replay: the instantiated Lean proposition evaluates to false
-/
#guard_msgs (info) in
#blaster (backend: ffi) (replay: 1) (solve-result: 1) [∀ (n : Nat), n = 0]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - xs: ([2] : List Int)
---
info: ✅ Replay: the instantiated Lean proposition evaluates to false
-/
#guard_msgs (info) in
#blaster (backend: ffi) (replay: 1) (solve-result: 1) [∀ (xs : List Int), xs = []]

/--
info: ✅ Expected Falsified
---
info: ⚠️ Replay unavailable: select (backend: ffi)
-/
#guard_msgs (info) in
#blaster (backend: smtlib) (replay: 1) (gen-cex: 0) (solve-result: 1)
  [∀ (n : Nat), n = 0]

/--
info: ✅ Expected Falsified
---
info: Counterexample:
---
info:  - p: ({ x := 1, y := false } : Point)
---
info: ✅ Replay: the instantiated Lean proposition evaluates to false
-/
#guard_msgs (info) in
#blaster (backend: ffi) (replay: 1) (solve-result: 1)
  [∀ (p : Point), p.x = 0]

#eval do
  let ctx ← Blaster.Smt.FFI.mkContext
  let ast ← ctx.mkStringLit "éλ🔍"
  let v ← ctx.readModelValue ast
  match v with
  | .str "éλ🔍" => pure ()
  | _ => throw (IO.userError s!"libz3 Unicode string AST was not preserved: {repr v}")

#eval do
  let s ← Blaster.Smt.FFI.Z3Session.create
  let lit := fun (x : String) => Blaster.Smt.SmtTerm.StrTerm s!"\"{x}\""
  let op := fun (name : String) (args : Array Blaster.Smt.SmtTerm) =>
    Blaster.Smt.SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol name)) args
  s.assert (op "=" #[op "str.replace_all" #[lit "aaa", lit "a", lit "b"], lit "bbb"])
  match ← s.checkSat #[] false with
  | .Falsified _ => pure ()
  | _ => throw (IO.userError "native str.replace_all did not evaluate to bbb")

#eval do
  let s ← Blaster.Smt.FFI.Z3Session.create
  s.runCommand (.declareConst (.NormalSymbol "hidden") Blaster.Smt.intSort)
  s.assert (.AppTerm (.SimpleIdent (.ReservedSymbol "=")) #[
    .SmtIdent (.SimpleIdent (.NormalSymbol "hidden")), .NumTerm 1])
  let model ← s.checkSat #[] true
  match model with
  | .Falsified ⟨_, [raw]⟩ =>
      unless raw.contains 'h' do
        throw (IO.userError "native model fallback omitted the declared symbol")
  | _ => throw (IO.userError "native model fallback returned no model")

#eval do
  let s ← Blaster.Smt.FFI.Z3Session.create
  let op := fun (name : String) (args : Array Blaster.Smt.SmtTerm) =>
    Blaster.Smt.SmtTerm.AppTerm (.SimpleIdent (.ReservedSymbol name)) args
  let a := Blaster.Smt.SmtTerm.HexTerm "#x0f"
  let b := Blaster.Smt.SmtTerm.BinTerm "#b00000001"
  s.assert (op "=" #[op "bvadd" #[a, b], .HexTerm "#x10"])
  s.assert (op "bvult" #[a, .HexTerm "#x10"])
  match ← s.checkSat #[] false with
  | .Falsified _ => pure ()
  | _ => throw (IO.userError "native BitVec literals/operators failed")

end Tests.Smt.FFI.FFITypedCex
