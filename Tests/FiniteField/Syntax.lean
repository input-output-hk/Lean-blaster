import Tests.Pure

namespace Tests.FiniteField.Syntax

open Blaster.Smt Blaster.Optimize

/-- Exercise the production pipe emitter using a fixed byte relay, never a solver. -/
private def checkEmission (action : TranslateEnvT Unit) (expected : String) : Lean.MetaM Unit := do
  let child ← IO.Process.spawn {
    cmd := "/bin/cat", stdin := .piped, stdout := .piped, stderr := .piped
  }
  try
    let env : TranslateEnv := default
    let env := { env with smtEnv.emitProc := some child }
    discard <| action.run env
    child.stdin.putStr "\n;end-of-syntax\n"
    child.stdin.flush
    let mut actual := ""
    repeat
      let line ← child.stdout.getLine
      if line == ";end-of-syntax\n" then break
      if line.isEmpty then throwError "byte relay closed before syntax terminator"
      actual := actual ++ line
    unless actual == expected ++ "\n" do
      throwError "streaming syntax mismatch: expected {repr expected}, got {repr actual}"
  finally
    child.kill
    discard <| child.wait

private def checkSort (sort : SortExpr) (expected : String) : Lean.MetaM Unit := do
  unless toString sort == expected do
    throwError "sort syntax mismatch: expected {expected}, got {sort}"
  checkEmission sort.emit expected

private def checkCommand (command : SmtCommand) (expected : String) : Lean.MetaM Unit := do
  unless toString command == expected do
    throwError "command syntax mismatch: expected {expected}, got {command}"
  checkEmission command.emit (expected ++ "\n")

#eval checkSort (.ParamSort (.ReservedSymbol "Array") #[intSort, boolSort]) "(Array Int Bool)"
#eval checkCommand (.defineSort (.NormalSymbol "Scalar") none intSort) "(define-sort Scalar () Int)"

private def ff7 : SortExpr := .IndexedSort (.ReservedSymbol "FiniteField") #[7]
private def ff11 : SortExpr := .IndexedSort (.ReservedSymbol "FiniteField") #[11]
private def ff7Again : SortExpr := .IndexedSort (.ReservedSymbol ("Finite" ++ "Field")) (#[].push 7)
private def nested : SortExpr := .ParamSort (.ReservedSymbol "Array") #[ff7, ff11]

/-! Structural identity includes the constructor, symbol, index order and arity. -/
#guard ff7 == ff7Again
#guard hash ff7 == hash ff7Again
#guard ff7 != ff11
#guard ff7 != .SymbolSort (.ReservedSymbol "(_ FiniteField 7)")
#guard ff7 != .SymbolSort (.ReservedSymbol "FiniteField")
#guard ff7 != .ParamSort (.ReservedSymbol "FiniteField") #[]
#guard ff7 != .ParamSort (.ReservedSymbol "FiniteField") #[.SymbolSort (.ReservedSymbol "7")]
#guard ff7 != .IndexedSort (.NormalSymbol "FiniteField") #[7]
#guard ff7 != .IndexedSort (.ReservedSymbol "Other") #[7]
#guard ff7 != .IndexedSort (.ReservedSymbol "FiniteField") #[]
#guard ff7 != .IndexedSort (.ReservedSymbol "FiniteField") #[7, 11]
#guard (SortExpr.IndexedSort (.ReservedSymbol "Pair") #[7, 11]) !=
  .IndexedSort (.ReservedSymbol "Pair") #[11, 7]
#guard !isParamSort ff7 (.ReservedSymbol "FiniteField")
#guard isParamSort nested (.ReservedSymbol "Array")
#guard !isParamSort intSort (.ReservedSymbol "Int")

private def nestedAgain : SortExpr := .ParamSort (.ReservedSymbol "Array") #[ff7Again, ff11]
#guard nested == nestedAgain
#guard hash nested == hash nestedAgain
#guard nested != .ParamSort (.ReservedSymbol "Array") #[ff11, ff7]
#guard nested != .ParamSort (.ReservedSymbol "Array") #[ff7]

/-! Hash-table lookup must preserve distinct structural keys even if their text agrees. -/
#eval show Lean.MetaM Unit from do
  let textual := SortExpr.SymbolSort (.ReservedSymbol "(_ FiniteField 7)")
  let param := SortExpr.ParamSort (.ReservedSymbol "FiniteField") #[]
  let table : Std.HashMap SortExpr Nat :=
    ({} : Std.HashMap SortExpr Nat) |>.insert ff7 7 |>.insert ff11 11 |>.insert textual 70
       |>.insert param 1 |>.insert nested 77 |>.insert ff7Again 8
  unless table.size == 5 && table[ff7]? == some 8 && table[ff7Again]? == some 8 &&
      table[ff11]? == some 11 && table[textual]? == some 70 &&
      table[param]? == some 1 && table[nestedAgain]? == some 77 do
    throwError "structural sort hash-table keys collided or failed repeated lookup"

/-! Exact sort bytes, including existing constructors and quoted names. -/
#eval checkSort intSort "Int"
#eval checkSort (.SymbolSort (.NormalSymbol "User Sort")) "|User Sort|"
#eval checkSort ff7 "(_ FiniteField 7)"
#eval checkSort nested "(Array (_ FiniteField 7) (_ FiniteField 11))"
#eval checkSort (.ParamSort (.NormalSymbol "Box") #[nested])
  "(Box (Array (_ FiniteField 7) (_ FiniteField 11)))"
#eval checkSort (.IndexedSort (.NormalSymbol "Indexed Sort") #[7, 11]) "(_ |Indexed Sort| 7 11)"

/-! Both command printers use indexed sorts in declarations, aliases and sort arguments. -/
#eval checkCommand (.declareConst (.NormalSymbol "x") ff7)
  "(declare-const x (_ FiniteField 7))"
#eval checkCommand (.declareFun (.NormalSymbol "f") #[ff7, nested] ff11)
  "(declare-fun f ( (_ FiniteField 7) (Array (_ FiniteField 7) (_ FiniteField 11))) (_ FiniteField 11))"
#eval checkCommand (.defineSort (.NormalSymbol "F7") none ff7)
  "(define-sort F7 () (_ FiniteField 7))"
#eval checkCommand (.defineSort (.NormalSymbol "FieldArray") (some #[]) nested)
  "(define-sort FieldArray () (Array (_ FiniteField 7) (_ FiniteField 11)))"
#eval checkCommand (.defineSort (.NormalSymbol "WithField") (some #[.NormalSymbol "T"])
    (.ParamSort (.ReservedSymbol "Array") #[.SymbolSort (.NormalSymbol "T"), ff7]))
  "(define-sort WithField ( T) (Array T (_ FiniteField 7)))"
#eval checkEmission (SmtQualifiedIdent.QualifiedIdent (.NormalSymbol "x") ff7).emit
  "(as x (_ FiniteField 7))"
#guard toString (SmtQualifiedIdent.QualifiedIdent (.NormalSymbol "x") ff7) == "(as x (_ FiniteField 7))"

/-! Positivity is syntax-only: one and composites do not establish field admission. -/
#guard finiteFieldSort 0 == none
#guard finiteFieldSort 7 == some ff7
#guard finiteFieldSort 11 == some ff11
#guard finiteFieldSort 1 == some (.IndexedSort (.ReservedSymbol "FiniteField") #[1])
#guard finiteFieldSort 6 == some (.IndexedSort (.ReservedSymbol "FiniteField") #[6])
#guard (finiteFieldLit 3 0).isNone
#guard (finiteFieldLit (-3) 0).isNone
#guard (finiteFieldLit 0 0).isNone

private def checkLiteral (value : Int) (modulus : Nat) (expected : String) : Lean.MetaM Unit := do
  let some term := finiteFieldLit value modulus | throwError "positive modulus rejected"
  unless toString term == expected do
    throwError "literal mismatch: expected {expected}, got {term}"
  checkEmission term.emit expected
  checkCommand (.defineFun false (.NormalSymbol "literal") #[]
    (.IndexedSort (.ReservedSymbol "FiniteField") #[modulus]) term)
    s!"(define-fun literal () (_ FiniteField {modulus}) {expected})"

#eval checkLiteral (-1) 7 "#f6m7"
#eval checkLiteral (-15) 7 "#f6m7"
#eval checkLiteral (-14) 7 "#f0m7"
#eval checkLiteral 22 7 "#f1m7"
#eval checkLiteral 0 7 "#f0m7"
#eval checkLiteral 7 7 "#f0m7"
#eval checkLiteral (-3) 2 "#f1m2"
#eval checkLiteral (-2) 2 "#f0m2"
#eval checkLiteral 0 2 "#f0m2"
#eval checkLiteral 3 2 "#f1m2"
#eval checkLiteral 4 2 "#f0m2"
#eval checkLiteral (-99) 1 "#f0m1"
#eval checkLiteral (-1) 6 "#f5m6"
#eval checkLiteral (-1) 18446744073709551629 "#f18446744073709551628m18446744073709551629"
#eval checkLiteral 18446744073709551630 18446744073709551629 "#f1m18446744073709551629"

end Tests.FiniteField.Syntax
