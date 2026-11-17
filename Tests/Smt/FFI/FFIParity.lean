import Blaster.Smt.FFI

open Blaster.Smt.FFI Blaster.Smt

private def op (name : String) (args : Array SmtTerm) : SmtTerm :=
  .AppTerm (.SimpleIdent (.ReservedSymbol name)) args

/-- Compare native constructor output with Z3's own SMT-LIB parser in the same
    context. A matching satisfiability verdict alone would miss changed terms. -/
private def checkAst (ctx : Context) (name : String) (term : SmtTerm)
    (script : String) : IO Unit := do
  let native ← BuildM.run ctx (buildTerm term)
  let parsed ← ctx.parseAssertForTest script
  unless ← ctx.astEqForTest native parsed do
    throw <| IO.userError s!"{name}: native {← ctx.astToString native} differs from SMT-LIB {← ctx.astToString parsed}"

/-- info: ground AST parity ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  checkAst ctx "integer arithmetic"
    (op "not" #[op "=" #[op "+" #[.NumTerm 1, .NumTerm 2], .NumTerm 4]])
    "(assert (not (= (+ 1 2) 4)))"
  checkAst ctx "integer division"
    (op "=" #[op "div" #[.NumTerm 17, .NumTerm 3], .NumTerm 5])
    "(assert (= (div 17 3) 5))"
  checkAst ctx "strings"
    (op "=" #[op "str.len" #[.StrTerm "\"abc\""], .NumTerm 3])
    "(assert (= (str.len \"abc\") 3))"
  checkAst ctx "bitvectors"
    (op "=" #[op "bvadd" #[.BinTerm "#b0011", .BinTerm "#b0101"], .BinTerm "#b1000"])
    "(assert (= (bvadd #b0011 #b0101) #b1000))"
  let arithmetic := #[
    ("negation", op "-" #[.NumTerm 3]),
    ("subtraction", op "-" #[.NumTerm 9, .NumTerm 2]),
    ("multiplication", op "*" #[.NumTerm 3, .NumTerm 4]),
    ("modulo", op "mod" #[.NumTerm 17, .NumTerm 3]),
    ("absolute value", op "abs" #[op "-" #[.NumTerm 3]]),
    ("power", op "^" #[.NumTerm 3, .NumTerm 2])]
  for (name, value) in arithmetic do
    let t := op "=" #[value, value]
    checkAst ctx name t s!"(assert {t})"
  let stringOps := #[
    ("string concatenation", op "str.++" #[.StrTerm "\"a\"", .StrTerm "\"b\""]),
    ("string replacement", op "str.replace" #[.StrTerm "\"aba\"", .StrTerm "\"a\"", .StrTerm "\"c\""]),
    ("string replacement all", op "str.replace_all" #[.StrTerm "\"aba\"", .StrTerm "\"a\"", .StrTerm "\"c\""])]
  for (name, value) in stringOps do
    let t := op "=" #[value, value]
    checkAst ctx name t s!"(assert {t})"
  let boolCases := #[
    ("conjunction", op "and" #[.BoolTerm true, .BoolTerm false]),
    ("disjunction", op "or" #[.BoolTerm true, .BoolTerm false]),
    ("negation", op "not" #[.BoolTerm true]),
    ("implication", op "=>" #[.BoolTerm true, .BoolTerm false]),
    ("less than", op "<" #[.NumTerm 1, .NumTerm 2]),
    ("less or equal", op "<=" #[.NumTerm 1, .NumTerm 2]),
    ("string less than", op "str.<" #[.StrTerm "\"a\"", .StrTerm "\"b\""]),
    ("string less or equal", op "str.<=" #[.StrTerm "\"a\"", .StrTerm "\"b\""])]
  for (name, t) in boolCases do
    checkAst ctx name t s!"(assert {t})"
  let ite := op "ite" #[.BoolTerm true, .NumTerm 1, .NumTerm 2]
  let iteEq := op "=" #[ite, ite]
  checkAst ctx "if then else" iteEq s!"(assert {iteEq})"
  let toInt := op "to_int" #[.DecTerm "3.5"]
  let toIntEq := op "=" #[toInt, toInt]
  checkAst ctx "real to integer" toIntEq s!"(assert {toIntEq})"
  let bvBinary := #["bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv", "bvurem",
    "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvor", "bvand",
    "bvnand", "bvnor", "bvxnor", "concat"]
  for name in bvBinary do
    let value := op name #[.BinTerm "#b1100", .BinTerm "#b0010"]
    let t := op "=" #[value, value]
    checkAst ctx name t s!"(assert {t})"
  for name in #["bvneg", "bvnot"] do
    let value := op name #[.BinTerm "#b1100"]
    let t := op "=" #[value, value]
    checkAst ctx name t s!"(assert {t})"
  for name in #["bvule", "bvult", "bvuge", "bvugt", "bvsle", "bvslt", "bvsge", "bvsgt"] do
    let t := op name #[.BinTerm "#b1100", .BinTerm "#b0010"]
    checkAst ctx name t s!"(assert {t})"
  IO.println "ground AST parity ok"

/-- info: quantifier AST parity ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  let q := mkForallTerm none #[(.NormalSymbol "x", intSort)]
    (op "=" #[op "+" #[x, .NumTerm 0], x])
    (some #[mkQid (.NormalSymbol "q1")])
  checkAst ctx "quantifier" q s!"(assert {q})"
  let nested := mkForallTerm none #[(.NormalSymbol "x", intSort)]
    (mkExistsTerm none #[(.NormalSymbol "x", intSort)]
      (op "=" #[x, .NumTerm 1]) (some #[mkQid (.NormalSymbol "q2")]))
    (some #[mkQid (.NormalSymbol "q3")])
  checkAst ctx "shadowed quantifiers" nested s!"(assert {nested})"
  IO.println "quantifier AST parity ok"

/-- info: pattern AST parity ok -/
#guard_msgs in
#eval do
  let ctx ← mkContext
  let f : SmtSymbol := .NormalSymbol "f"
  let x : SmtTerm := .SmtIdent (.SimpleIdent (.NormalSymbol "x"))
  let fx : SmtTerm := .AppTerm (.SimpleIdent f) #[x]
  let checkPattern (name : String) (q : SmtTerm) : IO Unit := do
    let native ← BuildM.run ctx do
      runCommand (.declareFun f #[intSort] intSort)
      buildTerm q
    let parsed ← ctx.parseAssertForTest s!"(declare-fun f (Int) Int)\n(assert {q})"
    unless ← ctx.astEqForTest native parsed do
      throw <| IO.userError s!"{name}: native {← ctx.astToString native} differs from SMT-LIB {← ctx.astToString parsed}"
  let good := mkForallTerm none #[(.NormalSymbol "x", intSort)]
    (op "=" #[fx, fx]) (some #[mkPattern #[fx], mkQid (.NormalSymbol "q4")])
  checkPattern "valid pattern" good
  let bad := mkForallTerm none #[(.NormalSymbol "x", intSort), (.NormalSymbol "y", intSort)]
    (op "=" #[x, .SmtIdent (.SimpleIdent (.NormalSymbol "y"))])
    (some #[mkPattern #[fx], mkQid (.NormalSymbol "q5")])
  checkPattern "discarded invalid pattern" bad
  IO.println "pattern AST parity ok"
