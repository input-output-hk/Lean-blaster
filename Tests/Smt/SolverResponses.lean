import Blaster.Smt.Env

namespace Test.SolverResponses

open Blaster.Smt

/-! `get-value` removes only the echoed term and response wrapper. Preserve
    the returned SMT-LIB value, including solver-specific syntax and layout. -/

#guard unwrapGetValueOutput "((x 3))\n" == "3"
#guard unwrapGetValueOutput "((x (- 6)))\n" == "(- 6)"
#guard unwrapGetValueOutput "((s \"a\"\"b\"))\n" == "\"a\"\"b\""
#guard unwrapGetValueOutput "((s \"a\\u{5c}b\"))\n" == "\"a\\u{5c}b\""
#guard unwrapGetValueOutput "((s \"(x))((\"))\n" == "\"(x))((\""
#guard unwrapGetValueOutput "((|x (y)| |foo (bar)|))\n" == "|foo (bar)|"
#guard unwrapGetValueOutput "(((f 1) ((as Option.some (@Option Int)) (- 2))))\n"
  == "((as Option.some (@Option Int)) (- 2))"
#guard unwrapGetValueOutput "((o (as Option.none (@Option Int))))\n"
  == "(as Option.none (@Option Int))"
#guard unwrapGetValueOutput "((p (Point.mk\n  (- 3)\n  0)))\n"
  == "(Point.mk\n  (- 3)\n  0)"
#guard unwrapGetValueOutput
    "((l (let ((_let_1 (as List.cons (@List Int)))) (_let_1 1 (_let_1 2 (as List.nil (@List Int)))))))\n"
  == "(let ((_let_1 (as List.cons (@List Int)))) (_let_1 1 (_let_1 2 (as List.nil (@List Int)))))"
#guard unwrapGetValueOutput "((t (Prod.mk 1 (Prod.mk 2 true))))\n"
  == "(Prod.mk 1 (Prod.mk 2 true))"
#guard unwrapGetValueOutput "((f (lambda ((x Int)) (+ x 1))))\n"
  == "(lambda ((x Int)) (+ x 1))"

/-! Errors stay distinguishable from values without decoding their strings. -/

#guard solverErrorResponse? "(error \"cannot get value\")\n"
  == some "(error \"cannot get value\")"
#guard solverErrorResponse? "  ( error \"line 1 \"\"quoted\"\" msg\")\n"
  == some "( error \"line 1 \"\"quoted\"\" msg\")"
#guard solverErrorResponse? "((x 3))\n" == none
#guard solverErrorResponse? "(errorCode 1)\n" == none
#guard unwrapGetValueOutput "(error \"cannot get value\")\n"
  == "(error \"cannot get value\")"
#guard unwrapGetValueOutput "unsupported\n" == "unsupported"

/-! Correct SMT-LIB string emission is required by both backend adapters. -/

private def strLit? (s : String) : Option String :=
  match strLitSmt s with
  | .ok (.StrTerm t) => some t
  | _ => none

#guard strLit? "hello" == some "\"hello\""
#guard strLit? "a\"b" == some "\"a\"\"b\""
#guard strLit? "a\\b" == some "\"a\\u{5c}b\""
#guard strLit? "a\nb" == some "\"a\\u{a}b\""
#guard strLit? "(x))((" == some "\"(x))((\""
#guard strLit? (Char.ofNat 0x30000).toString == none

end Test.SolverResponses
