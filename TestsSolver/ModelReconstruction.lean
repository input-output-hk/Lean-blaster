import Blaster

namespace Test.ModelReconstruction

open Blaster.Smt

/-! ## Test objectives to validate solver model-value reconstruction

    These tests exercise the pure `get-value` response pipeline
    (`Blaster.Smt.Model`): S-expression parsing, `let` expansion, `as`
    ascription stripping and Lean-flavored textual rendering. Fixtures
    explicitly labeled as captured are verbatim output from the named solver
    version. Other strings are representative or constructed regression inputs
    and make no claim of verbatim capture provenance.
-/

/-! # Primitive values (both solvers use the same format) -/

#guard reconstructGetValue? "((x 3))\n" == some "3"
#guard reconstructGetValue? "((x (- 6)))\n" == some "-6"
#guard reconstructGetValue? "((b true))\n" == some "true"
#guard reconstructGetValue? "((b false))\n" == some "false"

/-! # Strings: `""` undoubling, `\u{…}` decoding, Lean re-quoting -/

#guard reconstructGetValue? "((s \"hello\"))\n" == some "\"hello\""
#guard reconstructGetValue? "((s \"\"))\n" == some "\"\""
#guard reconstructGetValue? "((s \"a\"\"b\"))\n" == some "\"a\\\"b\""
#guard reconstructGetValue? "((s \"a\\u{5c}b\"))\n" == some "\"a\\\\b\""
#guard reconstructGetValue? "((s \"he\\u{1234}llo\"))\n" == some "\"heሴllo\""

/-! # Parentheses inside atoms

    The interactive response reader decides completeness by scanning parens
    across lines; these pin the parser-level assumption that parens inside
    string literals and quoted symbols never count as delimiters. -/

#guard reconstructGetValue? "((s \"a(b\"))\n" == some "\"a(b\""
#guard reconstructGetValue? "((s \"(x))((\"))\n" == some "\"(x))((\""
-- quoted symbols admit parentheses and spaces
#guard reconstructGetValue? "((x |foo (bar)|))\n" == some "foo (bar)"
-- same value through the unwrapped (single-expression) entry point
#guard reconstructValue? "|foo (bar)|" == some "foo (bar)"

/-! # SMT-LIB string literal emission (mirror of the decoding above) -/

#guard quoteSmtString "hello" == "\"hello\""
#guard quoteSmtString "a\"b" == "\"a\"\"b\""
#guard quoteSmtString "a\\b" == "\"a\\u{5c}b\""
#guard quoteSmtString "a\nb" == "\"a\\u{a}b\""
#guard quoteSmtString "(x))((" == "\"(x))((\"" -- parentheses travel unescaped
-- Round trip: decode ∘ quote = id
#guard Sexp.decodeStringLit? (quoteSmtString "a\"b\\c\nd") == some "a\"b\\c\nd"
#guard Sexp.decodeStringLit? (quoteSmtString "(x))((") == some "(x))(("

/-! # Datatype constructor applications -/

-- z3: plain application, single line
#guard reconstructGetValue? "((p (Point.mk (- 3) 0)))\n" == some "Point.mk (-3) 0"
-- z3: line-wrapped application (values past ~80 columns span several lines)
#guard reconstructGetValue?
    "(($0 (Test.Counter06.CounterState.mk\n  Test.Counter06.State.Delay\n  2\n  Test.Counter06.State.Busy\n  Test.Counter06.Request.Tr\n  3)))\n"
  == some "Test.Counter06.CounterState.mk Test.Counter06.State.Delay 2 Test.Counter06.State.Busy Test.Counter06.Request.Tr 3"
-- constructors with quoted symbols
#guard reconstructGetValue? "((p (|Foo 1.mk| (- 3))))\n" == some "Foo 1.mk (-3)"

/-! # Parametric datatypes: cvc5 `as` constructor qualifiers -/

-- cvc5: nullary constructor
#guard reconstructGetValue? "((o (as Option.none (@Option Int))))\n" == some "Option.none"
-- z3 prints the same value unqualified
#guard reconstructGetValue? "((o Option.none))\n" == some "Option.none"
-- cvc5: qualified constructor application
#guard reconstructGetValue? "((o ((as Option.some (@Option Int)) (- 2))))\n"
  == some "Option.some (-2)"
-- cvc5 1.2.1 (minimum supported version) omits the `@` prefix on the
-- instantiated sort (captured verbatim from a real 1.2.1 run)
#guard reconstructGetValue? "((o ((as Option.some (Option Int)) 7)))\n"
  == some "Option.some 7"
-- Ascriptions whose qualified term is itself an application still strip.
#guard reconstructValue? "(as (_ bv1 8) (_ BitVec 8))" == some "(_ bv1 8)"
#guard reconstructGetValue? "((t ((as Prod.mk (@Prod Int Bool)) (- 1) true)))\n"
  == some "(-1, true)"

/-! # Lists (rendered with Lean brackets) and cvc5 `let`-shared subterms -/

-- z3
#guard reconstructGetValue? "((l (List.cons (- 2) (List.cons 2 List.nil))))\n"
  == some "[-2, 2]"
#guard reconstructGetValue? "((l List.nil))\n" == some "[]"
-- cvc5 shares the qualified constructor through a `let`
#guard reconstructGetValue?
    "((l (let ((_let_1 (as List.cons (@List Int)))) (_let_1 (- 2) (_let_1 0 (as List.nil (@List Int)))))))\n"
  == some "[-2, 0]"
-- cvc5 1.2.1 prints the same `let`-shared value without the `@` sort prefix
-- (captured verbatim from a real 1.2.1 run)
#guard reconstructGetValue?
    "((l (let ((_let_1 (as List.cons (List Int)))) (_let_1 1 (_let_1 2 (as List.nil (List Int)))))))\n"
  == some "[1, 2]"
-- nested values: option inside a list
#guard reconstructGetValue? "((l (List.cons Option.none List.nil)))\n"
  == some "[Option.none]"

/-! # Tuples: right-nested `Prod.mk` flattens like Lean's tuple notation -/

#guard reconstructGetValue? "((t (Prod.mk 1 (Prod.mk 2 true))))\n" == some "(1, 2, true)"

/-! # Values with no Lean counterpart fall back to raw S-expressions -/

-- uninterpreted sort elements (abstracted `Type` parameters)
#guard reconstructGetValue? "((u U!val!0))\n" == some "U!val!0" -- z3
#guard reconstructGetValue? "((u (as @U_0 U)))\n" == some "@U_0" -- cvc5
-- z3 constant-array value (function-typed variables)
#guard reconstructGetValue? "((f ((as const (Array Int Int)) 0)))\n"
  == some "((as const (Array Int Int)) 0)"
-- constant array nested inside a constructor application: the application
-- still renders Lean-style while the array argument falls back to raw form
#guard reconstructGetValue? "((p (Pair.mk ((as const (Array Int Int)) 0) 1)))\n"
  == some "Pair.mk ((as const (Array Int Int)) 0) 1"
-- cvc5 lambda value
#guard reconstructGetValue? "((f (lambda ((_x Int)) (+ _x 1))))\n"
  == some "(lambda ((_x Int)) (+ _x 1))"

/-! # Binder-aware `let` normalization -/

-- A binder shadows an enclosing `let` substitution in both its declaration
-- and its body (the review's original capture regression).
#guard reconstructValue? "(let ((x 1)) (lambda ((x Int)) x))"
  == some "(lambda ((x Int)) x)"
-- Quoted binder names use the parser's preserved raw spelling consistently.
#guard reconstructValue? "(let ((|x y| 1)) (lambda ((|x y| Int)) |x y|))"
  == some "(lambda ((|x y| Int)) |x y|)"
-- Simple and quoted spellings denote the same SMT symbol during substitution.
#guard reconstructValue? "(let ((|x| 1)) x)" == some "1"
-- Quoted symbols never collide with unquoted lexical or command reserved words.
#guard reconstructValue? "(let ((|NUMERAL| 1)) (! |NUMERAL| :foo (NUMERAL)))"
  == some "(! 1 :foo (NUMERAL))"
#guard reconstructValue? "(let ((|assert| 1)) (! |assert| :foo (assert)))"
  == some "(! 1 :foo (assert))"
-- Binding declarations are opaque to term substitution, including their sort.
#guard reconstructValue? "(let ((S Int)) (lambda ((x S)) x))"
  == some "(lambda ((x S)) x)"
-- Nested `let` bindings are parallel: inner `y` sees the outer `x`, while the
-- inner `x` shadows it in the body.
#guard reconstructValue? "(let ((x 1)) (let ((x 2) (y x)) (+ x y)))"
  == some "(+ 2 1)"
-- The free occurrence is substituted while the lambda-bound occurrence of
-- the same spelling remains bound.
#guard reconstructValue? "(let ((x 1)) (Pair.mk x (lambda ((x Int)) x)))"
  == some "Pair.mk 1 (lambda ((x Int)) x)"
-- Quantifier declarations also shadow substitutions, while genuinely free
-- names in the quantified body are still normalized.
#guard reconstructValue? "(let ((x 1) (y 2)) (forall ((x Int)) (= x y)))"
  == some "(forall ((x Int)) (= x 2))"
-- Alpha-renaming prevents a free atom introduced by substitution from being
-- captured by an inner binder.
#guard reconstructValue? "(let ((y x)) (exists ((x Int)) (= x y)))"
  == some "(exists ((_blaster_bound_0 Int)) (= _blaster_bound_0 x))"
-- A quoted binder also captures the equivalent unquoted replacement atom, so
-- the binder and its quoted occurrences must be alpha-renamed.
#guard reconstructValue? "(let ((y x)) (forall ((|x| Int)) (= |x| y)))"
  == some "(forall ((_blaster_bound_0 Int)) (= _blaster_bound_0 x))"
-- Fresh names also avoid atoms nested inside the replacement term.
#guard reconstructValue?
    "(let ((y (Pair.mk x _blaster_bound_0))) (exists ((x Int)) (= x y)))"
  == some "(exists ((_blaster_bound_1 Int)) (= _blaster_bound_1 (Pair.mk x _blaster_bound_0)))"
-- Fresh names exclude equivalent quoted atoms already present in the body,
-- while preserving that atom's original spelling.
#guard reconstructValue?
    "(let ((y x)) (forall ((x Int)) (= |_blaster_bound_0| y)))"
  == some "(forall ((_blaster_bound_1 Int)) (= |_blaster_bound_0| x))"
-- Alpha-renaming is term-only and never rewrites a sort position.
#guard reconstructValue?
    "(let ((y S)) (lambda ((S Int)) (Pair.mk y ((as const (Array S Int)) 0))))"
  == some "(lambda ((_blaster_bound_0 Int)) (Pair.mk S ((as const (Array S Int)) 0)))"

/-! # Unsupported binder preservation -/

-- SMT-LIB match patterns bind variables in their branch terms. Until that
-- scope is implemented, preserve the complete enclosing value: substituting
-- the outer `x` into either the `(C x)` pattern or its branch changes meaning.
#guard reconstructValue? "(let ((x 1)) (match v (((C x) x))))"
  == some "(let ((x 1)) (match v (((C x) x))))"
-- Preservation must include the enclosing `let`, not just the match subtree;
-- otherwise genuinely free occurrences would be left dangling after expansion.
#guard reconstructValue? "(let ((x 1)) (Pair.mk x (match x (((C y) x)))))"
  == some "(let ((x 1)) (Pair.mk x (match x (((C y) x)))))"

/-! # Solver errors and malformed responses -/

#guard solverErrorMsg? "(error \"cannot get value\")\n" == some "cannot get value"
#guard reconstructGetValue? "(error \"cannot get value\")\n" == none
-- SMT-LIB `""` escapes in the message are undoubled …
#guard solverErrorMsg? "(error \"line 1 \"\"quoted\"\" msg\")\n" == some "line 1 \"quoted\" msg"
-- … and an `(error …)` response is never mistaken for a model
#guard reconstructGetValue? "(error \"line 1 \"\"quoted\"\" msg\")\n" == none
#guard reconstructGetValue? "((x (- 6))" == none -- truncated response
#guard reconstructGetValue? "unsupported\n" == none
#guard reconstructGetValue? "" == none
#guard solverErrorMsg? "((x 3))\n" == none

end Test.ModelReconstruction
