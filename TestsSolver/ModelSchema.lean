import Blaster

namespace Test.ModelSchema

open Blaster.Smt

/-! ## Test objectives to validate the sorts driving cvc5 model retrieval

    cvc5 counterexample values that can hold function values are retrieved
    type-directed, one selector term at a time (see `retrieveTypedValue`). The
    sorts come from a `ModelSchema` built from the canonical commands.

    These tests need no solver. They pin:
     - which sorts hold function values (`holdsFunctions`), through aliases,
       datatype fields, parametric datatypes and recursive datatypes;
     - the constructors of a datatype sort, with field sorts instantiated by
       the sort arguments (`constructors?`);
     - the constructors of function-holding datatypes that a function value
       can contain (`functionDatatypeConstructors`);
     - the symbols that mark a value as unevaluated (`symbols`, with
       `Sexp.freeSymbols`): declared constants and functions and defined
       functions, but not bound variables or selectors. -/

private def sym := mkNormalSymbol
private def funSort := arraySort #[intSort, intSort]
private def boxSort := SortExpr.SymbolSort (sym "@Box")
private def pointSort := SortExpr.SymbolSort (sym "@Point")
private def listSort := SortExpr.SymbolSort (sym "@FList")
private def optionOf (s : SortExpr) := SortExpr.ParamSort (sym "@Option") #[s]
private def alpha := sym "@α"

/-- `structure Box where fn : Int → Int; k : Int`, a first-order `Point`, a
    parametric `Option`, a recursive list of functions, a `Nat` alias and the
    declarations of a counterexample query. -/
private def commands : Array SmtCommand := #[
  .defineSort natSymbol none intSort,
  .declareDataType (sym "@Box") { params := none, ctors := #[
    (sym "Box.mk", some #[(sym "Box.mk.0", funSort), (sym "Box.mk.1", intSort)])] },
  .declareDataType (sym "@Point") { params := none, ctors := #[
    (sym "Point.mk", some #[(sym "Point.mk.0", intSort), (sym "Point.mk.1", natSort)])] },
  .declareDataType (sym "@Option") { params := some #[alpha], ctors := #[
    (sym "Option.none", none),
    (sym "Option.some", some #[(sym "Option.some.0", .SymbolSort alpha)])] },
  .declareDataType (sym "@FList") { params := none, ctors := #[
    (sym "FList.nil", none),
    (sym "FList.cons", some #[(sym "FList.cons.0", funSort), (sym "FList.cons.1", listSort)])] },
  .declareConst (sym "$0") boxSort,
  .declareFun (sym "@d") #[] intSort,
  .defineFun false (sym "@isBox") #[(sym "@x", boxSort)] boolSort (.BoolTerm true)
]

private def schema := ModelSchema.ofCommands commands

/-! # Sorts holding function values -/

#guard schema.holdsFunctions funSort
#guard schema.holdsFunctions boxSort
#guard schema.holdsFunctions (optionOf funSort)
#guard schema.holdsFunctions (optionOf boxSort)
#guard schema.holdsFunctions listSort
#guard schema.holdsFunctions (arraySort #[boxSort, intSort])
#guard !schema.holdsFunctions intSort
#guard !schema.holdsFunctions natSort
#guard !schema.holdsFunctions pointSort
#guard !schema.holdsFunctions (optionOf intSort)
#guard !schema.holdsFunctions (optionOf pointSort)

#guard schema.isFunctionSort funSort
#guard !schema.isFunctionSort boxSort
#guard schema.unfold natSort == intSort
#guard schema.consts.get? (sym "$0") == some boxSort

/-! # Constructors with instantiated field sorts -/

#guard (schema.constructors? (optionOf funSort)).map (·.map fun (c, fs) => (c.name, fs.map (·.2))) ==
  some #[("Option.none", #[]), ("Option.some", #[funSort])]
#guard (schema.constructors? boxSort).map (·.map fun (c, fs) => (c.name, fs.map (·.1.name))) ==
  some #[("Box.mk", #["Box.mk.0", "Box.mk.1"])]
#guard (schema.constructors? funSort).isNone
#guard (schema.constructors? intSort).isNone

/-! # Constructors a function value can contain -/

private def ctorNames (s : SortExpr) : List String :=
  (schema.functionDatatypeConstructors s).toList.mergeSort

#guard ctorNames funSort == []
#guard ctorNames (arraySort #[intSort, boxSort]) == ["Box.mk"]
#guard ctorNames (arraySort #[boxSort, intSort]) == ["Box.mk"]
#guard ctorNames (arraySort #[intSort, optionOf intSort]) == []
#guard ctorNames (arraySort #[intSort, pointSort]) == []
#guard ctorNames (arraySort #[intSort, optionOf funSort]) == ["Option.none", "Option.some"]
#guard ctorNames (arraySort #[intSort, listSort]) == ["FList.cons", "FList.nil"]

/-! # Unevaluated values -/

private def unevaluated (value : String) : List String :=
  match Sexp.parseMany value with
  | .ok #[e] => (Sexp.freeSymbols e).filter schema.symbols.contains |>.mergeSort
  | _ => ["<parse error>"]

-- cvc5's value of `$0 : Box`, which refers to `$0` itself.
#guard unevaluated "(Box.mk (Box.mk.0 $0) 1)" == ["$0"]
#guard unevaluated "(lambda ((x Int)) (ite (= x 1) (@d) 0))" == ["@d"]
#guard unevaluated "(lambda ((x @Box)) (@isBox x))" == ["@isBox"]
#guard unevaluated "(Box.mk (lambda ((x Int)) (ite (= x 1) 5 0)) (- 1))" == []
-- Bound variables named like declared constants are not free.
#guard unevaluated "(lambda (($0 Int)) (+ $0 1))" == []
-- Selectors applied to bound variables are evaluable.
#guard unevaluated "(lambda ((b @Box)) (Box.mk.1 b))" == []
#guard unevaluated "(let ((_let_1 3)) (Box.mk (lambda ((x Int)) _let_1) _let_1))" == []

end Test.ModelSchema
