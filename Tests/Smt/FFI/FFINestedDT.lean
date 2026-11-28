import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt
/-!
# NESTED parametric-recursion datatype fields on the in-process Z3 FFI backend

Exercises the low-level FFI datatype builder for parametric datatypes whose fields
mention a type parameter UNDER another type constructor — the case that previously
threw "nested parametric field … unsupported". The datatypes here reproduce the
`Term`/`List` shape from Issue32:

```
(declare-datatype @List  (par (@α) ((List.nil) (List.cons (List.cons.0 @α) (List.cons.1 (@List @α))))))
(declare-datatype @Term  (par (@α) (
  (Term.leaf  (Term.leaf.0 @α))                       -- type parameter (type var)
  (Term.node  (Term.node.0 (@List (@Term @α))))       -- NESTED self-under-@List (forward ref)
  (Term.annot (Term.annot.0 (@Term @α))               -- REGULAR self-ref  (NULL + sort_ref)
              (Term.annot.1 (@List String))))))       -- NESTED-at-concrete (@List String)
```

`Term.annot` deliberately MIXES a NULL self-ref slot (field 0) and a real nested sort
(field 1) inside ONE constructor's `sorts[]` — the exact layout `Term.Annotated` has.

Because Z3 resets its error code at the head of every API call and the FFI context uses
a no-op error handler, a wrong nested/forward-ref sort corrupts the AST SILENTLY (no
throw). Every step therefore pins `errorCode == 0` right after the API call that could
have failed:

* `decl-ec` — after `Z3_mk_polymorphic_datatype` for `@Term` (its `Term.node` field is a
  forward reference `(@List (@Term @α))` to the datatype being declared).
* `node-ec` — after building `(Term.node xs)` with `xs : (@List (@Term Int))`: this is the
  discriminating check that Z3 SUBSTITUTED through the forward-ref field sort at
  instantiation (an un-substituted `@α` would sort-mismatch the ctor arg).
* `g1-ec` — after building `(= (Term.node.0 (Term.node xs)) xs)`: the accessor is
  monomorphized via `Z3_get_sort` and `mkEq` sort-checks its result against `xs`.

The two solver-reaching goals are VALID by the datatype theory:
* `g1`: `(Term.node.0 (Term.node xs)) = xs`      — accessor∘ctor round-trip on the nested field.
* `g2`: `annot t as = annot t bs → as = bs`      — ctor injectivity on the mixed-`sorts[]` ctor.
-/

namespace Test.FFINestedDT

/-! ## Shared datatype declarations (`@List`, then `@Term`) -/

private def listSym : SmtSymbol := mkNormalSymbol "@List"
private def termSym : SmtSymbol := mkNormalSymbol "@Term"
private def aSym    : SmtSymbol := mkNormalSymbol "@α"
private def aSort   : SortExpr := .SymbolSort aSym
private def listOf (s : SortExpr) : SortExpr := .ParamSort listSym #[s]
private def termOf (s : SortExpr) : SortExpr := .ParamSort termSym #[s]

private def listDecl : SmtDatatypeDecl := { params := some #[aSym], ctors := #[
  (mkNormalSymbol "List.nil", none),
  (mkNormalSymbol "List.cons", some #[
    (mkNormalSymbol "List.cons.0", aSort),
    (mkNormalSymbol "List.cons.1", listOf aSort)]) ] }

private def termDecl : SmtDatatypeDecl := { params := some #[aSym], ctors := #[
  (mkNormalSymbol "Term.leaf",  some #[(mkNormalSymbol "Term.leaf.0", aSort)]),
  (mkNormalSymbol "Term.node",  some #[(mkNormalSymbol "Term.node.0", listOf (termOf aSort))]),
  (mkNormalSymbol "Term.annot", some #[
    (mkNormalSymbol "Term.annot.0", termOf aSort),
    (mkNormalSymbol "Term.annot.1", listOf stringSort)]) ] }

/-- Declare `@List` BEFORE `@Term` (so `@List` is a resolved datatype when `@Term`'s
    nested field `(@List (@Term @α))` is built; the `@Term` occurrence inside it is a
    forward reference to the datatype currently being declared). -/
private def declDTs (s : Z3Session) : IO Unit := do
  s.runCommand (.declareDataType listSym listDecl)
  s.runCommand (.declareDataType termSym termDecl)

private def app (nm : SmtSymbol) (args : Array SmtTerm) : SmtTerm := .AppTerm (.SimpleIdent nm) args
private def notOp (t : SmtTerm) : SmtTerm := app (.ReservedSymbol "not") #[t]
private def eqOp (a b : SmtTerm) : SmtTerm := app (.ReservedSymbol "=") #[a, b]
private def impOp (a b : SmtTerm) : SmtTerm := app (.ReservedSymbol "=>") #[a, b]
private def showR : Result → String
  | .Valid => "valid" | .Falsified _ => "falsified" | .Undetermined => "undet"

/-! ## Round-trip: declaration → forward-ref instantiation → accessor → solve -/

/-- info: nested-dt decl-ec=0 node-ec=0 g1-ec=0 g1=valid g2=valid -/
#guard_msgs in
#eval do
  let termInt     := termOf intSort          -- (@Term Int)
  let listTermInt := listOf termInt          -- (@List (@Term Int))
  let listStr     := listOf stringSort       -- (@List String)
  -- Session A: declare, pin declaration-time errorCode, build the nested-field ctor,
  -- pin its errorCode, then discharge g1 (accessor∘ctor round-trip on the nested field).
  let sa ← Z3Session.create
  declDTs sa
  let decEc ← sa.ctx.errorCode               -- after Z3_mk_polymorphic_datatype for @Term
  sa.runCommand (.declareConst (mkNormalSymbol "xs") listTermInt)
  let xs : SmtTerm := .SmtIdent (.SimpleIdent (mkNormalSymbol "xs"))
  -- (Term.node xs) : (@Term Int) — ctor applied at the forward-ref-instantiated field sort.
  let nodeXs : SmtTerm := .AppTerm (.QualifiedIdent (mkNormalSymbol "Term.node") termInt) #[xs]
  let _ ← sa.run (buildTerm nodeXs)
  let nodeEc ← sa.ctx.errorCode              -- ctor arg sort-check (substitution through forward ref)
  -- g1: (Term.node.0 (Term.node xs)) = xs   (accessor monomorphized via Z3_get_sort)
  let g1 : SmtTerm := eqOp (app (mkNormalSymbol "Term.node.0") #[nodeXs]) xs
  let _ ← sa.run (buildTerm g1)
  let g1Ec ← sa.ctx.errorCode                -- mkEq sort-check: accessor result vs xs
  sa.assert (notOp g1)
  let r1 ← sa.checkSat #[] false
  -- Session B: g2 (ctor injectivity on the MIXED-sorts[] ctor Term.annot).
  let sb ← Z3Session.create
  declDTs sb
  sb.runCommand (.declareConst (mkNormalSymbol "t")  termInt)
  sb.runCommand (.declareConst (mkNormalSymbol "as") listStr)
  sb.runCommand (.declareConst (mkNormalSymbol "bs") listStr)
  let t  : SmtTerm := .SmtIdent (.SimpleIdent (mkNormalSymbol "t"))
  let as : SmtTerm := .SmtIdent (.SimpleIdent (mkNormalSymbol "as"))
  let bs : SmtTerm := .SmtIdent (.SimpleIdent (mkNormalSymbol "bs"))
  let annot := fun (l : SmtTerm) =>
    SmtTerm.AppTerm (.QualifiedIdent (mkNormalSymbol "Term.annot") termInt) #[t, l]
  -- g2: (annot t as = annot t bs) → as = bs
  let g2 : SmtTerm := impOp (eqOp (annot as) (annot bs)) (eqOp as bs)
  sb.assert (notOp g2)
  let r2 ← sb.checkSat #[] false
  IO.println s!"nested-dt decl-ec={decEc} node-ec={nodeEc} g1-ec={g1Ec} g1={showR r1} g2={showR r2}"

end Test.FFINestedDT
