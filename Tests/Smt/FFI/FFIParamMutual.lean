import Blaster.Smt.FFI
open Blaster.Smt.FFI Blaster.Smt
/-!
# PARAMETRIC-MUTUAL datatype groups on the in-process Z3 FFI backend

The Z3 C API has no parametric-mutual datatype constructor (only single via
`Z3_mk_polymorphic_datatype` and non-parametric-mutual via `Z3_mk_datatypes`), so a
parametric-mutual `declare-datatypes` is routed through Z3's OWN SMT-LIB parser
(`Context.evalSmtlib2`) on the session context; the datatypes then resolve by NAME via
`Z3_mk_datatype_sort` and the `dt*` func_decl queries. This mirrors Issue16's
`Attribute`/`Term` shape, reduced to the probe's mutually-recursive pair:

```
(declare-datatypes ((@A 1)(@B 1))
  ((par (@T) ((A.leaf (A.leaf.0 @T)) (A.node (A.node.0 (@B @T)))))     -- A holds a B
   (par (@T) ((B.leaf (B.leaf.0 @T)) (B.node (B.node.0 (@A @T))))))))  -- B holds an A
```

Because the FFI context uses a no-op error handler, a parse failure corrupts sorts
SILENTLY (no throw). Each stage therefore pins `errorCode == 0` right after the API call
that could have failed: after the `declare-datatypes` eval (`decl-ec`), after building the
cross-referencing constructor `(A.node y)` with `y : (@B Int)` (`ctor-ec` — this discriminates
that Z3 substituted `@T := Int` through the `(@B @T)` field), and after building the accessor
term (`acc-ec`).

The solver-reaching goals are decided by the datatype theory:
* `g1`   : `(A.leaf.0 (A.leaf x)) = x`          — accessor∘ctor round-trip (VALID).
* `recog`: `is-A.leaf (A.leaf x)`               — recognizer on the matching ctor (VALID).
* `cross`: `(A.node.0 (A.node y)) = y`          — accessor round-trip on the CROSS-REF field
                                                  `(@B Int)` held inside `(@A Int)` (VALID).
* `inv`  : `(A.leaf.0 (A.leaf x)) = z`          — reduces to `x = z`, NOT a theorem
                                                  (FALSIFIED) — guards against a vacuous model.
-/

namespace Test.FFIParamMutual

private def tSym : SmtSymbol := mkNormalSymbol "@T"
private def tSort : SortExpr := .SymbolSort tSym
private def aSym : SmtSymbol := mkNormalSymbol "@A"
private def bSym : SmtSymbol := mkNormalSymbol "@B"
private def aOf (s : SortExpr) : SortExpr := .ParamSort aSym #[s]
private def bOf (s : SortExpr) : SortExpr := .ParamSort bSym #[s]

private def aDecl : SmtDatatypeDecl := { params := some #[tSym], ctors := #[
  (mkNormalSymbol "A.leaf", some #[(mkNormalSymbol "A.leaf.0", tSort)]),
  (mkNormalSymbol "A.node", some #[(mkNormalSymbol "A.node.0", bOf tSort)]) ] }

private def bDecl : SmtDatatypeDecl := { params := some #[tSym], ctors := #[
  (mkNormalSymbol "B.leaf", some #[(mkNormalSymbol "B.leaf.0", tSort)]),
  (mkNormalSymbol "B.node", some #[(mkNormalSymbol "B.node.0", aOf tSort)]) ] }

private def sortDecls : Array SmtSortDecl :=
  #[{ name := aSym, arity := 1 }, { name := bSym, arity := 1 }]

private def app (nm : SmtSymbol) (args : Array SmtTerm) : SmtTerm := .AppTerm (.SimpleIdent nm) args
private def notOp (t : SmtTerm) : SmtTerm := app (.ReservedSymbol "not") #[t]
private def eqOp (a b : SmtTerm) : SmtTerm := app (.ReservedSymbol "=") #[a, b]
private def var (s : String) : SmtTerm := .SmtIdent (.SimpleIdent (mkNormalSymbol s))
private def showR : Result → String
  | .Valid => "valid" | .Falsified _ => "falsified" | .Undetermined => "undet"

/-- info: param-mutual decl-ec=0 ctor-ec=0 acc-ec=0 g1=valid recog=valid cross=valid inv=falsified -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.declareMutualDataTypes sortDecls #[aDecl, bDecl])
  let decEc ← s.ctx.errorCode                       -- after the parametric-mutual parser eval
  s.runCommand (.declareConst (mkNormalSymbol "x") intSort)
  s.runCommand (.declareConst (mkNormalSymbol "z") intSort)
  s.runCommand (.declareConst (mkNormalSymbol "y") (bOf intSort))
  let x := var "x"; let z := var "z"; let y := var "y"
  -- (A.leaf x) : (@A Int); (A.node y) : (@A Int) with y : (@B Int) (cross-ref field)
  let leafAx : SmtTerm := .AppTerm (.QualifiedIdent (mkNormalSymbol "A.leaf") (aOf intSort)) #[x]
  let nodeAy : SmtTerm := .AppTerm (.QualifiedIdent (mkNormalSymbol "A.node") (aOf intSort)) #[y]
  let _ ← s.run (buildTerm nodeAy)
  let ctorEc ← s.ctx.errorCode                      -- ctor arg sort-check through the (@B @T) field
  let g1    : SmtTerm := eqOp (app (mkNormalSymbol "A.leaf.0") #[leafAx]) x
  let _ ← s.run (buildTerm g1)
  let accEc ← s.ctx.errorCode                       -- accessor monomorphized via Z3_get_sort
  let recog : SmtTerm := app (mkNormalSymbol "is-A.leaf") #[leafAx]
  let cross : SmtTerm := eqOp (app (mkNormalSymbol "A.node.0") #[nodeAy]) y
  let inv   : SmtTerm := eqOp (app (mkNormalSymbol "A.leaf.0") #[leafAx]) z
  let r1 ← s.checkAssuming #[notOp g1]    #[] false
  let r2 ← s.checkAssuming #[notOp recog] #[] false
  let r3 ← s.checkAssuming #[notOp cross] #[] false
  let r4 ← s.checkAssuming #[notOp inv]   #[] false
  IO.println s!"param-mutual decl-ec={decEc} ctor-ec={ctorEc} acc-ec={accEc} \
g1={showR r1} recog={showR r2} cross={showR r3} inv={showR r4}"

/-! ## Single parametric datatype, THEN a parametric-mutual group that references it

The Issue16 shape: a single parametric datatype (`@List`) is declared first, then a
parametric-MUTUAL group (`@C`/`@D`) whose fields reference it (`C.node.0 : (@List (@D @T))`).
This works ONLY because single parametric datatypes are now ALSO routed through the parser
(`declareParamDatatype` → `evalDeclChecked`): successive evals accumulate, so the later
mutual group's parser eval sees the earlier `@List`. If `@List` were declared via the C API
(the old path), the mutual eval would fail with `unknown sort '@List'` — the regression this
block guards against. -/

private def listSym : SmtSymbol := mkNormalSymbol "@List"
private def cSym : SmtSymbol := mkNormalSymbol "@C"
private def dSym : SmtSymbol := mkNormalSymbol "@D"
private def listOf (s : SortExpr) : SortExpr := .ParamSort listSym #[s]
private def cOf (s : SortExpr) : SortExpr := .ParamSort cSym #[s]
private def dOf (s : SortExpr) : SortExpr := .ParamSort dSym #[s]

private def listDecl : SmtDatatypeDecl := { params := some #[tSym], ctors := #[
  (mkNormalSymbol "List.nil", none),
  (mkNormalSymbol "List.cons", some #[
    (mkNormalSymbol "List.cons.0", tSort),
    (mkNormalSymbol "List.cons.1", listOf tSort)]) ] }

private def cDecl : SmtDatatypeDecl := { params := some #[tSym], ctors := #[
  (mkNormalSymbol "C.leaf", some #[(mkNormalSymbol "C.leaf.0", tSort)]),
  (mkNormalSymbol "C.node", some #[(mkNormalSymbol "C.node.0", listOf (dOf tSort))]) ] }

private def dDecl : SmtDatatypeDecl := { params := some #[tSym], ctors := #[
  (mkNormalSymbol "D.leaf", some #[(mkNormalSymbol "D.leaf.0", tSort)]),
  (mkNormalSymbol "D.wrap", some #[(mkNormalSymbol "D.wrap.0", cOf tSort)]) ] }

private def cdSortDecls : Array SmtSortDecl :=
  #[{ name := cSym, arity := 1 }, { name := dSym, arity := 1 }]

/-- info: single+mutual list-ec=0 mut-ec=0 ctor-ec=0 acc-ec=0 g=valid -/
#guard_msgs in
#eval do
  let s ← Z3Session.create
  s.runCommand (.declareDataType listSym listDecl)          -- single parametric, via parser
  let listEc ← s.ctx.errorCode
  s.runCommand (.declareMutualDataTypes cdSortDecls #[cDecl, dDecl])  -- mutual refs @List
  let mutEc ← s.ctx.errorCode
  s.runCommand (.declareConst (mkNormalSymbol "n") intSort)
  let n := var "n"
  let cLeaf : SmtTerm := .AppTerm (.QualifiedIdent (mkNormalSymbol "C.leaf") (cOf intSort)) #[n]
  let dWrap : SmtTerm := .AppTerm (.QualifiedIdent (mkNormalSymbol "D.wrap") (dOf intSort)) #[cLeaf]
  let _ ← s.run (buildTerm dWrap)
  let ctorEc ← s.ctx.errorCode
  let g : SmtTerm := eqOp (app (mkNormalSymbol "D.wrap.0") #[dWrap]) cLeaf
  let _ ← s.run (buildTerm g)
  let accEc ← s.ctx.errorCode
  let r ← s.checkAssuming #[notOp g] #[] false
  IO.println s!"single+mutual list-ec={listEc} mut-ec={mutEc} ctor-ec={ctorEc} acc-ec={accEc} g={showR r}"

end Test.FFIParamMutual
