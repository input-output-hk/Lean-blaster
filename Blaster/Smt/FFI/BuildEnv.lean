import Blaster.Smt.FFI.Types
import Blaster.Smt.FFI.Solver
import Blaster.Smt.Syntax

namespace Blaster.Smt.FFI
open Blaster.Smt

/-- A defined-function macro: parameters + the raw SmtTerm body, to inline at apply sites. -/
structure MacroDef where
  params : Array SmtSymbol
  body   : SmtTerm

/-- Template for a PARAMETRIC datatype. Both single and mutual parametric datatypes are
    declared NATIVELY via `Z3_mk_polymorphic_datatype` (`Context.mkPolyDatatype`) — one call
    per datatype, with `Z3_mk_datatype_sort(sibling, [args])` forward-refs for cross-references
    in a mutual group. No SMT-LIB parser is involved, so all datatypes and the C-API-declared
    uninterpreted sorts (`@@ArrowT2`) share ONE Z3 manager name space. Concrete instantiations
    are obtained on demand via `Context.mkDatatypeSort name argSorts` (resolving by NAME).
    `ctorNames` is ordered by Z3 ctor index; `accessorNames[i]` is the ordered accessor names of
    ctor `i`. `polySort` is always `none` (the `Z3_mk_polymorphic_datatype` result is not kept);
    the field is dead — never read. -/
structure ParamDatatype where
  name          : SmtSymbol
  polySort      : Option Z3Sort
  nparams       : Nat
  /-- Whether the datatype is (self- or mutually-) recursive. Used to classify a datatype used
      as a field WRAPPER: a NON-recursive datatype with ≥2 constructors is an "unsafe wrapper" —
      instantiating it at a bare forward-ref sibling segfaults Z3, so a mutual member that wraps
      a sibling directly in one must be declared AFTER that sibling (see the mutual reorder). -/
  recursive     : Bool
  ctorNames     : Array SmtSymbol
  accessorNames : Array (Array SmtSymbol)

/-- Mutable build environment mapping SMT names to Z3 handles. -/
structure BuildState where
  mkRaw ::
  ctx      : Context
  sorts    : Std.HashMap SmtSymbol Z3Sort
  consts   : Std.HashMap SmtSymbol Ast
  funcs    : Std.HashMap SmtSymbol FuncDecl
  macros   : Std.HashMap SmtSymbol MacroDef
  recFuncs : Std.HashMap SmtSymbol FuncDecl
  /-- scoped local bindings (let + quantifier vars), innermost last -/
  locals   : Array (SmtSymbol × Ast)
  /-- parametric-datatype templates, keyed by datatype name (e.g. `@List`). -/
  paramDatatypes  : Std.HashMap SmtSymbol ParamDatatype
  /-- ctor name → (datatypeName, Z3 ctor index). -/
  ctorIndex       : Std.HashMap SmtSymbol (SmtSymbol × Nat)
  /-- accessor (selector) name → (datatypeName, ctor index, field index). -/
  accessorIndex   : Std.HashMap SmtSymbol (SmtSymbol × Nat × Nat)
  /-- recognizer name (`is-<ctor>`) → (datatypeName, ctor index). -/
  recognizerIndex : Std.HashMap SmtSymbol (SmtSymbol × Nat)
  /-- cache of instantiated datatype sorts, keyed by the `.ParamSort` SortExpr. -/
  instSortCache   : Std.HashMap SortExpr Z3Sort

def BuildState.mk (ctx : Context) : IO BuildState := return {
  ctx, sorts := {}, consts := {}, funcs := {}, macros := {}, recFuncs := {}, locals := #[],
  paramDatatypes := {}, ctorIndex := {}, accessorIndex := {}, recognizerIndex := {},
  instSortCache := {} }

abbrev BuildM := StateRefT BuildState IO

def BuildM.run (ctx : Context) (m : BuildM α) : IO α := do
  let st ← BuildState.mk ctx
  StateRefT'.run' m st

/-- Look up a local binding by symbol (searches innermost-first). -/
def lookupLocal (s : SmtSymbol) : BuildM (Option Ast) := do
  let locals := (← get).locals
  return locals.findSomeRev? (fun (k, v) => if k == s then some v else none)

end Blaster.Smt.FFI
