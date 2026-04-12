/-
  Blaster.Wasm.ExportSmt — Elaboration command for exporting SMT-LIB 2

  Provides `#export_smt` which runs Blaster at elaboration time on a theorem
  and creates an `@[export]` definition containing the SMT-LIB 2 string.

  Usage:
    #export_smt myTheorem as mySmtDef export_as "wasm_my_smt"

  This creates:
    @[export wasm_my_smt]
    def mySmtDef : String := "(declare-datatype ...)\n..."
-/
import Lean
import Blaster.Wasm.SmtCapture

open Lean Elab Command Term Meta

namespace Blaster.Wasm

/-- `#export_smt <theorem> as <def_name> export_as "<c_name>"`

    Runs Blaster's SMT translation on `<theorem>` at elaboration time
    and creates a new definition `<def_name> : String` containing the
    complete SMT-LIB 2 query. The definition is marked with
    `@[export <c_name>]` so it can be called from C/WASM.

    Example:
    ```
    #export_smt myProp as mySmtQuery export_as "wasm_get_my_smt"
    ```
    Creates a C-callable function `wasm_get_my_smt` returning the SMT string.
-/
elab "#export_smt " thm:ident " as " defName:ident " export_as " exportName:str : command => do
  let thmName := thm.getId
  -- Resolve the fully qualified name
  let resolvedName ← liftTermElabM do
    let ns ← getCurrNamespace
    let candidates := #[thmName, ns ++ thmName]
    let env ← getEnv
    for c in candidates do
      if env.find? c |>.isSome then return c
    -- Try to resolve via the current scope
    resolveGlobalConstNoOverload thm
  -- Look up the theorem type
  let some info := (← getEnv).find? resolvedName
    | throwError "#export_smt: theorem '{resolvedName}' not found in environment"
  -- Run Blaster at elaboration time (TermElabM extends MetaM)
  let smtStr ← liftTermElabM $ captureSmtLib2 info.type
  -- Create the @[export] definition as a function taking Unit
  -- This ensures the C signature is: lean_object* name(lean_object* unit)
  let exportIdent := mkIdent (Name.mkSimple exportName.getString)
  elabCommand (← `(
    @[export $exportIdent]
    def $defName (_ : Unit) : String := $(Lean.quote smtStr)
  ))
  logInfo m!"#export_smt: generated {smtStr.length} chars of SMT-LIB 2 for '{resolvedName}'"

end Blaster.Wasm
