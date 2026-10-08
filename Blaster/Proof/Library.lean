import Lean

/-!
# Library facts

Ordinary theorems about library definitions (for example laws of a builtin
operation or of an encoding) that a library states and proves with Blaster.
Automatic induction and invariant inference instantiate the registered facts
whose statements mention definitions reachable from a goal. A registered fact
is never assumed: the attribute checks that its proof is Blaster's own
(depending on `Blaster.Tactic.blasterProven`), with no other non-standard axiom.
-/
namespace Blaster.Proof.Library
open Lean Meta

initialize extension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.flatten
  }

/-- The axiom by which Blaster's SMT translation proves a goal: the trust
boundary of every proof that uses the solver. -/
def solverAxiom : Name := `Blaster.Tactic.blasterProven

/-- Register the theorem `name` as a library fact, after checking that Blaster
proved it (it uses `Blaster.Tactic.blasterProven` and no axiom besides the
standard ones). -/
def register (name : Name) : MetaM Unit := do
  let .thmInfo info ← getConstInfo name
    | throwError "blaster_library requires a theorem: {name}"
  unless info.levelParams.isEmpty do
    throwError "blaster_library facts must be monomorphic: {name}"
  let axioms ← collectAxioms name
  unless axioms.contains solverAxiom do
    throwError "blaster_library facts must be proved by blaster: {name}"
  unless axioms.all #[``propext, ``Quot.sound, ``Classical.choice, solverAxiom].contains do
    throwError "blaster_library fact {name} depends on the axioms {axioms}"
  modifyEnv fun env => extension.addEntry env name

initialize registerBuiltinAttribute {
  name := `blaster_library
  descr := "Register a theorem proved by blaster as a library fact for automatic verification"
  applicationTime := .afterTypeChecking
  add := fun name stx _ => do
    Attribute.Builtin.ensureNoArgs stx
    MetaM.run' (register name)
}

/-- Registered facts whose statements mention one of `constants`. Only facts
of imported modules: the facts a library is still establishing are proved
with the summaries their own proofs name, and every one of them offered to
every later proof of the same file multiplies fact instantiation. -/
def relevant (constants : Array Name) : CoreM (Array Expr) := do
  let env ← getEnv
  let mut result := #[]
  for name in extension.getState env do
    if (env.getModuleIdxFor? name).isNone then continue
    let some info := env.find? name | continue
    if info.type.getUsedConstants.any constants.contains then
      result := result.push (mkConst name)
  return result

/-- Registered facts (of imported modules) all of whose definitions are among
`constants`: a stricter selection, for constants reached less directly. -/
def relevantCovered (constants : Array Name) : CoreM (Array Expr) := do
  let env ← getEnv
  let known := Std.HashSet.ofArray constants
  let mut result := #[]
  for name in extension.getState env do
    if (env.getModuleIdxFor? name).isNone then continue
    let some info := env.find? name | continue
    -- value-level definitions only (a type abbreviation is not a program)
    let definitions := info.type.getUsedConstants.filter fun c =>
      match env.find? c with
      | some (.defnInfo d) =>
        let body := d.type.getForallBody
        -- nor is a type-class instance
        !body.isSort && !(match body.getAppFn with
          | .const cls _ => isClass env cls
          | _ => false)
      | _ => false
    if !definitions.isEmpty && definitions.all known.contains then
      result := result.push (mkConst name)
  return result

end Blaster.Proof.Library
