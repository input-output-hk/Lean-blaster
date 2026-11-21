import Lean
import Blaster.Optimize.Env.Types
import Blaster.Optimize.Env.ExtensionGen

open Lean Meta Blaster.Optimize

namespace Blaster

/-- Uniform signature of every optimization function. -/
abbrev OptFn := (f : Expr) → (args : Array Expr) → TranslateEnvT (Option Expr)

instance : Inhabited OptFn := ⟨fun _ _ => pure none⟩

/-- What is serialized into the .olean file: pure data, no closures. -/
structure OLeanBlasterExtension where
  /-- target of optimization function, e.g., Nat.add -/
  head : Name
  /-- Name of optimization function -/
  declName : Name
 deriving Inhabited, BEq, Repr

/-- In-memory entry: the olean data + the materialized function.
    Never serialized — rebuilt from `OLeanBlasterEntry` at import time. -/
structure BlasterExtension extends OLeanBlasterExtension where
  fn : OptFn

instance : Inhabited BlasterExtension := ⟨{ head := default, declName := default, fn := default }⟩

/-- Interpreter evaluation of a `def ... : OptFn`, for registration time (CoreM). -/
private unsafe def evalOptFnUnsafe (declName : Name) : CoreM OptFn := do
  match (← getEnv).evalConst OptFn (← getOptions) declName with
  | .ok fn     => return fn
  | .error msg => throwError "failed to evaluate '{declName}' as OptFn: {msg}"

@[implemented_by evalOptFnUnsafe]
opaque evalOptFn (declName : Name) : CoreM OptFn

/-- Same as evalOptfnUnsafe but for import time (ImportM), used by `ofOLeanEntry`. -/
private unsafe def evalOptFnImportUnsafe (declName : Name) : ImportM OptFn := do
  let ctx ← read
  IO.ofExcept <| ctx.env.evalConst OptFn ctx.opts declName

@[implemented_by evalOptFnImportUnsafe]
opaque evalOptFnImport (declName : Name) : ImportM OptFn

/-- Rebuild the in-memory entry from the serialized one.
    Runs once per entry per importing process.
-/
def OLeanBlasterExtension.toBlasterExtension (e : OLeanBlasterExtension) : ImportM BlasterExtension :=
  return { e with fn := ← evalOptFnImport e.declName }

/-! ## Global Blaster extension map -/

initialize blasterExt :
    ScopedEnvExtension OLeanBlasterExtension BlasterExtension (NameMap (Array BlasterExtension)) ←
  registerScopedEnvExtension {
    mkInitial    := pure {}
    ofOLeanEntry := fun _ e => e.toBlasterExtension
    toOLeanEntry := BlasterExtension.toOLeanBlasterExtension
    addEntry     := fun m e => m.insert e.head (((m.find? e.head).getD #[]).push e)
  }

/-! ## Blaster extension attribute -/
/-- `@[blaster]` registers an optimization function:
     - on a definition of type `Blaster.OptFn`, the target head constant must be specified,
       e.g., `@[blaster Nat.add]`;
     - on a theorem/axiom, an optimization function is generated (see `Blaster.ThmOptFn`);
       - `(noRestart := true)` do not pass the returned term to the optimization process again.
       - `(register := false)` do not register the generated optimize function in Blaster database.
       - `(cyclicCheck := false)` do not check the theorem for cyclic rewriting with the previously
         tagged theorems/axioms (see `Blaster.Optimize.Env.ExtensionRules`); the theorem is still
         recorded for the check of the subsequent ones.
-/
declare_syntax_cat extensionOption
syntax (ppSpace "(" &"noRestart" " := " term ")") : extensionOption
syntax (ppSpace "(" &"register" " := " term ")") : extensionOption
syntax (ppSpace "(" &"cyclicCheck" " := " term ")") : extensionOption

syntax (name := blaster) "blaster" (ppSpace ident)? (extensionOption)* : attr


/-- Blaster extension options passed as argument -/
structure ExtensionOptions where
  /-- subject of annotation (if any) -/
  declName : Option Name := none
  /-- When `true`, restart is NOT triggered after rewriting is performed from the registered theorem. -/
  noRestart : Bool := false
  /-- When `false`, only the optimization function is generated for the annotated theorem. -/
  register : Bool := true
  /-- When `false`, the static cyclic rewriting check is skipped for the annotated theorem. -/
  cyclicCheck : Bool := true

instance : Inhabited ExtensionOptions where
  default := {}


def parseBoolFlag (b : Term) (msg : String) : AttrM Bool := do
  if b.raw.isIdent && b.raw.getId == `true then pure true
  else if b.raw.isIdent && b.raw.getId == `false then pure false
  else throwErrorAt b "@[blaster]: `true` or `false` expected for the {msg} flag"

/-- Parse one extension option and update `opts` accordingly (the last occurrence of an option wins). -/
def parseExtensionOption (opts : ExtensionOptions) : TSyntax `extensionOption → AttrM ExtensionOptions
 | `(extensionOption| (noRestart := $b:term)) => return { opts with noRestart := ← parseBoolFlag b "noRestart" }
 | `(extensionOption| (register := $b:term)) => return { opts with register := ← parseBoolFlag b "register" }
 | `(extensionOption| (cyclicCheck := $b:term)) => return { opts with cyclicCheck := ← parseBoolFlag b "cyclicCheck" }
 | stx => throwErrorAt stx "@[blaster]: unexpected option"

def parseExtensionOptions (args : TSyntaxArray `extensionOption) (opts : ExtensionOptions) : AttrM ExtensionOptions :=
  args.foldlM (init := opts) parseExtensionOption

initialize registerTraceClass `Optimize.extension

def isTheoremAxiom? (info : ConstantInfo) (declName : Name) : MetaM (Option Expr) := do
  match info with
  | ConstantInfo.thmInfo tinfo => return tinfo.type
  | ConstantInfo.axiomInfo ainfo =>
      if wasOriginallyTheorem (← getEnv) declName then return none
      else if ← isProp (ainfo.type) then return ainfo.type
      else return none
  | _ => return none

/-- Generate and compile the optimization function for theorem/axiom `declName` of type `thm`
    (see `Blaster.ThmOptFn.generate`). The generated function is named as an explicit
    `def <p'>.blaster_opt_<name>` in the current namespace would be, for `declName := <p>.<name>` and
    `<p'>` the namespace `<p>` relative to the current one (see `Blaster.ThmOptFn.mkOptFnName`).
    Return the entry to register along with the rule to record for the static cyclic rewriting check,
    `none` when nothing has been generated (theorem handled natively, or cyclic rewriting detected).
-/
def generateThmOptimizationFun
  (declName : Name) (thm : Expr) (noRestart : Bool := false) (headOverride? : Option Name := none)
  (cyclicCheck : Bool := true)
  : MetaM (Option (OLeanBlasterExtension × ThmOptFn.Rule)) := do
  match ← ThmOptFn.generate { thmName := declName, thmType := thm, noRestart, headOverride?, cyclicCheck } (mkConst ``OptFn) with
  | .generated res =>
      trace[Optimize.extension] "optimization function generated for `{declName}` (target `{res.head}`):\ndef {res.declName} : OptFn :=\n{res.code}"
      return some ({ head := res.head, declName := res.declName }, res.rule)
  | .native =>
      logInfo m!"@[blaster]: `{declName}` is already handled natively by the Blaster, no optimization function generated"
      return none
  | .cyclic _ => return none -- warning already logged

/-- Parse the arguments of the `blaster` attribute: the optional target head constant
    followed by any number of options, e.g.,
    `@[blaster]`, `@[blaster Nat.add]`, `@[blaster (restart := true)]`,
    `@[blaster Nat.add (register := false) (restart := true)]`.
-/
private def parseAttrArgs (stx : Syntax) : AttrM ExtensionOptions := do
  match stx with
  | `(attr| blaster $[$h:ident]? $opts:extensionOption*) =>
      let headOverride? ← h.mapM fun h => realizeGlobalConstNoOverload h
      let opts ← parseExtensionOptions opts { declName := headOverride? }
      return opts
  | _ => throwErrorAt stx "@[blaster]: unexpected attribute syntax"

initialize registerBuiltinAttribute {
  name  := `blaster
  descr := "register an optimization function, or generate one from a tagged theorem"
  applicationTime := .afterCompilation  -- compiled code must exist before evalConst
  add   := fun declName stx attrKind => do
    let opts ← parseAttrArgs stx
    let info ← getConstInfo declName
    if let some thm ← MetaM.run' (isTheoremAxiom? info declName) then
      let some (olean, rule) ← MetaM.run' (generateThmOptimizationFun declName thm opts.noRestart opts.declName opts.cyclicCheck)
        | return ()
      let fn ← evalOptFn olean.declName
      -- record the rule for the static cyclic rewriting check of the subsequent theorems
      ThmOptFn.blasterRuleExt.add rule attrKind
      unless !(opts.register) do -- add to database only when register flag is set to true.
        blasterExt.add { olean with fn} attrKind
    else
      -- only consider hand-written optimization function for now
      let ok ← MetaM.run' <| withReducible <| isDefEq info.type (mkConst ``OptFn)
      unless ok do
        throwError "@[blaster]: '{declName}' must have type 'Blaster.OptFn'"
      let some head := opts.declName
        | throwError "@[blaster]: specify the target head constant, e.g. @[blaster Nat.add]"
      let olean : OLeanBlasterExtension := { head, declName }
      let fn ← evalOptFn declName -- materializing function at registration
      blasterExt.add { olean with fn } attrKind
}

def hasRegisteredOptFns (f : Name) : CoreM Bool :=
  return (blasterExt.getState (← getEnv)).contains f

/-- Try every optimizations registered for `f`. -/
def applyRegisteredOptFns (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  let Expr.const n _ := f | return none
  let optEntries ← liftM (getOptEntries n)
  if optEntries.isEmpty then return none
  -- reorder operands for commutative operators
  let args ← reorderOperands f args
  for entry in optEntries do
    if let some e ← entry.fn f args then return some e
  return none

 where
   getOptEntries (f : Name) : CoreM (Array BlasterExtension) :=
     return ((blasterExt.getState (← getEnv)).find? f).getD #[]

end Blaster
