import Blaster.Proof.Export.Basic
import Blaster.Proof.Export.Print
import Blaster.Proof.Export.Term
import Blaster.Proof.Library

/-!
# Exporting a proof as a Lean file

`exportProof` writes the kernel proof that `blaster (induction: auto)` built
for a goal as a Lean file, one declaration at a time:

* the file starts with the source of the current file before the declaration
  being proved, so that everything the proof refers to is defined the same way;
* every constant the tactic made while proving (observed functions and their
  equations, facts, verification conditions), every constant the file could
  not name (lemmas Lean derives on demand, internal names), and every
  imported theorem that relies on Blaster's SMT translation (a library fact
  proved with `blaster`) is declared, in the namespace of the declaration
  being proved;
* every use of `Blaster.Tactic.blasterProven`, the axiom by which Blaster's
  SMT translation proves a goal, in the proof or in those imported theorems,
  becomes a theorem of its own whose statement is exactly the proposition the
  solver proved, quantified over the variables it mentions: these theorems
  are the whole contribution of the solver;
* a replay of the explorer is split into its statements and their proofs
  (`Replay`);
* the last theorem states the goal and proves it from the declarations before.

What the export changes (the solver's theorems and the declarations using
them, the replays, the goal's proof) is checked by the kernel before the file
is written. Compiling the file checks all of it again, from its text.
-/
namespace Blaster.Proof.Export
open Lean Meta Elab

/-! ## The solver's theorems -/

/-- A binder on the way to a subterm: its name, type, kind and (for a `let`) value. -/
structure Binder where
  name : Name
  type : Expr
  info : BinderInfo
  value? : Option Expr := none
  deriving Inhabited

/-- The theorems that the uses of the solver's axiom become (one per proposition). -/
structure Floating where
  /-- The theorem for each proposition proved by the solver. -/
  theorems : Std.HashMap ExprStructEq Name := {}
  /-- Their declarations, in order. -/
  decls : Array Decl := #[]
  /-- Whether a subterm mentions the solver's axiom. -/
  mentions : Std.HashMap ExprStructEq Bool := {}

abbrev FloatM := StateRefT Floating MetaM

/-- Whether `e` uses the solver's axiom (memoized). -/
partial def mentionsSolver (e : Expr) : FloatM Bool := do
  match e with
  | .const n _ => return n == Library.solverAxiom
  | .mdata _ b | .proj _ _ b => mentionsSolver b
  | .app .. | .lam .. | .forallE .. | .letE .. =>
    if let some r := (← get).mentions[(⟨e⟩ : ExprStructEq)]? then return r
    let r ← match e with
      | .app f a => pure ((← mentionsSolver f) || (← mentionsSolver a))
      | .lam _ t b _ | .forallE _ t b _ => pure ((← mentionsSolver t) || (← mentionsSolver b))
      | .letE _ t v b _ => pure ((← mentionsSolver t) || (← mentionsSolver v) || (← mentionsSolver b))
      | _ => pure false
    modify fun st => {st with mentions := st.mentions.insert ⟨e⟩ r}
    return r
  | _ => return false

/-- The theorem for the proposition `p` that the solver proved at a position
under `stack` (innermost last): `∀ xs, p` over the variables `p` mentions,
closed under the variables their types and values mention; and its
application to those variables. -/
def solverTheorem (base : Name) (p : Expr) (stack : Array Binder) : FloatM Expr := do
  let binderAt (i : Nat) : Binder := stack[stack.size - 1 - i]!
  -- (de Bruijn indices at the position; a binder's type and value are under the binders before it)
  let mut needed : Std.HashSet Nat := {}
  let mut work := p.collectLooseBVars.toArray
  while !work.isEmpty do
    let i := work.back!
    work := work.pop
    if needed.contains i then continue
    needed := needed.insert i
    let b := binderAt i
    for j in b.type.collectLooseBVars do work := work.push (i + 1 + j)
    if let some v := b.value? then
      for j in v.collectLooseBVars do work := work.push (i + 1 + j)
  let order := needed.toArray.qsort (· > ·)
  -- the statement, over local declarations for these variables, outermost first
  let rec go (k : Nat) (fvars : Std.HashMap Nat Expr) (xs : Array Expr) : MetaM Expr := do
    let inst (e : Expr) (offset : Nat) : Expr :=
      e.instantiate (Array.ofFn (n := e.looseBVarRange) fun j => fvars.getD (offset + j) (mkConst ``True))
    if h : k < order.size then
      let i := order[k]
      let b := binderAt i
      let type := inst b.type (i + 1)
      match b.value? with
      | some v => withLetDecl b.name type (inst v (i + 1)) fun x => go (k + 1) (fvars.insert i x) (xs.push x)
      | none => withLocalDecl b.name b.info type fun x => go (k + 1) (fvars.insert i x) (xs.push x)
    else
      mkForallFVars xs (inst p 0)
  let statement ← instantiateMVars (← go 0 {} #[])
  if statement.hasLooseBVars || statement.hasFVar || statement.hasMVar then
    throwError "export: a proposition the solver proved is not closed"
  -- (the universe parameters of the declaration it mentions are the theorem's)
  let levelParams := (collectLevelParams {} statement).params.toList
  let name ← match (← get).theorems[(⟨statement⟩ : ExprStructEq)]? with
    | some name => pure name
    | none =>
      let name := base ++ .mkSimple s!"blaster_{(← get).decls.size + 1}"
      let value := mkApp (mkConst Library.solverAxiom [← getLevel statement]) statement
      modify fun st => {st with theorems := st.theorems.insert ⟨statement⟩ name,
                                decls := st.decls.push {name, levelParams, type := statement, value,
                                                        group := .solver}}
      pure name
  let args := order.filterMap fun i => if (binderAt i).value?.isSome then none else some (mkBVar i)
  return mkAppN (mkConst name (levelParams.map mkLevelParam)) args

/-- `e` (under `stack`) with every use of the solver's axiom replaced by an
application of its theorem. -/
partial def floatSolver (base : Name) (e : Expr) (stack : Array Binder := #[]) : FloatM Expr := do
  unless ← mentionsSolver e do return e
  match e with
  | .app f a =>
    if f.isConstOf Library.solverAxiom then
      return ← solverTheorem base (← floatSolver base a stack) stack
    return e.updateApp! (← floatSolver base f stack) (← floatSolver base a stack)
  | .lam n t b bi =>
    return e.updateLambda! bi (← floatSolver base t stack)
      (← floatSolver base b (stack.push {name := n, type := t, info := bi}))
  | .forallE n t b bi =>
    return e.updateForall! bi (← floatSolver base t stack)
      (← floatSolver base b (stack.push {name := n, type := t, info := bi}))
  | .letE n t v b nondep =>
    return e.updateLet! (← floatSolver base t stack) (← floatSolver base v stack)
      (← floatSolver base b (stack.push {name := n, type := t, info := .default, value? := v})) nondep
  | .mdata _ b => return e.updateMData! (← floatSolver base b stack)
  | .proj _ _ b => return e.updateProj! (← floatSolver base b stack)
  | _ => throwError "export: `{Library.solverAxiom}` is used without the proposition it proves"

/-! ## The declarations of the file -/

/-- Whether the file can refer to `n` by name: a public name, or a private one
of this file (the file declares those again under the same names, and Lean
derives a lemma with a reserved name, such as a matcher's equation, on demand). -/
def referable (env : Environment) (n : Name) : Bool :=
  let user? := if isPrivateName n then
      let user := privateToUserName n
      if mkPrivateName env user == n then some user else none
    else some n
  match user? with
  | some user => !user.isAnonymous && !user.hasMacroScopes && !user.isInternalOrNum
  | none => false

/-- The modules that import the module of the solver's axiom, or are it: only
their constants can rely on it. Modules come after those they import. -/
def solverModules (env : Environment) : NameSet := Id.run do
  let some idx := env.getModuleIdxFor? Library.solverAxiom | return {}
  let mut result : NameSet := ({} : NameSet).insert env.header.moduleNames[idx.toNat]!
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    if data.imports.any (result.contains ·.module) then result := result.insert name
  return result

/-- Whether the imported constant `c` relies on the solver's axiom, through its
type or value (memoized in `memo`; `modules` are `solverModules`). -/
partial def reliesOnSolver (modules : NameSet) (memo : IO.Ref (NameMap Bool)) (c : Name) :
    CoreM Bool := do
  if c == Library.solverAxiom then return true
  if let some r := (← memo.get).find? c then return r
  let env ← getEnv
  let some idx := env.getModuleIdxFor? c | return false
  unless modules.contains env.header.moduleNames[idx.toNat]! do return false
  -- (a constant on a cycle being examined is taken not to: theorems form no cycles)
  memo.modify (·.insert c false)
  let some info := env.find? c | return false
  let used := info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map
    (·.getUsedConstants)).getD #[]
  let r ← used.anyM (reliesOnSolver modules memo)
  memo.modify (·.insert c r)
  return r

/-- The constants the file declares: those `roots` use, directly or through
each other, that it cannot refer to by name: made by the proof (absent from
`start`, or named after the declaration `base`), except the lemmas Lean
derives on demand from their (reserved) names, and the unnameable ones; and
the imported theorems that rely on the solver's axiom, so that every use of it
is among the file's (`blaster_i`). Each comes after those it uses. -/
partial def generatedConstants (roots : Array Expr) (start : Environment) (base : Name)
    (skip : NameSet) : CoreM (Array Name) := do
  let env ← getEnv
  let modules := solverModules env
  let memo ← IO.mkRef ({} : NameMap Bool)
  let declares (c : Name) : CoreM Bool := do
    if skip.contains c then return false
    if base.isPrefixOf (privateToUserName c) || !referable env c then return true
    if (env.getModuleIdxFor? c).isNone then return !start.contains c && !isReservedName env c
    -- (a theorem is replaced by its copy without changing the meaning of a term)
    return (env.find? c matches some (.thmInfo _)) && (← reliesOnSolver modules memo c)
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array Name)
  let rec visit (c : Name) : CoreM Unit := do
    if (← visited.get).contains c then return
    visited.modify (·.insert c)
    unless ← declares c do return
    let info ← getConstInfo c
    unless info matches .thmInfo _ | .defnInfo _ do
      throwError "export: the proof uses `{c}`, which a Lean file can neither name nor declare"
    for d in info.type.getUsedConstants do visit d
    if let some v := info.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit d
    out.modify (·.push c)
  for root in roots do
    for c in root.getUsedConstants do visit c
  out.get

/-- Friendlier names for what Blaster's provers declare. -/
def kindNames : List (String × String) :=
  [("exploreVC", "condition"), ("exploreLink", "link"), ("blasterObserverFact", "fact"),
   ("blasterObserved", "observed"), ("blasterSourceEquation", "source_equation"),
   ("blasterListViews", "list_view")]

/-- The name under which the file declares constant `n`, not in `used`. A
copy of a lemma with a reserved name (`f.eq_1`) is named so that Lean does not
reserve it for the copy of `f` (`f_eq_1`). -/
def exportName (base : Name) (n : Name) (reserved : Bool) (used : NameSet) : Name := Id.run do
  let user := privateToUserName n
  let (relative, aux) := if base.isPrefixOf user then (user.replacePrefix base .anonymous, false)
    else (user, true)
  let mut parts : Array String := #[]
  let mut numbered := false
  -- (numbers are dropped, and so are the macro scopes of a hygienic name: its
  -- components from `_@` to `_hyg`, such as `_@.M.12._hygCtx._hyg.3`)
  let mut hygienic := false
  for c in relative.components do
    let .str _ s := c | continue
    if s == "_@" then hygienic := true
    else if s == "_hyg" then hygienic := false
    else if !hygienic && s != "_uniq" then
      match kindNames.lookup s with
      | some kind => parts := parts.push kind; numbered := true
      | none =>
        let s := s.dropWhile (· == '_')
        unless s.isEmpty do parts := parts.push s
  if parts.isEmpty then parts := #["lemma"]
  if reserved && parts.size ≥ 2 then
    parts := (parts.extract 0 (parts.size - 2)).push (parts[parts.size - 2]! ++ "_" ++ parts.back!)
  let mk (suffix : String) : Name :=
    let parts := parts.modify (parts.size - 1) (· ++ suffix)
    parts.foldl (init := if aux then base ++ `aux else base) Name.str
  if !numbered && !used.contains (mk "") then return mk ""
  let mut i := 1
  while used.contains (mk s!"_{i}") do i := i + 1
  return mk s!"_{i}"

/-- The declarations in an order where each comes after those it uses, and
otherwise the earlier group first. -/
def orderDecls (decls : Array Decl) : Array Decl := Id.run do
  let index : Std.HashMap Name Nat := decls.zipIdx.foldl (init := {}) fun m (d, i) => m.insert d.name i
  let deps := decls.map fun d =>
    ((d.type.getUsedConstants ++ d.value.getUsedConstants).filterMap (index[·]?)).toList.eraseDups
  let mut users : Array (Array Nat) := Array.replicate decls.size #[]
  for (ds, i) in deps.zipIdx do
    for d in ds do users := users.modify d (·.push i)
  let mut waiting := deps.map (·.length)
  let mut ready : Array Nat := (Array.range decls.size).filter (waiting[·]! == 0)
  let mut out := #[]
  while !ready.isEmpty do
    let mut best := 0
    for j in [1:ready.size] do
      let (a, b) := (decls[ready[j]!]!, decls[ready[best]!]!)
      if a.group.rank < b.group.rank || (a.group.rank == b.group.rank && ready[j]! < ready[best]!) then
        best := j
    let i := ready[best]!
    ready := ready.eraseIdx! best
    out := out.push decls[i]!
    for u in users[i]! do
      waiting := waiting.modify u (· - 1)
      if waiting[u]! == 0 then ready := ready.push u
  return out

/-! ## The file -/

/-- The command of the current file containing position `pos`: the source
before it, and its syntax. -/
def commandAt (pos : String.Pos) : CoreM (String × Syntax) := do
  let source := (← getFileMap).source
  let input := Parser.mkInputContext source (← getFileName)
  let (_, state, _) ← Parser.parseHeader input
  let context : Parser.ParserModuleContext := {env := ← getEnv, options := ← getOptions}
  let mut state := state
  repeat
    if input.atEnd state.pos then break
    let (command, next, _) := Parser.parseCommand input context state {}
    if pos < next.pos then
      return (source.extract 0 (command.getPos?.getD state.pos), command)
    if next.pos == state.pos then break
    state := next
  throwError "export: the declaration being proved was not found in the source"

/-- The identifier a declaration command declares, if any. -/
partial def declaredId? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Parser.Command.declId then some stx[0].getId
  else stx.getArgs.findSome? declaredId?

/-- `ns` without the trailing components `p`. -/
def dropSuffix (ns p : Name) : Name :=
  match ns, p with
  | .str ns s, .str p t => if s == t then dropSuffix ns p else ns
  | ns, .anonymous => ns
  | ns, _ => ns

/-- `s` inside a comment: no comment starts or ends in it. -/
def commentText (s : String) : String :=
  (s.replace "/-" "/ -").replace "-/" "- /"

/-- The resident memory of the process, in MiB, where the system reports it. -/
def residentMiB : IO (Option Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let some line := status.splitOn "\n" |>.find? (·.startsWith "VmRSS:") | return none
    return (line.drop 6).trim.takeWhile Char.isDigit |>.toNat? |>.map (· / 1024)
  catch _ => return none

/-- Report the export's progress on standard error (with `blaster.explore.progress`). -/
def progress (start : Nat) (msg : String) : CoreM Unit := do
  if (← getOptions).getBool `blaster.explore.progress true then
    let memory := match ← residentMiB with
      | some m => s!", {m} MiB"
      | none => ""
    (← IO.getStderr).putStrLn s!"[export {((← IO.monoMsNow) - start) / 1000}s{memory}] {msg}"

/-- What a group of declarations is, for the reader of the file. -/
def Group.title : Group → String
  | .definitions => "Definitions derived by the tactic"
  | .solver => "Propositions proved by Blaster's SMT translation\n\n\
      Each is proved by `Blaster.Tactic.blasterProven`, the axiom that records an SMT proof: these \
      theorems are all the solver contributes to the proof (the library theorems that rely on it \
      are copied below, with their own uses of it among these), and each states exactly the \
      proposition the solver proved."
  | .library => "Library theorems\n\n\
      Copies of the theorems of imported libraries that the proof uses and that rely on Blaster's \
      SMT translation (proved with `blaster`, or from such theorems), and of those a Lean file \
      cannot name."
  | .lemmas => "Lemmas derived and proved by the tactic"
  | .conditions => "Verification conditions"
  | .statements => "The statements of the replay\n\n\
      The replay proves its statements together, by strong induction on the fuel: `all` is \
      their conjunction, a binary heap (statement `i` is node `i`)."
  | .proofs => "The proofs of the replay's statements, from the induction hypothesis"
  | .result => "The replay"

/-- The universe parameters of a declaration, as written after its name. -/
def universeParams (ls : List Name) : String :=
  if ls.isEmpty then "" else ".{" ++ ", ".intercalate (ls.map toString) ++ "}"

/-- How the printer names the constants of `terms` in the namespace `ns`: each
by the shortest name that refers to it there (after `renamed`). Shared terms
are referred to as `globalRef ++ "term_i"`. -/
def namesIn (ns : Name) (terms : Array Expr) (renamed : Std.HashMap Name Name)
    (types : Std.HashMap Name Expr) (globalName : Name) (globalRef : String)
    (isToken : String → Bool) : CoreM Names := do
  let textAbove := blaster.induction.exportTextAbove.get (← getOptions)
  let mut names : Names := {globalName, globalRef, isToken, textAbove}
  let mut seen : NameSet := {}
  for e in terms do
    for c in e.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      let printed ← withReader (fun ctx => {ctx with currNamespace := ns})
        (unresolveNameGlobal (renamed.getD c c))
      let root := printed.getRoot.toStringWithToken true isToken
      -- (a constant named like a shared term would be captured by it)
      if isNumbered "term" root then
        throwError "export: the proof uses `{c}`, named like the file's shared terms"
      let type ← match types[c]? with
        | some t => pure t
        | none => pure (← getConstInfo c).type
      names := {names with
        consts := names.consts.insert c (printed.toStringWithToken true isToken)
        explicit := if hasImplicit type then names.explicit.insert c else names.explicit
        reserved := names.reserved.insert root}
  return names

/-- Print the declarations and the goal into the file. The declarations are in
the namespace of the declaration being proved (when it is in the command's
namespace `commandNs`), so that they refer to each other by short names. -/
def writeFile (path : System.FilePath) (base commandNs : Name) (prefixText original : String)
    (decls : Array Decl) (renamed : Std.HashMap Name Name) (mainType mainValue : Expr)
    (levelParams : List Name) (docs : Std.HashMap Name String) (clock : Nat) : CoreM Unit := do
  let tokens := Parser.getTokenTable (← getEnv)
  let isToken := fun (s : String) => (tokens.find? s).isSome
  let types : Std.HashMap Name Expr := decls.foldl (init := {}) fun m d => m.insert d.name d.type
  let nested := commandNs.isPrefixOf base
  let relative := (base.replacePrefix commandNs .anonymous).toStringWithToken true isToken
  let full := (`_root_ ++ base).toStringWithToken true isToken
  let inner ← namesIn (if nested then base else commandNs) (decls.flatMap fun d => #[d.type, d.value])
    renamed types base (if nested then "" else full ++ ".") isToken
  let outer ← namesIn commandNs #[mainType, mainValue] renamed types base
    ((if nested then relative else full) ++ ".") isToken
  IO.FS.createDirAll (path.parent.getD ".")
  let h ← IO.FS.Handle.mk path .write
  h.putStr prefixText
  let solverCount := decls.filter (·.group == .solver) |>.size
  h.putStr s!"\n/-!\n# The proof of `{base}` found by Blaster\n\n\
    Written by `blaster (induction: auto)` (option `blaster.induction.export`): the proof of the \
    declaration below, as the kernel checks it, one declaration at a time. `kernel% t` is the \
    term `t` exactly as written, checked by the kernel only. Repeated subterms are printed \
    once: closed ones as definitions `term_i`, others as `let`s `t_i`.\n\n\
    {decls.size} declarations; {solverCount} propositions proved by Blaster's SMT translation \
    (`blaster_i`).\n\nCompiling the file (`lake env lean FILE`, in the project of the \
    declaration) checks all of it again, from its text.\n\n\
    The declaration as written:\n```\n{commentText original}\n```\n-/\n\n\
    set_option autoImplicit false\nset_option relaxedAutoImplicit false\n\
    set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\
    set_option linter.unusedVariables false\n"
  if nested then h.putStr s!"\nnamespace {relative}\n"
  let mut printer : Printer := {}
  let mut group? : Option Group := none
  let mut written := 0
  for d in decls do
    written := written + 1
    if written % 100 == 0 then progress clock s!"printed {written}/{decls.size} declarations"
    if group? != some d.group then
      h.putStr s!"\n/-! ## {d.group.title} -/\n"
      group? := some d.group
    let declName := (`_root_ ++ renamed.getD d.name d.name).toStringWithToken true isToken
    let header := (if d.isDef then "noncomputable def " else "theorem ") ++ declName ++
      universeParams d.levelParams
    let value? := if d.group == .solver then some "Blaster.Tactic.blasterProven" else none
    let ((globals, text), st) := ((printDecl header d.type d.value value?).run inner).run printer
    printer := st
    for g in globals do h.putStr s!"\n{g}\n"
    h.putStr "\n"
    if let some doc := docs[d.name]? then h.putStr s!"/-- {commentText doc} -/\n"
    h.putStr text
    h.putStr "\n"
  if nested then h.putStr s!"\nend {relative}\n"
  -- the goal
  let header := "theorem " ++ full ++ universeParams levelParams
  let ((globals, text), _) := ((printDecl header mainType mainValue none).run outer).run printer
  h.putStr "\n/-! ## The theorem -/\n"
  for g in globals do h.putStr s!"\n{g}\n"
  h.putStr s!"\n{text}"
  h.putStr s!"\n\n#print axioms {if nested then relative else full}\n"
  h.flush

/-- Write the proof `proof` of `goal` (found by `blaster (induction: auto)` at
`ref`; the environment was `start` when it began; `replays` give the structure
of the replays it uses) as a Lean file, if `blaster.induction.export` is set. -/
def exportProof (goal : MVarId) (proof : Expr) (start : Environment) (replays : Array Replay)
    (ref : Syntax) : TermElabM Unit := do
  let some target ← target? | return
  let clock ← IO.monoMsNow
  let some base ← Term.getDeclName? | throwError "export: no declaration is being elaborated"
  if base.isInternal then
    throwError "export: only the proofs of public named declarations are exported, not `{base}`"
  let some pos := ref.getPos? | throwError "export: the tactic has no source position"
  let (prefixText, command) ← commandAt pos
  let source := (← getFileMap).source
  let original := match command.getPos?, command.getTailPos? with
    | some s, some e => source.extract s e
    | _, _ => ""
  -- the scope of the command (a dotted declared name opens its namespace for the declaration)
  let currNs ← getCurrNamespace
  let commandNs := match declaredId? command with
    | some id => if (`_root_).isPrefixOf id then currNs else dropSuffix currNs id.getPrefix
    | none => currNs
  -- the goal, closed over its context, with the replays' structure
  let (mainType, mainValue) ← goal.withContext do
    let xs := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.toExpr
    pure (← instantiateMVars (← mkForallFVars xs (← goal.getType)),
          ← instantiateMVars (← mkLambdaFVars xs proof))
  if mainType.hasFVar || mainValue.hasFVar || mainType.hasMVar || mainValue.hasMVar then
    throwError "export: the proof is not closed"
  let substitution : Std.HashMap Name Name :=
    replays.foldl (init := {}) fun m r => m.insert r.replaces r.result
  let mainValue := mainValue.replace fun
    | .const n ls => (substitution[n]?).map (mkConst · ls)
    | _ => none
  let replayDecls := replays.flatMap (·.decls)
  -- the constants the file declares, and their names
  let skip : NameSet := replays.foldl (init := {}) fun s r =>
    r.decls.foldl (init := s.insert r.replaces) fun s d => s.insert d.name
  let roots := #[mainType, mainValue] ++ replayDecls.flatMap fun d => #[d.type, d.value]
  let generated ← generatedConstants roots start base skip
  let mut renamed : Std.HashMap Name Name := {}
  let mut used : NameSet := replayDecls.foldl (init := {}) fun s d => s.insert d.name
  -- (a constant whose parent is copied too is named like a reserved one: the
  -- copy of the parent is a definition, and Lean reserves names under it, such
  -- as `eq_1`, also when the original, a private name, is not reserved)
  let copied : NameSet := generated.foldl (·.insert ·) {}
  for c in generated do
    let n := exportName base c (isReservedName (← getEnv) c || copied.contains c.getPrefix) used
    renamed := renamed.insert c n
    used := used.insert n
  -- the solver's theorems, floated out of every value
  let mut floating : Floating := {}
  let mut exported : Array Decl := #[]
  let mut changed : NameSet := {}
  for c in generated do
    let info ← getConstInfo c
    let some value := info.value? (allowOpaque := true) | unreachable!
    let imported := ((← getEnv).getModuleIdxFor? c).isSome
    let group : Group := if info.isDefinition then .definitions
      else if c.components.contains `exploreVC then .conditions
      else if imported then .library else .lemmas
    let (value', st) ← (floatSolver base value).run floating
    floating := st
    unless value' == value do changed := changed.insert c
    exported := exported.push {
      name := c, levelParams := info.levelParams, isDef := info.isDefinition, type := info.type
      value := value', group }
  for d in replayDecls do
    let (value, st) ← (floatSolver base d.value).run floating
    floating := st
    changed := changed.insert d.name
    exported := exported.push {d with value}
  let (mainValue, st) ← (floatSolver base mainValue).run floating
  floating := st
  for d in floating.decls do changed := changed.insert d.name
  let decls := orderDecls (floating.decls ++ exported)
  let levelParams := (collectLevelParams (collectLevelParams {} mainType) mainValue).params.toList
  let path : System.FilePath := if target.endsWith ".lean" then target
    else System.FilePath.mk target / s!"{(privateToUserName base).toString (escape := false)}.lean"
  progress clock s!"{decls.size} declarations, {floating.decls.size} proved by the solver; checking"
  -- the kernel checks what the export changed: the solver's theorems, the
  -- declarations using them, the replays and the goal's proof
  withoutModifyingEnv do
    withOptions (Elab.async.set · false) do
      let mut checks := 0
      for d in decls do
        unless changed.contains d.name do continue
        -- (a changed copy of a constant is checked under a name of its own)
        let mut name := d.name
        if renamed.contains d.name then
          checks := checks + 1
          name := base ++ .mkSimple s!"export_check_{checks}"
        if d.isDef then
          addDecl (.defnDecl {
            name, levelParams := d.levelParams, type := d.type, value := d.value
            hints := .regular (getMaxHeight (← getEnv) d.value + 1), safety := .safe })
        else
          addDecl (.thmDecl {name, levelParams := d.levelParams, type := d.type, value := d.value})
      addDecl (.thmDecl {name := base ++ `export_check, levelParams, type := mainType, value := mainValue})
  progress clock "checked; writing the file"
  withoutModifyingEnv do
    -- the file's names of the constants it declares, for its references and the
    -- readable statements of the solver's theorems (unchecked: the kernel checked them)
    let rename (e : Expr) : Expr := e.replace fun
      | .const n ls => (renamed[n]?).map (mkConst · ls)
      | _ => none
    withOptions (debug.skipKernelTC.set · true) do
      for d in decls do
        let n := renamed.getD d.name d.name
        unless (← getEnv).contains n do
          addDecl (.axiomDecl {name := n, levelParams := d.levelParams, type := rename d.type, isUnsafe := false})
    -- the declarations that use each, and readable statements (of a readable size)
    let mut users : Std.HashMap Name (Array Name) := {}
    for d in decls do
      for c in d.value.getUsedConstants do
        users := users.insert c ((users.getD c #[]).push (renamed.getD d.name d.name))
    for c in mainValue.getUsedConstants do
      users := users.insert c ((users.getD c #[]).push base)
    -- (the declarations of the file by their names in its namespace; the theorem by its own)
    let short (u : Name) : Name := if u == base then base else u.replacePrefix base .anonymous
    let usedBy (n : Name) : String := match users[n]? with
      | some us => "Used by " ++ ", ".intercalate (us.toList.take 8 |>.map fun u => s!"`{short u}`") ++
          (if us.size > 8 then ", …" else "") ++ "."
      | none => ""
    -- (statements are shown with names as the file's declarations refer to them)
    let declNs := if commandNs.isPrefixOf base then base else commandNs
    let mut docs : Std.HashMap Name String := {}
    for d in decls do
      unless d.group == .solver || d.group == .conditions do continue
      let mut doc := usedBy d.name
      if d.group == .solver && !exceeds d.type 4000 then
        let shown ← withOptions (fun o => o.setNat `pp.maxSteps 1000000 |>.setBool `pp.deepTerms true) do
          withTheReader Core.Context (fun ctx => {ctx with currNamespace := declNs}) do
            ppExpr (rename d.type)
        let shown := toString shown
        if shown.length ≤ 20000 then doc := shown ++ (if doc.isEmpty then "" else "\n\n" ++ doc)
      unless doc.isEmpty do docs := docs.insert d.name doc
    writeFile path base commandNs prefixText original decls renamed mainType mainValue levelParams docs clock
  logInfo m!"exported the proof to {path}: {decls.size} declarations, \
    {floating.decls.size} of them propositions proved by the SMT solver"

end Blaster.Proof.Export
