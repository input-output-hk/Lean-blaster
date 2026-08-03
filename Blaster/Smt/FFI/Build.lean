import Blaster.Smt.FFI.Sorts
import Blaster.Smt.FFI.Terms
import Blaster.Smt.FFI.Datatypes
import Blaster.Smt.FFI.BuildEnv
import Blaster.Smt.Term

namespace Blaster.Smt.FFI
open Blaster.Smt

/-- Translate a SortExpr into a Z3 sort, resolving Nat→Int, Prop→Bool, and
    declared/aliased sorts via the build env. -/
partial def buildSort (se : SortExpr) : BuildM Z3Sort := do
  let ctx := (← get).ctx
  match se with
  | .SymbolSort nm =>
      match nm with
      | .ReservedSymbol "Int"    => ctx.mkIntSort
      | .ReservedSymbol "Nat"    => ctx.mkIntSort         -- Nat aliases Int
      | .ReservedSymbol "Bool"   => ctx.mkBoolSort
      | .ReservedSymbol "Prop"   => ctx.mkBoolSort        -- Prop modelled as Bool
      | .ReservedSymbol "String" => ctx.mkStringSort
      | _ =>
        match (← get).sorts.get? nm with
        | some s => return s
        | none =>
            let s ← ctx.mkUninterpSort nm.toString
            modify fun st => { st with sorts := st.sorts.insert nm s }
            return s
  | .ParamSort (.ReservedSymbol "Array") ps =>
      if ps.size == 2 then
        let d ← buildSort ps[0]!
        let r ← buildSort ps[1]!
        ctx.mkArraySort d r
      else throw (IO.userError s!"buildSort: Array expects 2 params, got {ps.size}")
  | .ParamSort nm _ =>
      match (← get).sorts.get? nm with
      | some s => return s
      | none => throw (IO.userError s!"buildSort: unknown parameterized sort {nm.toString}")

/-- Does `se` mention the sort symbol `target` anywhere? Used to reject
    (MVP: non-recursive datatypes only) self-recursive datatype fields with a
    clear error instead of silently minting an uninterpreted placeholder sort. -/
partial def sortMentions (target : SmtSymbol) : SortExpr → Bool
  | .SymbolSort s   => s == target
  | .ParamSort s ps => s == target || ps.any (sortMentions target)

/-- Strip the surrounding quotes strLitSmt adds to string literals. -/
private def unquote (s : String) : String :=
  if s.length ≥ 2 && s.front == '"' && s.back == '"' then (s.drop 1).dropRight 1 else s

/-- Collect pattern terms from a quantifier's annotations. -/
private def patternsOf (annot : Array SmtAttribute) : Array SmtTerm :=
  annot.foldl (fun acc a => match a with | .Pattern ps => acc ++ ps | _ => acc) #[]

mutual
/-- Translate an SmtTerm to a Z3 Ast. Literals, identifiers, and applications are
    handled here; quantifiers, let, etc. are added in later tasks. -/
partial def buildTerm (t : SmtTerm) : BuildM Ast := do
  let ctx := (← get).ctx
  match t with
  | .NumTerm n  => ctx.mkNumeral (toString n) (← ctx.mkIntSort)
  | .BoolTerm b => ctx.mkBool b
  | .StrTerm s  => ctx.mkStringLit (unquote s)
  | .SmtIdent nm => buildIdent nm
  | .AppTerm nm args => buildApp nm args
  | .ForallTerm bs body => buildQuant true bs body
  | .ExistsTerm bs body => buildQuant false bs body
  | .LambdaTerm bs body => do
      let (b, consts) ← withBound bs (buildTerm body)
      (← get).ctx.mkLambdaConst consts b
  | .AnnotatedTerm t annot =>
      match t with
      | .ForallTerm bs body => buildQuant true bs body (patternsOf annot)
      | .ExistsTerm bs body => buildQuant false bs body (patternsOf annot)
      | _ => buildTerm t
  | .LetTerm bs body => do
      -- SMT-LIB `let` binds SIMULTANEOUSLY: every RHS is evaluated in the OUTER
      -- scope, so translate all values BEFORE pushing any. Then push, build the
      -- body, and pop (mirrors withBound's push/shrink discipline).
      let vals ← bs.mapM (fun (s, v) => do return (s, ← buildTerm v))
      vals.forM fun (s, v) => modify fun st => { st with locals := st.locals.push (s, v) }
      let r ← buildTerm body
      modify fun st => { st with locals := st.locals.shrink (st.locals.size - bs.size) }
      return r
  | _ => throw (IO.userError s!"buildTerm: unhandled term kind (added in a later task)")

partial def buildIdent (nm : SmtQualifiedIdent) : BuildM Ast := do
  let sym := match nm with | .SimpleIdent s => s | .QualifiedIdent s _ => s
  if let some a ← lookupLocal sym then return a
  if let some a := (← get).consts.get? sym then return a
  if let some m := (← get).macros.get? sym then
    if m.params.isEmpty then return (← buildTerm m.body)
  -- a nullary declared/recursive function referenced bare is its 0-ary application
  if let some fd := (← get).recFuncs.get? sym then return (← (← get).ctx.mkApp fd #[])
  if let some fd := (← get).funcs.get? sym then return (← (← get).ctx.mkApp fd #[])
  throw (IO.userError s!"buildIdent: unbound identifier {sym.toString}")

partial def buildApp (nm : SmtQualifiedIdent) (args : Array SmtTerm) : BuildM Ast := do
  let sym := match nm with | .SimpleIdent s => s | .QualifiedIdent s _ => s
  if let some a ← buildBuiltin? sym args then return a
  if let some m := (← get).macros.get? sym then return (← inlineMacro m args)
  let argAsts ← args.mapM buildTerm
  if let some fd := (← get).recFuncs.get? sym then return (← (← get).ctx.mkApp fd argAsts)
  if let some fd := (← get).funcs.get? sym then return (← (← get).ctx.mkApp fd argAsts)
  throw (IO.userError s!"buildApp: unbound function {sym.toString}")

/-- Dispatch the SMT-LIB built-in operators the emitter actually produces to the
    corresponding Z3 constructors. Returns `none` for anything else (define-fun
    wrappers like `@Int.ediv`, user functions, unsupported ops), which then falls
    through to `buildApp`'s macro/func path. Arity is validated via the argument
    list pattern (there is no `Inhabited Ast`, so `!`-indexing is unavailable). -/
partial def buildBuiltin? (sym : SmtSymbol) (args : Array SmtTerm) : BuildM (Option Ast) := do
  let ctx := (← get).ctx
  let bs ← args.mapM buildTerm
  match sym, bs.toList with
  -- boolean / core
  | .ReservedSymbol "and", _         => return some (← ctx.mkAnd bs)
  | .ReservedSymbol "or",  _         => return some (← ctx.mkOr bs)
  | .ReservedSymbol "not", [a]       => return some (← ctx.mkNot a)
  | .ReservedSymbol "=>",  [a, b]    => return some (← ctx.mkImplies a b)
  | .ReservedSymbol "=",   [a, b]    => return some (← ctx.mkEq a b)
  | .ReservedSymbol "ite", [a, b, c] => return some (← ctx.mkIte a b c)
  -- integer arithmetic
  | .ReservedSymbol "+",   _         => return some (← ctx.mkAdd bs)
  | .ReservedSymbol "*",   _         => return some (← ctx.mkMul bs)
  | .ReservedSymbol "-",   [a]       => return some (← ctx.mkNeg a)   -- unary negation
  | .ReservedSymbol "-",   _         => return some (← ctx.mkSub bs)  -- subtraction (nary)
  | .ReservedSymbol "<",   [a, b]    => return some (← ctx.mkLt a b)
  | .ReservedSymbol "<=",  [a, b]    => return some (← ctx.mkLe a b)
  | .ReservedSymbol "div", [a, b]    => return some (← ctx.mkIDiv a b)
  | .ReservedSymbol "mod", [a, b]    => return some (← ctx.mkMod a b)
  | .ReservedSymbol "^",   [a, b]    => return some (← ctx.mkPower a b)
  | .ReservedSymbol "abs",    [a]    => return some (← ctx.mkIntAbs a)
  | .ReservedSymbol "to_int", [a]    => return some (← ctx.mkToInt a)
  -- arrays
  | .ReservedSymbol "select", [a, b] => return some (← ctx.mkSelect a b)
  -- strings
  | .ReservedSymbol "str.len", [a]      => return some (← ctx.mkStrLen a)
  | .ReservedSymbol "str.++",  _        => return some (← ctx.mkStrConcat bs)
  | .ReservedSymbol "str.<",   [a, b]   => return some (← ctx.mkStrLt a b)
  | .ReservedSymbol "str.<=",  [a, b]   => return some (← ctx.mkStrLe a b)
  | .ReservedSymbol "str.replace", [a, b, c] => return some (← ctx.mkStrReplace a b c)
  -- str.replace_all: no Z3 4.15 built-in; falls through to buildApp (throws) by design.
  | _, _ => return none

/-- Inline a non-recursive define-fun macro at an application site. Arg values are
    built in the CALLER's scope (macro args do not see the macro's own params),
    then params are bound as `locals` (like `let`) so `buildIdent` resolves them,
    the body is built, and the pushed locals are popped. -/
partial def inlineMacro (m : MacroDef) (args : Array SmtTerm) : BuildM Ast := do
  if m.params.size != args.size then
    throw (IO.userError s!"inlineMacro: arity mismatch {m.params.size} ≠ {args.size}")
  let vals ← args.mapM buildTerm
  (Array.zip m.params vals).forM fun (p, v) =>
    modify fun st => { st with locals := st.locals.push (p, v) }
  let r ← buildTerm m.body
  modify fun st => { st with locals := st.locals.shrink (st.locals.size - m.params.size) }
  return r

/-- Push each bound var as a FRESH Z3 const into `locals`, run `k`, then pop.
    Returns k's result and the array of fresh bound consts (for the binder). -/
partial def withBound {α : Type} (bs : SortedVars) (k : BuildM α) : BuildM (α × Array Ast) := do
  let ctx := (← get).ctx
  let mut consts : Array Ast := #[]
  for (sym, se) in bs do
    let s ← buildSort se
    let a ← ctx.mkFreshConst sym.toString s
    consts := consts.push a
    modify fun st => { st with locals := st.locals.push (sym, a) }
  let r ← k
  modify fun st => { st with locals := st.locals.shrink (st.locals.size - bs.size) }
  return (r, consts)

partial def buildQuant (isForall : Bool) (bs : SortedVars) (body : SmtTerm)
    (pats : Array SmtTerm := #[]) : BuildM Ast := do
  let ((b, patAsts), consts) ← withBound bs (do
    let b ← buildTerm body
    let patAsts ← pats.mapM buildTerm
    return (b, patAsts))
  (← get).ctx.mkQuantConst isForall 0 consts patAsts b
end

/-- Does `t` reference the symbol `nm` (i.e. is the definition self-recursive)?
    Used as a fallback recursion check when the `isRec` flag is not set. -/
partial def bodyReferences (nm : SmtSymbol) (t : SmtTerm) : Bool :=
  match t with
  | .SmtIdent (.SimpleIdent s) => s == nm
  | .AppTerm (.SimpleIdent s) as => s == nm || as.any (bodyReferences nm)
  | .AppTerm _ as => as.any (bodyReferences nm)
  | .LetTerm bs b => bs.any (fun (_, v) => bodyReferences nm v) || bodyReferences nm b
  | .ForallTerm _ b | .ExistsTerm _ b | .LambdaTerm _ b => bodyReferences nm b
  | .AnnotatedTerm t' _ => bodyReferences nm t'
  | _ => false

/-- Interpret an SmtCommand against the build state (declarations only in this task). -/
partial def runCommand (c : SmtCommand) : BuildM Unit := do
  let ctx := (← get).ctx
  match c with
  | .declareConst nm t =>
      let s ← buildSort t
      let a ← ctx.mkConst nm.toString s
      modify fun st => { st with consts := st.consts.insert nm a }
  | .declareFun nm dom rng =>
      let ds ← dom.mapM buildSort
      let r ← buildSort rng
      let fd ← ctx.mkFuncDecl nm.toString ds r
      modify fun st => { st with funcs := st.funcs.insert nm fd }
  | .declareSort nm _arity =>
      let s ← ctx.mkUninterpSort nm.toString
      modify fun st => { st with sorts := st.sorts.insert nm s }
  | .declareDataType nm decl => do
      -- MVP scope: single, non-recursive, non-mutual, non-parametric datatype.
      if let some ps := decl.params then
        if !ps.isEmpty then
          throw (IO.userError s!"declareDataType: parametric datatype {nm.toString} unsupported (FFI backend MVP: non-parametric only)")
      let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
      -- Reject self-recursive fields BEFORE building any sort, so a throw cannot
      -- leave a half-populated `sorts` cache (buildSort would otherwise mint an
      -- uninterpreted placeholder for the self-reference).
      for (_, sels) in decl.ctors do
        for (_, st) in selsOf sels do
          if sortMentions nm st then
            throw (IO.userError s!"declareDataType: recursive datatype {nm.toString} unsupported (FFI backend MVP: non-recursive only)")
      let ctorNames  : Array String := decl.ctors.map (fun (cn, _) => cn.toString)
      let recogNames : Array String := decl.ctors.map (fun (cn, _) => s!"is-{cn.toString}")
      let fieldNames : Array (Array String) :=
        decl.ctors.map (fun (_, sels) => (selsOf sels).map (fun (sn, _) => sn.toString))
      let fieldSorts : Array (Array Z3Sort) ←
        decl.ctors.mapM (fun (_, sels) => (selsOf sels).mapM (fun (_, se) => buildSort se))
      let (dtSort, decls) ← ctx.mkDatatype nm.toString ctorNames recogNames fieldNames fieldSorts
      modify fun st => { st with sorts := st.sorts.insert nm dtSort }
      -- Walk the flat decl layout `[ctor, recog, acc0, acc1, ...]` per ctor and
      -- register each func_decl under the SmtSymbol the translator references:
      -- constructor = the ctor symbol; recognizer = `is-<ctor>` (mkCtorTestorTerm);
      -- accessor = the selector symbol (mkCtorSelectorSymbol). `decls[k]?` avoids
      -- the missing `Inhabited FuncDecl`.
      let mut k := 0
      for (cn, sels) in decl.ctors do
        let some ctorFd := decls[k]? | throw (IO.userError "declareDataType: decl layout mismatch (ctor)")
        k := k + 1
        let some recogFd := decls[k]? | throw (IO.userError "declareDataType: decl layout mismatch (recog)")
        k := k + 1
        modify fun st => { st with funcs := st.funcs.insert cn ctorFd }
        modify fun st => { st with funcs := st.funcs.insert (.NormalSymbol s!"is-{cn.toString}") recogFd }
        for (sn, _) in selsOf sels do
          let some accFd := decls[k]? | throw (IO.userError "declareDataType: decl layout mismatch (accessor)")
          k := k + 1
          modify fun st => { st with funcs := st.funcs.insert sn accFd }
  | .declareMutualDataTypes _ _ =>
      throw (IO.userError "declareMutualDataTypes: FFI backend does not yet support mutual datatypes")
  | .defineFun isRec nm params rt body =>
      if isRec || bodyReferences nm body then
        -- recursive: declare a rec func decl, register it (so the body's self-
        -- reference resolves via recFuncs), then bind the params as fresh consts
        -- and add the definition using those consts as the formal arguments.
        let ds ← params.mapM (fun (_, se) => buildSort se)
        let r ← buildSort rt
        let fd ← ctx.mkRecFuncDecl nm.toString ds r
        modify fun st => { st with recFuncs := st.recFuncs.insert nm fd }
        let (bodyAst, consts) ← withBound params (buildTerm body)
        ctx.addRecDef fd consts bodyAst
      else
        -- non-recursive: register as an inlinable macro (expanded at apply sites).
        modify fun st => { st with macros := st.macros.insert nm { params := params.map (·.1), body } }
  | .defineFunsRec decls bodies =>
      -- mutual recursion: FIRST declare + register every rec func decl (so cross-
      -- references between the group's bodies resolve via recFuncs), THEN bind
      -- each one's params and add its definition.
      if decls.size != bodies.size then
        throw (IO.userError s!"defineFunsRec: {decls.size} decls ≠ {bodies.size} bodies")
      for decl in decls do
        let ds ← decl.params.mapM (fun (_, se) => buildSort se)
        let r ← buildSort decl.ret
        let fd ← ctx.mkRecFuncDecl decl.name.toString ds r
        modify fun st => { st with recFuncs := st.recFuncs.insert decl.name fd }
      for h : i in [:decls.size] do
        let decl := decls[i]
        let some body := bodies[i]? | throw (IO.userError "defineFunsRec: body index out of range")
        let some fd := (← get).recFuncs.get? decl.name
          | throw (IO.userError s!"defineFunsRec: missing rec func decl for {decl.name.toString}")
        let (bodyAst, consts) ← withBound decl.params (buildTerm body)
        ctx.addRecDef fd consts bodyAst
  | .defineSort nm args body =>
      -- Sort alias. Only nullary aliases are supported (parametric aliases would
      -- need to substitute the params into `body` at each use site). Register the
      -- resolved sort under `nm` so `buildSort (.SymbolSort nm)` finds it. Note
      -- `Nat`/`Prop` are `ReservedSymbol`s that `buildSort` special-cases before
      -- consulting `sorts`, so their aliases (from defineNat/PropSort) are harmless
      -- no-ops; a `NormalSymbol` alias is what actually exercises this path.
      match args with
      | none => let s ← buildSort body; modify fun st => { st with sorts := st.sorts.insert nm s }
      | some ps =>
          if ps.isEmpty then
            let s ← buildSort body; modify fun st => { st with sorts := st.sorts.insert nm s }
          else
            throw (IO.userError s!"defineSort: parametric alias {nm.toString} unsupported")
  | _ => throw (IO.userError s!"runCommand: unhandled command (later tasks)")

end Blaster.Smt.FFI
