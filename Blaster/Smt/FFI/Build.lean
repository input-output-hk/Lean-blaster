import Blaster.Smt.FFI.Sorts
import Blaster.Smt.FFI.Terms
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

partial def inlineMacro (_m : MacroDef) (_args : Array SmtTerm) : BuildM Ast :=
  throw (IO.userError "inlineMacro: implemented in a later task")

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
  | _ => throw (IO.userError s!"runCommand: unhandled command (later tasks)")

end Blaster.Smt.FFI
