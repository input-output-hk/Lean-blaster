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
  | .IndexSort (.ReservedSymbol "BitVec") #[.NumeralIndex n] => ctx.mkBvSort n
  | .IndexSort .. => throw (IO.userError s!"buildSort: unsupported indexed sort {se}")
  | .SymbolSort nm =>
      match nm with
      | .ReservedSymbol "Int"    => ctx.mkIntSort
      | .ReservedSymbol "Real"   => ctx.mkRealSort
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
  | .ParamSort nm args =>
      -- A registered PARAMETRIC datatype instantiated at concrete `args` (e.g.
      -- `(@List Int)`): build the arg sorts and instantiate via `Z3_mk_datatype_sort`.
      -- This MUST precede the `sorts.get?` lookup, which would otherwise hand back the
      -- UNINSTANTIATED polymorphic sort (a silent wrong-sort bug).
      if (← get).paramDatatypes.contains nm then
        if let some s := (← get).instSortCache.get? se then return s
        let argSorts ← args.mapM buildSort
        let s ← ctx.mkDatatypeSort nm.toString argSorts
        modify fun st => { st with instSortCache := st.instSortCache.insert se s }
        return s
      match (← get).sorts.get? nm with
      | some s => return s
      | none => throw (IO.userError s!"buildSort: unknown parameterized sort {nm.toString}")

/-- Does `se` mention the sort symbol `target` anywhere? Used to reject
    (MVP: non-recursive datatypes only) self-recursive datatype fields with a
    clear error instead of silently minting an uninterpreted placeholder sort. -/
partial def sortMentions (target : SmtSymbol) : SortExpr → Bool
  | .SymbolSort s   => s == target
  | .IndexSort s ps => s == target || ps.any (fun i => match i with | .SymbolIndex x => x == target | _ => false)
  | .ParamSort s ps => s == target || ps.any (sortMentions target)

/-- For a datatype field of sort `se`, in a group whose datatype sort names are
    `group`, return the Z3 field sort paired with its Z3 `sort_ref`:
    * `0` — a normal field; the returned sort (built via `buildSort`) is the field's
      real sort.
    * `k+1` — a self/mutual reference to the k-th datatype in `group` (a direct
      `.SymbolSort s` with `s == group[k]`). Z3 IGNORES the paired sort in this
      case, so we hand it a Bool placeholder rather than trying to `buildSort` the
      not-yet-declared datatype name (which would mint a bogus uninterpreted sort).
    A recursive reference nested inside a PARAMETERIZED sort (e.g. `List T` where
    `T` is in the group) needs parametric datatype support and is rejected here. -/
def buildFieldSortRef (group : Array SmtSymbol) (se : SortExpr) :
    BuildM (Z3Sort × UInt32) := do
  let ctx := (← get).ctx
  match se with
  | .SymbolSort s =>
      match (List.range group.size).find? (fun i => group[i]? == some s) with
      | some k => return (← ctx.mkBoolSort, UInt32.ofNat (k + 1))
      | none   => return (← buildSort se, 0)
  | .IndexSort .. => return (← buildSort se, 0)
  | _ =>
      if group.any (fun g => sortMentions g se) then
        throw (IO.userError s!"FFI datatype: recursive field inside a parameterized \
          sort {se} unsupported (parametric datatypes pending, next task)")
      else return (← buildSort se, 0)

/-- Build the Z3 field sort for an arbitrarily-NESTED field of a PARAMETRIC datatype
    whose type parameters are mapped to Z3 type variables in `tvMap`, given the set of
    datatype names `group` declared TOGETHER (`#[nm]` for a single datatype; all member
    names for a mutual group). Handles a type parameter appearing UNDER another type
    constructor (`Option α`, `List (Term α)`):
    * `.SymbolSort p`, `p ∈ tvMap` → its Z3 type variable (so Z3 sees `@α` as the
      datatype's own parameter); any other `.SymbolSort` (Int/Bool/String/declared
      sort) → `buildSort`.
    * `.ParamSort head args` where `head ∈ group` (a SELF or SIBLING forward-reference —
      e.g. the `@Term` inside `(@List (@Term @α))` while the group is still being
      declared) OR an already-declared parametric datatype (`@List`, `@Option`) →
      recursively build the arg sorts and instantiate / forward-ref via
      `Z3_mk_datatype_sort` (dual-purpose: instantiation AND forward reference; a
      not-yet-declared group sibling resolves when its own `mkPolyDatatype` runs).
    * any other `.ParamSort head args` (`head` is NOT a datatype — an uninterpreted
      arity-n sort like `@@ArrowT2`, or `Array`) → `buildSort` on the whole sort:
      `Array` is resolved structurally; an uninterpreted parameterized sort collapses
      to its declared sort (its type args are ignored, as the FFI does elsewhere). A
      parametric datatype declared only LATER (outside `group`) falls through to
      `buildSort`'s generic "unknown parameterized sort" error.
    The result is always a REAL sort, used with `sort_ref 0` (never NULL). -/
partial def buildParamFieldSort (group : Array SmtSymbol) (tvMap : Std.HashMap SmtSymbol Z3Sort)
    (se : SortExpr) : BuildM Z3Sort := do
  match se with
  | .SymbolSort p =>
      match tvMap.get? p with
      | some tv => return tv
      | none    =>
          if group.contains p then (← get).ctx.mkDatatypeSort p.toString #[]
          else buildSort (.SymbolSort p)
  | .IndexSort .. => buildSort se
  | .ParamSort head args =>
      let isDatatype := (← get).paramDatatypes.contains head
      if group.contains head || isDatatype then
        let argSorts ← args.mapM (buildParamFieldSort group tvMap)
        (← get).ctx.mkDatatypeSort head.toString argSorts
      else
        buildSort se

/-- Is `se` a REGULAR (direct) self-reference of datatype `nm` — i.e. `nm` applied to
    exactly its own type parameters `params`, in order (`(@Term @α)` for `@Term` with
    param `@α`)? Such a TOP-LEVEL field uses Z3's NULL + `sort_ref` convention; every
    other occurrence of `nm` (nested under a constructor, or at different args) is a
    forward reference built through `buildParamFieldSort`. -/
def isRegularSelfRef (nm : SmtSymbol) (params : Array SmtSymbol) (se : SortExpr) : Bool :=
  se == .ParamSort nm (params.map .SymbolSort)

/-- Field-sort resolution for a member `nm` (type params `params`, each mapped to its Z3
    type variable in `tvMap`) of the PARAMETRIC datatype `group` declared together
    (`#[nm]` for a single datatype; all member names for a mutual group). Returns the Z3
    field sort paired with its Z3 `sort_ref` (same convention as `buildFieldSortRef`):
    * a param field `.SymbolSort p` with `p ∈ params` → the type var, ref `0`;
    * a REGULAR self-recursive field `(@nm @α …)` — `nm` (the CURRENT member) applied to its
      OWN params — → `placeholder`, ref `1` (Z3 IGNORES the sort when ref>0 and keys
      recursion off a NULL `sorts[]` slot; sort_ref 0 selects the sole datatype in `nm`'s
      own `mkPolyDatatype` call, i.e. `nm` itself; the placeholder is never read). A SIBLING
      reference is never a regular self ref (`isRegularSelfRef` keys on `nm`), so it falls to
      the forward-ref case below;
    * any NESTED occurrence — a type parameter under another constructor (`(@Option @α)`,
      `(@List (@Term @α))`), a self/sibling nested under another constructor, a top-level
      sibling `(@B @α)`, or a nested-at-concrete (`(@List String)`) — → a REAL
      forward-ref/instantiated sort built via `buildParamFieldSort`, ref `0`;
    * any other CONCRETE field sort (`Int`, `Bool`, an already-declared sort) → built via
      `buildSort`, ref `0`. -/
def buildParamFieldSortRef (group : Array SmtSymbol) (nm : SmtSymbol) (params : Array SmtSymbol)
    (tvMap : Std.HashMap SmtSymbol Z3Sort) (placeholder : Z3Sort) (se : SortExpr) :
    BuildM (Z3Sort × UInt32) := do
  match se with
  | .SymbolSort p =>
      match tvMap.get? p with
      | some tv => return (tv, 0)
      | none    =>
          if group.contains p then
            if p == nm then return (placeholder, 1)
            else return (← (← get).ctx.mkDatatypeSort p.toString #[], 0)
          else return (← buildSort se, 0)
  | .IndexSort .. => return (← buildSort se, 0)
  | .ParamSort _ _ =>
      if isRegularSelfRef nm params se then return (placeholder, 1)
      else return (← buildParamFieldSort group tvMap se, 0)

/-- Strip the surrounding quotes strLitSmt adds to string literals. -/
private def unquote (s : String) : String :=
  if s.length ≥ 2 && s.front == '"' && s.back == '"' then (s.drop 1).dropRight 1 else s

private def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ '0'.toNat && n ≤ '9'.toNat then some (n - '0'.toNat)
  else if n ≥ 'a'.toNat && n ≤ 'f'.toNat then some (n - 'a'.toNat + 10)
  else if n ≥ 'A'.toNat && n ≤ 'F'.toNat then some (n - 'A'.toNat + 10)
  else none

private def parseRadix? (base : Nat) (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc c => do
    let d ← hexDigit? c
    if d < base then some (acc * base + d) else none) 0

/-- Collect pattern terms from a quantifier's annotations. -/
private def patternsOf (annot : Array SmtAttribute) : Array SmtTerm :=
  annot.foldl (fun acc a => match a with | .Pattern ps => acc ++ ps | _ => acc) #[]

private def qidOf (annot : Array SmtAttribute) : String :=
  (annot.findSome? fun a => match a with | .Qid nm => some nm.toString | _ => none).getD ""

mutual
/-- Translate an `SmtTerm` directly to a Z3 AST. -/
partial def buildTerm (t : SmtTerm) : BuildM Ast := do
  let ctx := (← get).ctx
  match t with
  | .NumTerm n  => ctx.mkNumeral (toString n) (← ctx.mkIntSort)
  | .DecTerm n  => ctx.mkNumeral n (← ctx.mkRealSort)
  | .BoolTerm b => ctx.mkBool b
  | .BinTerm v =>
      let digits := v.toList.drop 2
      let some n := (if v.startsWith "#b" && !digits.isEmpty then parseRadix? 2 digits else none)
        | throw (IO.userError s!"invalid binary BitVec literal {v}")
      ctx.mkNumeral (toString n) (← ctx.mkBvSort (UInt32.ofNat digits.length))
  | .HexTerm v =>
      let digits := v.toList.drop 2
      let some n := (if v.startsWith "#x" && !digits.isEmpty then parseRadix? 16 digits else none)
        | throw (IO.userError s!"invalid hexadecimal BitVec literal {v}")
      ctx.mkNumeral (toString n) (← ctx.mkBvSort (UInt32.ofNat (4 * digits.length)))
  | .StrTerm s  => ctx.mkSmtStringLit (unquote s)
  | .SmtIdent nm => buildIdent nm
  | .AppTerm nm args => buildApp nm args
  | .ForallTerm bs body => buildQuant true bs body
  | .ExistsTerm bs body => buildQuant false bs body
  | .LambdaTerm bs body => do
      let (b, consts) ← withBound bs (buildTerm body)
      (← get).ctx.mkLambdaConst consts b
  | .AnnotatedTerm t annot =>
      match t with
      | .ForallTerm bs body => buildQuant true bs body (patternsOf annot) (qidOf annot)
      | .ExistsTerm bs body => buildQuant false bs body (patternsOf annot) (qidOf annot)
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

partial def buildIdent (nm : SmtQualifiedIdent) : BuildM Ast := do
  -- A NULLARY parametric-datatype constructor arrives QUALIFIED with its instantiated
  -- sort: `(as List.nil (@List Int))` = `.SmtIdent (.QualifiedIdent List.nil (@List Int))`.
  -- Resolve it to the monomorphized ctor func_decl and apply with no args. Non-parametric
  -- constructors are NOT in `ctorIndex`, so they fall through to the `funcs` path below.
  if let .QualifiedIdent cn sortExpr := nm then
    if let some (_, ci) := (← get).ctorIndex.get? cn then
      let instSort ← buildSort sortExpr
      let fd ← (← get).ctx.dtConstructor instSort (UInt32.ofNat ci)
      return (← (← get).ctx.mkApp fd #[])
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
  let ctx := (← get).ctx
  let sym := match nm with | .SimpleIdent s => s | .QualifiedIdent s _ => s
  -- Parametric-datatype resolution (checked BEFORE builtins/funcs; the names never
  -- collide, but this keeps the branch order matching the design):
  -- (1) applied constructor `(List.cons x xs)` = `.AppTerm (.QualifiedIdent List.cons (@List Int)) …`
  if let .QualifiedIdent cn sortExpr := nm then
    if let some (_, ci) := (← get).ctorIndex.get? cn then
      let instSort ← buildSort sortExpr
      let fd ← ctx.dtConstructor instSort (UInt32.ofNat ci)
      return (← ctx.mkApp fd (← args.mapM buildTerm))
  -- (2) accessor `(List.cons.0 x)` — the ctor/field indices are fixed; the INSTANTIATED
  --     sort comes from arg0's own sort (`Z3_get_sort`), so the accessor is monomorphized.
  if let some (_, ci, fj) := (← get).accessorIndex.get? sym then
    let argAsts ← args.mapM buildTerm
    let some a0 := argAsts[0]? | throw (IO.userError s!"buildApp: accessor {sym.toString} expects 1 argument")
    let fd ← ctx.dtAccessor (← ctx.astSort a0) (UInt32.ofNat ci) (UInt32.ofNat fj)
    return (← ctx.mkApp fd argAsts)
  -- (3) recognizer `(is-List.cons x)` — same arg-sort-driven monomorphization.
  if let some (_, ci) := (← get).recognizerIndex.get? sym then
    let argAsts ← args.mapM buildTerm
    let some a0 := argAsts[0]? | throw (IO.userError s!"buildApp: recognizer {sym.toString} expects 1 argument")
    let fd ← ctx.dtRecognizer (← ctx.astSort a0) (UInt32.ofNat ci)
    return (← ctx.mkApp fd argAsts)
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
  | .ReservedSymbol "str.replace_all", [a, b, c] => return some (← ctx.mkStrReplaceAll a b c)
  -- bit-vectors
  | .ReservedSymbol "bvadd", [a, b]  => return some (← ctx.mkBvAdd a b)
  | .ReservedSymbol "bvsub", [a, b]  => return some (← ctx.mkBvSub a b)
  | .ReservedSymbol "bvmul", [a, b]  => return some (← ctx.mkBvMul a b)
  | .ReservedSymbol "bvudiv", [a, b] => return some (← ctx.mkBvUDiv a b)
  | .ReservedSymbol "bvsdiv", [a, b] => return some (← ctx.mkBvSDiv a b)
  | .ReservedSymbol "bvurem", [a, b] => return some (← ctx.mkBvURem a b)
  | .ReservedSymbol "bvsrem", [a, b] => return some (← ctx.mkBvSRem a b)
  | .ReservedSymbol "bvsmod", [a, b] => return some (← ctx.mkBvSMod a b)
  | .ReservedSymbol "bvshl", [a, b]  => return some (← ctx.mkBvShl a b)
  | .ReservedSymbol "bvlshr", [a, b] => return some (← ctx.mkBvLShr a b)
  | .ReservedSymbol "bvashr", [a, b] => return some (← ctx.mkBvAShr a b)
  | .ReservedSymbol "bvor", [a, b]   => return some (← ctx.mkBvOr a b)
  | .ReservedSymbol "bvand", [a, b]  => return some (← ctx.mkBvAnd a b)
  | .ReservedSymbol "bvnand", [a, b] => return some (← ctx.mkBvNand a b)
  | .ReservedSymbol "bvnor", [a, b]  => return some (← ctx.mkBvNor a b)
  | .ReservedSymbol "bvxnor", [a, b] => return some (← ctx.mkBvXnor a b)
  | .ReservedSymbol "concat", [a, b] => return some (← ctx.mkBvConcat a b)
  | .ReservedSymbol "bvule", [a, b]  => return some (← ctx.mkBvULe a b)
  | .ReservedSymbol "bvult", [a, b]  => return some (← ctx.mkBvULt a b)
  | .ReservedSymbol "bvuge", [a, b]  => return some (← ctx.mkBvUGe a b)
  | .ReservedSymbol "bvugt", [a, b]  => return some (← ctx.mkBvUGt a b)
  | .ReservedSymbol "bvsle", [a, b]  => return some (← ctx.mkBvSLe a b)
  | .ReservedSymbol "bvslt", [a, b]  => return some (← ctx.mkBvSLt a b)
  | .ReservedSymbol "bvsge", [a, b]  => return some (← ctx.mkBvSGe a b)
  | .ReservedSymbol "bvsgt", [a, b]  => return some (← ctx.mkBvSGt a b)
  | .ReservedSymbol "bvneg", [a]    => return some (← ctx.mkBvNeg a)
  | .ReservedSymbol "bvnot", [a]    => return some (← ctx.mkBvNot a)
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
    (pats : Array SmtTerm := #[]) (qid : String := "") : BuildM Ast := do
  -- The SMT-LIB emitter places :pattern on the quantifier body.
  -- Z3_mk_quantifier_const_ex takes patterns and qid as separate arguments.
  let (body, bodyPats, bodyQid) := match body with
    | .AnnotatedTerm inner attrs => (inner, patternsOf attrs, qidOf attrs)
    | inner => (inner, #[], "")
  let ((b, patAsts), consts) ← withBound bs (do
    let b ← buildTerm body
    let patAsts ← (pats ++ bodyPats).mapM buildTerm
    return (b, patAsts))
  -- SMT-LIB quantifiers without :weight receive Z3's default weight 1.
  (← get).ctx.mkQuantConst isForall 1 (if bodyQid.isEmpty then qid else bodyQid) consts patAsts b
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

/-- Register the NAME→index metadata for a PARAMETRIC datatype `nm` with `nparams` type
    params, given its `decl`. The datatype's sort has already been built in the manager
    NATIVELY (`Z3_mk_polymorphic_datatype`, via `mkPolyDatatype`); this only records the
    template + the ctor/accessor/recognizer resolution indices so `buildSort (@nm …)` (via
    `mkDatatypeSort`, resolving by name) and use-site resolution in `buildApp`/`buildIdent`
    work. Pure state mutation — no Z3 call — so callers may run it after their last Z3 API
    call without disturbing `errorCode`. Shared by the single (`declareParamDatatype`) and
    mutual parametric paths. `polySort` is `none` (the field is dead — never read). -/
def registerParamDatatypeTemplate (nm : SmtSymbol) (nparams : Nat) (recursive : Bool)
    (decl : SmtDatatypeDecl) : BuildM Unit := do
  let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
  let ctorSyms      : Array SmtSymbol := decl.ctors.map (·.1)
  let accessorNames : Array (Array SmtSymbol) :=
    decl.ctors.map (fun (_, sels) => (selsOf sels).map (·.1))
  let template : ParamDatatype :=
    { name := nm, polySort := none, nparams, recursive, ctorNames := ctorSyms, accessorNames }
  modify fun st => { st with paramDatatypes := st.paramDatatypes.insert nm template }
  for h : ci in [:decl.ctors.size] do
    let (cn, sels) := decl.ctors[ci]
    modify fun st => { st with
      ctorIndex       := st.ctorIndex.insert cn (nm, ci),
      recognizerIndex := st.recognizerIndex.insert (.NormalSymbol s!"is-{cn.toString}") (nm, ci) }
    let sels' := selsOf sels
    for h : fj in [:sels'.size] do
      let (sn, _) := sels'[fj]
      modify fun st => { st with accessorIndex := st.accessorIndex.insert sn (nm, ci, fj) }

/-- Register a NON-parametric (arity-0) datatype `nm` that is a member of a MIXED mutual
    group (some members parametric, some not) already declared NATIVELY (via
    `mkPolyDatatype` with zero type vars). Its use sites resolve through `funcs`/`sorts`
    (via `SimpleIdent`), NOT `ctorIndex`, so recover the sort and each ctor/recognizer/
    accessor func_decl BY NAME (`mkDatatypeSort nm #[]` + the `dt*` queries) and register
    them exactly as the native non-parametric paths do. NOTE: this issues Z3 API calls, so
    callers that read `errorCode` right after the group's declaration must not route a
    member here between the last `mkPolyDatatype` and that read (no test exercises the
    mixed case, so this is defensive only). -/
def registerParserDatatypeFuncs (nm : SmtSymbol) (decl : SmtDatatypeDecl) : BuildM Unit := do
  let ctx := (← get).ctx
  let dtSort ← ctx.mkDatatypeSort nm.toString #[]
  modify fun st => { st with sorts := st.sorts.insert nm dtSort }
  let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
  for h : ci in [:decl.ctors.size] do
    let (cn, sels) := decl.ctors[ci]
    let ctorFd  ← ctx.dtConstructor dtSort (UInt32.ofNat ci)
    let recogFd ← ctx.dtRecognizer  dtSort (UInt32.ofNat ci)
    modify fun st => { st with funcs := st.funcs.insert cn ctorFd }
    modify fun st => { st with funcs := st.funcs.insert (.NormalSymbol s!"is-{cn.toString}") recogFd }
    let sels' := selsOf sels
    for h : fj in [:sels'.size] do
      let (sn, _) := sels'[fj]
      let accFd ← ctx.dtAccessor dtSort (UInt32.ofNat ci) (UInt32.ofNat fj)
      modify fun st => { st with funcs := st.funcs.insert sn accFd }

/-- Does datatype `decl` mention any of `names` (its own name and/or its group siblings) in a
    field sort? Determines (self- or mutual-) recursiveness for wrapper classification. -/
def declMentionsAny (names : Array SmtSymbol) (decl : SmtDatatypeDecl) : Bool :=
  decl.ctors.any (fun (_, sels) =>
    (sels.getD #[]).any (fun (_, se) => names.any (fun n => sortMentions n se)))

/-- Head symbol of a sort expression. -/
def sortHead : SortExpr → SmtSymbol
  | .SymbolSort s  => s
  | .IndexSort s _ => s
  | .ParamSort s _ => s

/-- Is `d` an UNSAFE wrapper — a datatype that is NON-recursive with ≥2 constructors — per the
    snapshot `wrapperInfo` (`name ↦ (recursive, ctorCount)`, covering the current group's members
    and every already-declared parametric datatype)? Instantiating such a datatype at a BARE
    forward-ref sibling segfaults Z3 (its `Z3_mk_datatype_sort` forward-ref contract covers only
    recursive datatypes and array-range / sequence-element nesting), so a member wrapping a sibling
    directly in one must be declared AFTER that sibling. A name absent from `wrapperInfo` is a
    builtin or uninterpreted sort (`@@ArrowT2`, `Array`) — NOT a datatype wrapper. -/
def isUnsafeWrapper (wrapperInfo : Std.HashMap SmtSymbol (Bool × Nat)) (d : SmtSymbol) : Bool :=
  match wrapperInfo.get? d with
  | some (rec, nc) => !rec && nc ≥ 2
  | none           => false

/-- Precedence edges `(before, after)` forced by a field sort `se` of member `X`: for each
    `.ParamSort d dargs` where `d` is an unsafe wrapper, a DIRECT argument whose head is a group
    member `Y` forces `Y` before `X` (Z3 must see a REAL `Y`, not a forward-ref, to instantiate
    `d Y`); and if the unsafe wrapper `d` is itself a group sibling, it too must precede `X`. A
    sibling reference nested under a SAFE (recursive) wrapper — `d (List (Y …))` — imposes nothing
    (probe-verified), so only direct arguments are scanned. `Y == X` yields a self edge → later
    flagged as an unresolvable cycle. -/
partial def scanPrecede (group : Array SmtSymbol) (wrapperInfo : Std.HashMap SmtSymbol (Bool × Nat))
    (X : SmtSymbol) : SortExpr → Array (SmtSymbol × SmtSymbol)
  | .SymbolSort _     => #[]
  | .IndexSort _ _    => #[]
  | .ParamSort d dargs =>
      let sub := dargs.foldl (fun acc a => acc ++ scanPrecede group wrapperInfo X a) #[]
      if isUnsafeWrapper wrapperInfo d then
        let direct := dargs.filterMap (fun a =>
          let h := sortHead a
          if group.contains h then some (h, X) else none)
        let dEdge := if group.contains d && d != X then #[(d, X)] else #[]
        sub ++ direct ++ dEdge
      else sub

/-- A stable topological order of `group` satisfying the precedence edges `(before, after)`:
    a member is emitted only once every member that must precede it has been emitted, and among
    otherwise-free members the original order is kept (so a group with no unsafe-wrapper constraint
    declares in the emitter's order — the native forward-ref path, unchanged). Throws (naming the
    members) on a cycle, including a self edge `(X, X)` — a member that wraps a sibling or itself
    directly in an unsafe wrapper along a cycle has NO valid order, and Z3 would segfault. -/
def mutualDeclOrder (group : Array SmtSymbol) (edges : Array (SmtSymbol × SmtSymbol)) :
    BuildM (Array SmtSymbol) := do
  if let some (b, _) := edges.find? (fun (b, a) => b == a) then
    throw (IO.userError s!"declareMutualDataTypes: {b.toString} wraps itself directly in a \
      non-recursive multi-constructor datatype — Z3 cannot forward-reference it (no valid order)")
  let mut remaining := group
  let mut result : Array SmtSymbol := #[]
  for _ in [:group.size] do
    match remaining.find? (fun m => !(edges.any (fun (b, a) => a == m && remaining.contains b))) with
    | some m => result := result.push m; remaining := remaining.filter (· != m)
    | none   =>
        throw (IO.userError s!"declareMutualDataTypes: cyclic unsafe-wrapper dependency among \
          {remaining.map (·.toString)} — members mutually wrap each other directly in \
          non-recursive multi-constructor datatypes, which Z3 cannot forward-reference")
  return result

/-- Declare a SINGLE PARAMETRIC datatype (`decl.params = some ps`, `ps` non-empty)
    NATIVELY via `Z3_mk_polymorphic_datatype` (`mkPolyDatatype`) — no SMT-LIB parser. One
    Z3 type variable per param (`mkTypeVar`, mapped by param symbol); each field's sort +
    `sort_ref` is resolved by `buildParamFieldSortRef` (param → type var; regular self-ref →
    NULL + ref 1; nested self / declared-datatype instantiation / forward-ref →
    `Z3_mk_datatype_sort`; uninterpreted `@@ArrowT2`/`Array` → `buildSort` collapse). The
    instantiated (monomorphized) func_decls are recovered on demand at use sites via the
    `dt*` calls, keyed by name. Register the template AFTER the Z3 call succeeds (no
    half-populated registry); `group = #[nm]` (a single datatype is its own only sibling). -/
def declareParamDatatype (nm : SmtSymbol) (ps : Array SmtSymbol)
    (decl : SmtDatatypeDecl) : BuildM Unit := do
  let ctx := (← get).ctx
  -- 1. one Z3 type variable per param, mapped by param symbol
  let tvs ← ps.mapM (fun p => ctx.mkTypeVar p.toString)
  let mut tvMap : Std.HashMap SmtSymbol Z3Sort := {}
  for (p, tv) in ps.zip tvs do
    tvMap := tvMap.insert p tv
  let placeholder ← ctx.mkBoolSort   -- never-read filler for recursive field slots (ref>0)
  let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
  let ctorNames  : Array String := decl.ctors.map (fun (cn, _) => cn.toString)
  let recogNames : Array String := decl.ctors.map (fun (cn, _) => s!"is-{cn.toString}")
  let fieldNames : Array (Array String) :=
    decl.ctors.map (fun (_, sels) => (selsOf sels).map (fun (sn, _) => sn.toString))
  -- 2. per ctor / per field: (Z3 field sort, sort_ref); group is just this datatype
  let fieldData : Array (Array (Z3Sort × UInt32)) ←
    decl.ctors.mapM (fun (_, sels) =>
      (selsOf sels).mapM (fun (_, se) => buildParamFieldSortRef #[nm] nm ps tvMap placeholder se))
  let fieldSorts : Array (Array Z3Sort) := fieldData.map (·.map (·.1))
  let fieldRefs  : Array (Array UInt32) := fieldData.map (·.map (·.2))
  -- 3. declare the polymorphic datatype (the returned poly sort is unused — polySort is dead)
  let _ ← ctx.mkPolyDatatype nm.toString tvs ctorNames recogNames fieldNames fieldSorts fieldRefs
  -- 4. register the template + resolution indices (AFTER the Z3 call succeeds); `recursive` is
  --    whether any field mentions `nm` (self-recursion) — used to classify `nm` as a field wrapper.
  registerParamDatatypeTemplate nm ps.size (declMentionsAny #[nm] decl) decl

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
      -- Parametric datatype (`@List α`, `@Either α β`): handled via
      -- `Z3_mk_polymorphic_datatype`; instantiated func_decls resolved at use sites.
      if let some ps := decl.params then
        if !ps.isEmpty then
          declareParamDatatype nm ps decl
          return
      -- A non-parametric recursive datatype may occur underneath an already
      -- declared parametric datatype (for example `List Data`). Z3's ordinary
      -- `mk_datatype` field refs only express direct recursion. Declare this
      -- case through the native polymorphic datatype API with zero parameters,
      -- which can resolve a forward reference nested in a recursive wrapper.
      let hasNestedRec := decl.ctors.any fun (_, sels) =>
        (sels.getD #[]).any fun (_, se) =>
          match se with
          | .ParamSort .. => sortMentions nm se
          | _ => false
      if hasNestedRec then
        let placeholder ← ctx.mkBoolSort
        let ctorNames := decl.ctors.map (fun (cn, _) => cn.toString)
        let recogNames := decl.ctors.map (fun (cn, _) => s!"is-{cn.toString}")
        let fieldNames := decl.ctors.map (fun (_, sels) =>
          (sels.getD #[]).map (fun (sn, _) => sn.toString))
        let fieldData ← decl.ctors.mapM (fun (_, sels) =>
          (sels.getD #[]).mapM (fun (_, se) =>
            buildParamFieldSortRef #[nm] nm #[] {} placeholder se))
        let fieldSorts := fieldData.map (·.map (·.1))
        let fieldRefs := fieldData.map (·.map (·.2))
        let _ ← ctx.mkPolyDatatype nm.toString #[] ctorNames recogNames
          fieldNames fieldSorts fieldRefs
        registerParserDatatypeFuncs nm decl
        return
      -- Single datatype: non-recursive OR (self-)recursive, non-parametric.
      let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
      let ctorNames  : Array String := decl.ctors.map (fun (cn, _) => cn.toString)
      let recogNames : Array String := decl.ctors.map (fun (cn, _) => s!"is-{cn.toString}")
      let fieldNames : Array (Array String) :=
        decl.ctors.map (fun (_, sels) => (selsOf sels).map (fun (sn, _) => sn.toString))
      -- Per field: (Z3 sort, sort_ref). A direct `.SymbolSort nm` self-reference
      -- gets ref=1 with a Bool placeholder sort (Z3 ignores it); all other fields
      -- get ref=0 and their real built sort. `buildFieldSortRef` rejects recursion
      -- nested inside a parameterized sort (needs parametric support).
      let fieldData : Array (Array (Z3Sort × UInt32)) ←
        decl.ctors.mapM (fun (_, sels) =>
          (selsOf sels).mapM (fun (_, se) => buildFieldSortRef #[nm] se))
      let fieldSorts : Array (Array Z3Sort) := fieldData.map (·.map (·.1))
      let fieldRefs  : Array (Array UInt32) := fieldData.map (·.map (·.2))
      let isRec := fieldRefs.any (·.any (· != 0))
      let (dtSort, decls) ←
        if isRec then
          ctx.mkDatatypeRec nm.toString ctorNames recogNames fieldNames fieldSorts fieldRefs
        else
          ctx.mkDatatype nm.toString ctorNames recogNames fieldNames fieldSorts
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
  | .declareMutualDataTypes nms decls => do
      -- A mutually-recursive datatype group. The parametric signal lives in BOTH the sort
      -- decls' `arity` and each datatype decl's `params`.
      if nms.size != decls.size then
        throw (IO.userError s!"declareMutualDataTypes: {nms.size} sort decls ≠ {decls.size} datatype decls")
      let selsOf := fun (sels : Option (Array SmtSelector)) => sels.getD #[]
      let isParam := nms.any (·.arity != 0) || decls.any (fun d => !(d.params.getD #[]).isEmpty)
      if isParam then
        -- PARAMETRIC (or MIXED parametric/non-parametric) mutual group, declared NATIVELY:
        -- each member gets its own `Z3_mk_polymorphic_datatype` (`mkPolyDatatype`) call, and a
        -- reference to a group SIBLING becomes a `Z3_mk_datatype_sort(sibling, [args])` FORWARD REF
        -- (real sort, `sort_ref 0`) that Z3 resolves when that sibling's own `mkPolyDatatype` runs.
        -- No SMT-LIB parser is involved, so everything lives in ONE manager name space — the
        -- uninterpreted `@@ArrowT2` and earlier single parametric datatypes (`@List`/`@Option`/…)
        -- are visible to the group (what the parser route could NOT do — the DT-8 regression).
        --
        -- One Z3 limitation the probe missed: `Z3_mk_datatype_sort`'s forward-ref contract covers
        -- only RECURSIVE datatypes (and array-range / sequence-element nesting), so instantiating a
        -- NON-recursive multi-constructor datatype (`Option`/`Except`) DIRECTLY at a bare forward-ref
        -- sibling SEGFAULTS. We avoid it by DECLARATION ORDER: a member that wraps a sibling directly
        -- in such an "unsafe wrapper" is declared AFTER that sibling (so the sibling is a REAL sort,
        -- not a forward-ref). `mutualDeclOrder` computes this; an unbreakable cycle throws.
        --
        -- Validate arity ↔ params BEFORE any Z3 call; register AFTER all declarations succeed (no
        -- half-populated registry), and do NOT emit a Z3 call between the last `mkPolyDatatype` and
        -- the caller's `errorCode` read — `registerParamDatatypeTemplate` (pure) is used per member.
        for h : i in [:decls.size] do
          let np := (decls[i].params.getD #[]).size
          let some sd := nms[i]? | throw (IO.userError "declareMutualDataTypes: sort/decl count mismatch")
          if sd.arity != np then
            throw (IO.userError s!"declareMutualDataTypes: sort decl arity {sd.arity} ≠ \
              datatype params {np} for {sd.name.toString}")
        let group : Array SmtSymbol := nms.map (·.name)
        -- Wrapper snapshot: every already-declared parametric datatype + this group's members
        -- (a member is recursive iff it mentions itself OR any sibling — mutual recursion is safe).
        let mut wrapperInfo : Std.HashMap SmtSymbol (Bool × Nat) :=
          (← get).paramDatatypes.fold
            (fun acc nm t => acc.insert nm (t.recursive, t.ctorNames.size)) {}
        for h : i in [:decls.size] do
          let some sd := nms[i]? | throw (IO.userError "declareMutualDataTypes: sort/decl count mismatch")
          wrapperInfo := wrapperInfo.insert sd.name (declMentionsAny group decls[i], decls[i].ctors.size)
        -- Precedence edges from every member's field sorts, then a safe declaration order.
        let mut edges : Array (SmtSymbol × SmtSymbol) := #[]
        for h : i in [:decls.size] do
          let some sd := nms[i]? | throw (IO.userError "declareMutualDataTypes: sort/decl count mismatch")
          for (_, sels) in decls[i].ctors do
            for (_, se) in selsOf sels do
              edges := edges ++ scanPrecede group wrapperInfo sd.name se
        let order ← mutualDeclOrder group edges
        let mut nameToIdx : Std.HashMap SmtSymbol Nat := {}
        for h : i in [:decls.size] do
          let some sd := nms[i]? | throw (IO.userError "declareMutualDataTypes: sort/decl count mismatch")
          nameToIdx := nameToIdx.insert sd.name i
        let placeholder ← ctx.mkBoolSort   -- never-read filler for regular self-ref slots (ref 1)
        -- Shared param-name → Z3 type-var cache: same-named params across members (all groups
        -- here name their param `@α`) share ONE interned type var, matching the probe.
        let mut tvCache : Std.HashMap SmtSymbol Z3Sort := {}
        -- Declare each member in the SAFE order (a forward-ref to a LATER sibling is fine; an unsafe
        -- wrapper of a sibling never occurs because that sibling was ordered earlier and is REAL).
        for nm in order do
          let some idx := nameToIdx.get? nm | throw (IO.userError "declareMutualDataTypes: order/name mismatch")
          let some decl := decls[idx]? | throw (IO.userError "declareMutualDataTypes: decl index out of range")
          let ps := decl.params.getD #[]
          let mut tvs : Array Z3Sort := #[]
          for p in ps do
            match tvCache.get? p with
            | some tv => tvs := tvs.push tv
            | none    => let tv ← ctx.mkTypeVar p.toString
                         tvCache := tvCache.insert p tv
                         tvs := tvs.push tv
          let ctorNames  : Array String := decl.ctors.map (fun (cn, _) => cn.toString)
          let recogNames : Array String := decl.ctors.map (fun (cn, _) => s!"is-{cn.toString}")
          let fieldNames : Array (Array String) :=
            decl.ctors.map (fun (_, sels) => (selsOf sels).map (fun (sn, _) => sn.toString))
          -- Per field: (Z3 sort, sort_ref). `group` = all member names, so a self OR sibling
          -- reference resolves via `mkDatatypeSort` (forward-ref, ref 0); a REGULAR self-ref of
          -- THIS member gets NULL + ref 1 (`buildParamFieldSortRef` keys `isRegularSelfRef` on `nm`);
          -- `@@ArrowT2`/`Array` collapse via `buildSort`.
          let fieldData : Array (Array (Z3Sort × UInt32)) ←
            decl.ctors.mapM (fun (_, sels) =>
              (selsOf sels).mapM (fun (_, se) =>
                buildParamFieldSortRef group nm ps tvCache placeholder se))
          let fieldSorts : Array (Array Z3Sort) := fieldData.map (·.map (·.1))
          let fieldRefs  : Array (Array UInt32) := fieldData.map (·.map (·.2))
          let _ ← ctx.mkPolyDatatype nm.toString tvs ctorNames recogNames fieldNames fieldSorts fieldRefs
        -- Register each member (AFTER all Z3 declarations): parametric (arity>0) via the pure
        -- template + ctor/accessor/recognizer indices; a non-parametric (arity 0) member of a
        -- MIXED group via by-name recovery (no test exercises this — see `registerParserDatatypeFuncs`).
        for h : i in [:decls.size] do
          let some sd := nms[i]? | throw (IO.userError "declareMutualDataTypes: sort/decl count mismatch")
          if sd.arity != 0 then
            registerParamDatatypeTemplate sd.name sd.arity (declMentionsAny group decls[i]) decls[i]
          else
            registerParserDatatypeFuncs sd.name decls[i]
      else
        -- Non-parametric mutual group: native `Z3_mk_datatypes`.
        let group : Array SmtSymbol := nms.map (·.name)
        let sortNames  : Array String := group.map (·.toString)
        let ctorNames  : Array (Array String) :=
          decls.map (fun d => d.ctors.map (fun (cn, _) => cn.toString))
        let recogNames : Array (Array String) :=
          decls.map (fun d => d.ctors.map (fun (cn, _) => s!"is-{cn.toString}"))
        let fieldNames : Array (Array (Array String)) :=
          decls.map (fun d => d.ctors.map (fun (_, sels) =>
            (selsOf sels).map (fun (sn, _) => sn.toString)))
        -- Per sort/ctor/field: (Z3 sort, ref). A `.SymbolSort s` naming a group member
        -- → ref = (its group index)+1 with a placeholder sort; otherwise ref=0.
        let fieldData : Array (Array (Array (Z3Sort × UInt32))) ←
          decls.mapM (fun d => d.ctors.mapM (fun (_, sels) =>
            (selsOf sels).mapM (fun (_, se) => buildFieldSortRef group se)))
        let fieldSorts : Array (Array (Array Z3Sort)) :=
          fieldData.map (·.map (·.map (·.1)))
        let fieldRefs  : Array (Array (Array UInt32)) :=
          fieldData.map (·.map (·.map (·.2)))
        let (dtSorts, declGroups) ←
          ctx.mkDatatypes sortNames ctorNames recogNames fieldNames fieldSorts fieldRefs
        -- register each datatype's sort under its group name
        for h : i in [:group.size] do
          let some s := dtSorts[i]? | throw (IO.userError "declareMutualDataTypes: sort layout mismatch")
          modify fun st => { st with sorts := st.sorts.insert group[i] s }
        -- register each datatype's func_decls from its flat `[ctor, recog, acc...]` layout
        for h : si in [:decls.size] do
          let decl := decls[si]
          let some declsFlat := declGroups[si]?
            | throw (IO.userError "declareMutualDataTypes: decl group layout mismatch")
          let mut k := 0
          for (cn, sels) in decl.ctors do
            let some ctorFd := declsFlat[k]? | throw (IO.userError "declareMutualDataTypes: layout mismatch (ctor)")
            k := k + 1
            let some recogFd := declsFlat[k]? | throw (IO.userError "declareMutualDataTypes: layout mismatch (recog)")
            k := k + 1
            modify fun st => { st with funcs := st.funcs.insert cn ctorFd }
            modify fun st => { st with funcs := st.funcs.insert (.NormalSymbol s!"is-{cn.toString}") recogFd }
            for (sn, _) in selsOf sels do
              let some accFd := declsFlat[k]? | throw (IO.userError "declareMutualDataTypes: layout mismatch (accessor)")
              k := k + 1
              modify fun st => { st with funcs := st.funcs.insert sn accFd }
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
