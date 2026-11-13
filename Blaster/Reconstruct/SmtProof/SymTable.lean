import Lean
import Blaster.Smt.Translate
import Blaster.Reconstruct.SmtProof.Backend
import Blaster.Reconstruct.SmtProof.Interp
import Blaster.Reconstruct.SmtProof.Poly

/-!
# Interpretation of the symbols of an SMT query

The interpretation (`SymTable`) of the symbols of Blaster's query in Lean: the Lean functions of the translation
(from its caches), the datatypes, the definitions of lambda terms and of auxiliary functions, the sorts of the
polymorphic encoding, and the skolem functions of the proofs.
-/

open Lean Meta Elab Term Tactic Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.Reconstruct.SmtProof

/-! ## Interpretation of the query symbols -/

/-- Lean name of an SMT symbol produced by `nameToSmtSymbol` (possibly quoted). -/
def symbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropRight 1) else s
  s.toName

/-- Interpretation of Blaster's auxiliary recursive functions (as Lean functions on `Int`). -/
def auxiliaryInterp (s : String) : MetaM (Option Expr) := do
  let int := Lean.mkConst ``Int
  let toNat (x : Expr) := mkApp (Lean.mkConst ``Int.toNat) x
  let ofNat (n : Expr) := mkApp3 (Lean.mkConst ``Nat.cast [levelZero]) int (Lean.mkConst ``instNatCastInt) n
  match s with
  | "@Nat.pow" | "@Int.pow" =>
      -- `Nat` is encoded by integers with guards at quantifiers. Z3's recursive
      -- power equations also apply to negative bases, so truncating the base
      -- with `toNat` would make e.g. `pow x 1 = x * pow x 0` false. The bridge
      -- relates this integer extension to natural powers using `natCast_pow`.
      withLocalDeclD `x int fun x => withLocalDeclD `y int fun y => do
        mkLambdaFVars #[x, y] (← mkAppM ``HPow.hPow #[x, toNat y])
  | "@Nat.log2" =>
      withLocalDeclD `x int fun x => do
        mkLambdaFVars #[x] (ofNat (mkApp (Lean.mkConst ``Nat.log2) (toNat x)))
  -- the string of a list of characters
  | "@String.mk" => return some (Lean.mkConst ``String.mk)
  | _ => return none

/-- Remove the bars of a quoted symbol. -/
def unquote (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" && s.length ≥ 2 then (s.drop 1).dropRight 1 else s

/-- The definition of a lambda term of the translation (see `Blaster.Smt.translateLambda`):
    `(forall (xs) (! (=> G₁ (=> ... (= (@apply @lambda_n xs) b))) :qid @lambda_n_def_cstr))`, and
    `(forall (ys xs) (! (=> G₁ (=> ... (= (@apply (@apply @global_lambda_n ys) xs) b))) ...))`: its name, the
    parameters `ys` and `xs`, the guards on variables (membership predicates, the guards `0 ≤ x` are removed, see
    `guardNatQuantifiers`) and its body. -/
def guardedLambdaDef? (e : SExpr) :
    Option (String × Array (String × SExpr) × Array (String × SExpr) × Std.HashMap String SExpr × STerm) := Id.run do
  let some #[SExpr.atom "forall", SExpr.list vs, SExpr.list ann] := e.list? | return none
  if ann[0]? != some (SExpr.atom "!") then return none
  let some d₀ := ann[1]? | return none
  let mut d := d₀
  let names := vs.filterMap fun v => match v with
    | .list #[.atom x, _] => some x
    | _ => none
  let mut guards : Std.HashMap String SExpr := {}
  for _ in [0:3 * vs.size] do
    match d with
    | .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom _], b] => d := b
    | .list #[.atom "=>", g, b] =>
        let some h := g.head? | return none
        if !(unquote h).startsWith "@is" then return none
        -- the guarded parameter (e.g., `(@isInstance x α)`, `(@isList α x)`)
        let some args := g.list? | return none
        let isParam (a : SExpr) : Option String := match a with
          | .atom x => if names.contains x then some x else none
          | _ => none
        let some x := args.findSome? isParam | return none
        guards := guards.insert x g
        d := b
    | _ => break
  let some #[SExpr.atom "=", SExpr.list lhs, body] := d.list? | return none
  let vars := vs.filterMap fun v => match v with
    | .list #[.atom x, s] => some (x, s)
    | _ => none
  let some (SExpr.atom apply) := lhs[0]? | return none
  if !apply.startsWith "@apply" then return none
  let .ok b := STerm.ofSExpr {} body | return none
  match lhs[1]? with
  | some (SExpr.atom l) =>
      if !l.startsWith "@lambda" then return none
      return some (l, #[], vars, guards, b)
  | some (SExpr.list inner) =>
      let some (SExpr.atom g) := inner[1]? | return none
      if !g.startsWith "@global_lambda" then return none
      let k := inner.size - 2
      if k > vars.size then return none
      return some (g, vars.extract 0 k, vars.extract k vars.size, guards, b)
  | _ => return none

/-- Interpretation of a lambda term of the translation (see `guardedLambdaDef?`) of sort `s` in `Poly`: each parameter
    `x` guarded by a membership predicate `Img w x` is bound by `fun x => if Img w x then b else dflt x`, where `dflt`
    is the default of the world of the function (see `Poly.mkWorld`), such that the lambda term is the image of a
    Lean function (see `Poly.lam_world_ite`) whatever its body outside of the domain (e.g., constant functions). The
    definition, guarded by the same predicates, holds. Returns the term and the table with the symbols of the default
    values. -/
def guardedLambda (tbl : SymTable) (n : String) (s : SExpr) (ys xs : Array (String × SExpr))
    (guards : Std.HashMap String SExpr) (body : STerm) : MetaM (STerm × SymTable) := do
  let mut tbl := tbl
  let mut ty ← (sortToType s).run { table := tbl }
  for _ in ys do
    let .forallE _ _ b _ ← whnfR ty | throwError "guardedLambda: function type expected"
    ty := b
  let mut doms := #[]
  for _ in xs do
    let .forallE _ d b _ ← whnfR ty | throwError "guardedLambda: function type expected"
    doms := doms.push (d, b)
    ty := b
  let mut t := body
  for i' in [0:xs.size] do
    let i := xs.size - 1 - i'
    let (x, _) := xs[i]!
    let (d, c) := doms[i]!
    let guarded ← match guards.get? x with
      | some g =>
          let some h := g.head? | pure none
          let some (.lam _) := tbl.syms.get? h | pure none
          let .ok g := STerm.ofSExpr {} g | pure none
          pure (some g)
      | none => pure none
    if let some g := guarded then
      -- the default of the world (see `Poly.mkWorld`): the identity for the functions of a sort into itself
      let dflt ← if c == d || (← withReducible (isDefEq d c)) then pure (STerm.sym x) else do
        let k := s!"@@poly_default_{n}_{i}"
        tbl := { tbl with syms := tbl.syms.insert k (.expr (← Poly.mkDefault c)) }
        pure (STerm.sym k)
      t := .app "ite" #[g, t, dflt]
    t := .quant .lambda #[xs[i]!] t
  return (if ys.isEmpty then t else .quant .lambda ys t, tbl)

/-- The axiom of a type `T` used as a value (see `Blaster.Smt.translateIndTypeExpr?`):
    `(forall ((@x S)) (=> (@isT @x) (@isInstance (@coerce_m @x) @abstractType_n)))`: the conversion `@coerce_m`, the
    sort `S` of `T` and the constant `@abstractType_n` standing for `T`. -/
def abstractTypeAxiom? (e : SExpr) : Option (String × SExpr × String) := Id.run do
  let some #[SExpr.atom "forall", SExpr.list #[SExpr.list #[SExpr.atom x, s]], b] := e.list? | return none
  -- NOTE: possibly with patterns, `(! b :pattern ...)`
  let b := match b.list? with
    | some xs => if xs[0]? == some (SExpr.atom "!") then xs[1]?.getD b else b
    | none => b
  -- the premises: the membership predicate of `T`, and `0 ≤ @x` for `Nat` (see `guardNatQuantifiers`)
  let mut b := b
  for _ in [0:3] do
    let some #[SExpr.atom "=>", _, c] := b.list? | break
    b := c
  let some #[SExpr.atom _, SExpr.list #[SExpr.atom c, SExpr.atom x'], SExpr.atom a] := b.list? | return none
  if x' != x || !(unquote c).startsWith "@coerce" || !(unquote a).startsWith "@abstractType" then return none
  return some (c, s, a)

/-- Interpretation of Blaster's polymorphic encoding (see `Poly`), given the sort variables of the goal with their
    SMT symbols: the membership predicates of the types with sort variables are the images of their worlds (e.g.,
    `@isFun α β f` is `Img (liftFun (inj α) (inj β) _) f`), the constants of the goal the images of their values
    (e.g., `x : α` is `inj α x`), and the lambda terms are guarded by the membership predicates of their parameters
    (see `guardedLambda`). The sorts `@Type` and `@Instance`, the predicates `@isInstance` and the polymorphic
    functions (at the universe, see `Poly.instantiateUniv`) are interpreted by `buildSymTable`. -/
def polySymTable (tbl : SymTable) (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (sortVars : Array (String × Expr)) : MetaM SymTable := do
  let mut tbl := tbl
  for (s, α) in sortVars do tbl := { tbl with syms := tbl.syms.insert s (.expr α) }
  -- membership predicates of the types with sort variables (cached as `fun αs => T`): `fun αs v => Img w v`
  for (k, decl) in env.smtEnv.indTypeInstCache.toList do
    let .lam .. := k | continue
    try
      let sort ← ofExcept (parseSExpr (toString decl.instSort))
      let d ← (sortToType sort).run { table := tbl }
      let pred ← lambdaTelescope k fun αs t => do
        if ← αs.anyM fun α => do return !isTypeUniverse (← inferType α) then throwError "not a sort variable"
        let some (w, _) ← Poly.mkWorld t d | throwError "no world for {t}"
        -- NOTE: the sort parameters are explicit arguments of the predicates (e.g., `{β}` in the cached type)
        withNewBinderInfos (αs.map (·.fvarId!, .default)) do
        withLocalDeclD `v d fun v => do mkLambdaFVars (αs.push v) (← mkAppM ``Poly.Img #[w, v])
      let n := toString decl.instName
      -- NOTE: the recursive definitions of the predicates of datatypes (`_LRec`) have the same interpretation
      let rec_ := if n.startsWith "|" then s!"|{unquote n}_LRec|" else s!"{n}_LRec"
      tbl := { tbl with syms := tbl.syms.insert n (.lam pred) |>.insert rec_ (.lam pred) }
    catch _ => pure ()
  -- constants of the goal
  for c in cmds do
    let some #[SExpr.atom "declare-const", SExpr.atom n, s] := c.list? | continue
    let some x := consts.get? n | continue
    try
      let d ← (sortToType s).run { table := tbl }
      if let some (w, _) ← Poly.mkWorld (← inferType x) d then
        tbl := { tbl with syms := tbl.syms.insert n (.expr (Poly.applyWorld w x)) }
    catch _ => pure ()
  -- types used as values (see `abstractTypeAxiom?`): the constant `@abstractType_n` is the type `T`, and the
  -- conversion `@coerce_m` maps the values of the sort of `T` to their preimages in `T` in the universe
  -- (`Poly.coerceWorld`), such that the axiom holds
  let mut absTypes : Std.HashMap String Expr := {}
  for (k, n) in env.smtEnv.abstractTypeCache.toList do
    absTypes := absTypes.insert (toString n) k
    tbl := { tbl with syms := tbl.syms.insert (toString n) (.expr k) }
  for c in cmds do
    let some #[SExpr.atom "assert", a] := c.list? | continue
    let some (coerce, s, abst) := abstractTypeAxiom? a | continue
    -- NOTE: a conversion shared by several types (of the same sort) is interpreted for the first one
    if tbl.syms.contains coerce then continue
    let some t := absTypes.get? abst | continue
    try
      let d ← (sortToType s).run { table := tbl }
      -- NOTE: the world of `T` (the identity when `T` is interpreted as itself, e.g., `List Nat`)
      let w? ← if ← withReducible (isDefEq t d) then pure (some (mkApp (mkConst ``id [← getLevel t]) t))
        else pure ((← Poly.mkWorld.go t d).map (·.1))
      if let some w := w? then
        tbl := { tbl with syms := tbl.syms.insert coerce (.expr (← mkAppM ``Poly.coerceWorld #[w])) }
    catch _ => pure ()
  -- lambda terms, guarded by the membership predicates of their parameters (the first definition, as in
  -- `buildSymTable`)
  let mut sorts : Std.HashMap String SExpr := {}
  for c in cmds do
    if let some #[SExpr.atom "declare-const", SExpr.atom n, s] := c.list? then sorts := sorts.insert n s
  let mut guarded : Std.HashSet String := {}
  for c in cmds do
    let some #[SExpr.atom "assert", a] := c.list? | continue
    let some (n, ys, xs, guards, body) := guardedLambdaDef? a | continue
    let some s := sorts.get? n | continue
    if guarded.contains n then continue
    guarded := guarded.insert n
    try
      let (t, tbl') ← guardedLambda tbl n s ys xs guards body
      tbl := { tbl' with syms := tbl'.syms.insert n (.macro #[] t) }
    catch _ => pure ()
  return tbl

/-- Build the interpretation of the symbols of the query `cmds`, given the translation environment
    and the map from SMT constants (`$k`) to Lean free variables. Blaster's polymorphic encoding is interpreted
    with `@Instance` as `instanceType?` (a single sort variable), or as `Poly.Univ` given the sort variables
    `polySortVars?` (see `polySymTable`). -/
def buildSymTable (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (instanceType? : Option Expr := none) (polySortVars? : Option (Array (String × Expr)) := none) :
    MetaM SymTable := do
  let mut tbl : SymTable := {}
  -- polymorphic encoding: the sorts `@Type` and `@Instance` of the sort variables of `Sort u` (cached on `Sort u`),
  -- and their membership predicates `@isInstance v α`
  let mut polySorts : Std.HashMap String Expr := {}
  if polySortVars?.isSome then
    for (k, decl) in env.smtEnv.indTypeInstCache.toList do
      let .sort u := k | continue
      let (.SymbolSort ty, some (.SymbolSort inst)) := (decl.instSort, decl.instInstanceSort) | continue
      let univ := Lean.mkConst ``Poly.Univ [u]
      let mem ← withLocalDeclD `v univ fun v => withLocalDeclD `α (mkSort u) fun α => do
        mkLambdaFVars #[v, α] (← mkAppM ``Poly.Img #[mkApp (Lean.mkConst ``Poly.inj [u]) α, v])
      polySorts := polySorts.insert (toString ty) (mkSort u) |>.insert (toString inst) univ
      tbl := { tbl with syms := tbl.syms.insert (toString decl.instName) (.lam mem) }
  -- Lean functions of the translation
  let mut funs : Std.HashMap String Expr := {}
  let arities := if polySortVars?.isSome then funArities cmds else {}
  for (k, v) in env.smtEnv.funInstCache.toList do
    let nm := match v with
      | .SimpleIdent s => toString s
      | .QualifiedIdent s _ => toString s
    let e ← if polySortVars?.isSome then polyInstantiate arities nm k else instantiateSortParams instanceType? k
    funs := funs.insert nm e
  let mut datatypeSorts : Array SExpr := #[]
  for c in cmds do
    let some xs := c.list? | continue
    match xs[0]?.bind SExpr.atom?, xs[1]?.bind SExpr.atom? with
    | some "declare-sort", some n =>
        -- polymorphic encoding (see `proveBySmtProof`)
        if let some t := polySorts.get? n then
          tbl := { tbl with sorts := tbl.sorts.insert n t }
        else if n.startsWith "@Type" then
          tbl := { tbl with sorts := tbl.sorts.insert n (mkConst ``Unit) }
        else if n.startsWith "@Instance" then
          if let some t := instanceType? then tbl := { tbl with sorts := tbl.sorts.insert n t }
        else if let some t ← emptyInductive? n then
          tbl := { tbl with sorts := tbl.sorts.insert n t }
    | some "define-sort", some n =>
        if let some (SExpr.list #[]) := xs[2]? then
          tbl := { tbl with aliases := tbl.aliases.insert n xs[3]! }
    | some "declare-const", some n =>
        if let some e := consts.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if let some (SExpr.atom s) := xs[2]? then
          -- sort variables (polymorphic encoding)
          if s.startsWith "@Type" then tbl := { tbl with syms := tbl.syms.insert n (.expr (mkConst ``Unit.unit)) }
        if let some s := xs[2]? then datatypeSorts := datatypeSorts.push s
    | some "declare-fun", some n =>
        if let some e := funs.get? n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if n.startsWith "@apply" then
          tbl := { tbl with syms := tbl.syms.insert n .apply }
        else if n.startsWith "@is" && !tbl.syms.contains n then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
    | some "define-fun", some n =>
        let some (SExpr.list ps) := xs[2]? | continue
        let params := ps.filterMap fun p => match p with
          | .list #[.atom x, s] => some (x, s)
          | _ => none
        match STerm.ofSExpr {} xs[4]! with
        | .ok body => tbl := { tbl with syms := tbl.syms.insert n (.macro params body) }
        | .error _ => pure ()
    | some "define-fun-rec", some n =>
        if n.startsWith "@is" then
          tbl := { tbl with syms := tbl.syms.insert n .trueFun }
        else if let some e ← auxiliaryInterp n then
          tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
        else if (unquote n).endsWith "_LRec" then
          -- the definition of a recursive function: same interpretation as the function
          let base := (unquote n).dropRight 5
          if let some e := funs.get? base <|> funs.get? s!"|{base}|" then
            tbl := { tbl with syms := tbl.syms.insert n (.expr e) }
    | some "assert", _ =>
        -- definitions of lambda terms (see `Blaster.Smt.translateLambda`):
        -- `(forall (xs) (! (= (@apply @lambda_n xs) b) :qid @lambda_n_def_cstr))`, and
        -- `(forall (ys xs) (! (= (@apply (@apply @global_lambda_n ys) xs) b) :qid @global_lambda_n_def_cstr))`
        if let some (n, t) := lambdaDef? xs[1]! then
          if !tbl.syms.contains n then tbl := { tbl with syms := tbl.syms.insert n (.macro #[] t) }
    | some "declare-datatype", some n =>
        tbl ← addDatatype tbl n xs[2]!
    | some "declare-datatypes", _ =>
        let some (SExpr.list sorts) := xs[1]? | continue
        let some (SExpr.list decls) := xs[2]? | continue
        for (s, d) in sorts.zip decls do
          let some (SExpr.atom n) := s.list? >>= (·[0]?) | continue
          tbl ← addDatatype tbl n d
    | _, _ => pure ()
  if let some sortVars := polySortVars? then tbl ← polySymTable tbl cmds env consts sortVars
  -- datatype sorts of the query as they occur in proofs (with expanded aliases)
  let ctx : InterpCtx := { table := tbl }
  let mut expanded : Std.HashMap String (Option Expr) := {}
  for s in datatypeSorts do
    let some _ := s.list? | continue
    try
      let t ← (sortToType s).run ctx
      let key := toString (expandSort tbl s)
      match expanded.get? key with
      | some (some t') => if !(← isDefEq t t') then expanded := expanded.insert key none
      | some none => pure ()
      | none => expanded := expanded.insert key (some t)
    catch _ => pure ()
  for (k, v) in expanded.toList do
    if let some t := v then tbl := { tbl with expandedSorts := tbl.expandedSorts.insert k t }
  return tbl
where
  /-- Arities of the functions declared by `cmds`. -/
  funArities (cmds : Array SExpr) : Std.HashMap String Nat := Id.run do
    let mut m := {}
    for c in cmds do
      if let some #[SExpr.atom "declare-fun", SExpr.atom n, SExpr.list ss, _] := c.list? then m := m.insert n ss.size
    return m
  /-- Lean functions of the translation abstracted over their generic parameters, interpreted by `Poly`: at the
      universe (see `Poly.instantiateUniv`). -/
  polyInstantiate (arities : Std.HashMap String Nat) (nm : String) (e : Expr) : MetaM Expr := do
    let some arity := arities.get? nm | return e
    try Poly.instantiateUniv e (← Poly.genericParams e arity) catch _ => return e
  /-- Lean functions of the translation abstracted over their generic parameters (instances of
      `Blaster.Optimize.getInstApp`, e.g., `fun α [BEq α] a b => a == b`), which are erased in their SMT
      signatures: with a single sort variable `α` interpreting `@Instance`, the explicit sort parameters are
      instantiated with `α` (the instances are synthesized when the function is applied, and the implicit
      parameters inferred from the arguments, see `mkAppCoerce`). -/
  instantiateSortParams (instanceType? : Option Expr) (e : Expr) : MetaM Expr := do
    let some α := instanceType? | return e
    let ty ← inferType α
    let mut e := e.headBeta
    for _ in [:16] do
      let .lam _ t b bi := e | break
      if !bi.isExplicit || !(← isDefEq t ty) then break
      e := (b.instantiate1 α).headBeta
    return e
  lambdaDef? (e : SExpr) : Option (String × STerm) := Id.run do
    let some #[SExpr.atom "forall", SExpr.list vs, SExpr.list ann] := e.list? | return none
    if ann[0]? != some (SExpr.atom "!") then return none
    -- NOTE: the guards of the definition are removed: `0 ≤ x` for the variables of sort `Nat` (see
    -- `guardNatQuantifiers`), and the membership predicates of the parameters (see `Blaster.Smt.translateLambda`)
    let rec unguard (e : SExpr) (fuel : Nat) : SExpr :=
      match fuel, e with
      | fuel + 1, .list #[.atom "=>", .list #[.atom "<=", .atom "0", .atom _], b] => unguard b fuel
      | fuel + 1, .list #[.atom "=>", g, b] =>
          if (g.head?.map unquote).any (·.startsWith "@is") then unguard b fuel else e
      | _, e => e
    let some #[SExpr.atom "=", SExpr.list lhs, body] := (ann[1]?.map (unguard · (3 * vs.size))) >>= SExpr.list? | return none
    let vars := vs.filterMap fun v => match v with
      | .list #[.atom x, s] => some (x, s)
      | _ => none
    let some (SExpr.atom apply) := lhs[0]? | return none
    if !apply.startsWith "@apply" then return none
    let .ok b := STerm.ofSExpr {} body | return none
    match lhs[1]? with
    | some (SExpr.atom l) =>
        if !l.startsWith "@lambda" then return none
        return some (l, .quant .lambda vars b)
    | some (SExpr.list inner) =>
        let some (SExpr.atom g) := inner[1]? | return none
        if !g.startsWith "@global_lambda" then return none
        let k := inner.size - 2
        if k > vars.size then return none
        let ys := vars.extract 0 k
        let xs := vars.extract k vars.size
        return some (g, .quant .lambda ys (if xs.isEmpty then b else .quant .lambda xs b))
    | _ => return none
  /-- The inductive type without constructors (e.g., `Empty`) declared as the uninterpreted sort `n`
      (e.g., `(declare-sort Empty 0)`), which is interpreted by itself: its membership predicate is `false`,
      and the terms of the sort in a proof are terms of the goal (e.g., the applications of a function of
      type `True → Empty`). -/
  emptyInductive? (n : String) : MetaM (Option Expr) := do
    let some (.inductInfo info) := (← getEnv).find? (symbolToName n) | return none
    unless info.ctors.isEmpty && info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do
      return none
    return some (mkConst info.name)
  addDatatype (tbl : SymTable) (n : String) (decl : SExpr) : MetaM SymTable := do
    -- `(par (params) (ctors))` or `(ctors)`
    let ctors := match decl with
      | .list #[.atom "par", _, .list cs] => cs
      | .list cs => cs
      | _ => #[]
    let mut tbl := tbl
    for c in ctors do
      let (cname, fields) := match c with
        | .atom a => (a, #[])
        | .list xs => (xs[0]!.atom?.getD "", xs.extract 1 xs.size)
        | _ => ("", #[])
      let leanCtor := symbolToName cname
      let some (.ctorInfo info) := (← getEnv).find? leanCtor | continue
      tbl := { tbl with
        syms := tbl.syms.insert cname (.ctor leanCtor) |>.insert s!"is-{cname}" (.tester leanCtor),
        sorts := tbl.sorts.insert n (mkConst info.induct) }
      for h : i in [:fields.size] do
        if let some (SExpr.atom sel) := fields[i].list? >>= (·[0]?) then
          tbl := { tbl with syms := tbl.syms.insert sel (.selector leanCtor i) }
    return tbl

/-- `buildSymTable` with the polymorphic encoding interpreted by `Poly`, for the sort variables `sortVars` (declared
    by the translation `env`). -/
def polyBuildSymTable (cmds : Array SExpr) (env : TranslateEnv) (consts : Std.HashMap String Expr)
    (sortVars : Array Expr) : TermElabM SymTable := do
  let (syms, _) ← (sortVars.mapM fun α => do
      return (toString (← typeParamNameToSmtSymbol α.fvarId!), α) : TranslateEnvT (Array (String × Expr))).run env
  buildSymTable cmds env consts (polySortVars? := some syms)

/-- Interpretation of the skolem constants introduced by `sk` steps (Z3): for
    `(~ (not (forall ((x S)) φ)) (not φ[x := c]))` (resp. `(~ (exists ((x S)) φ) φ[x := c])`),
    the constant `c` (named `x!n`) is interpreted as `Classical.epsilon (fun x => ¬ φ)`
    (resp. `Classical.epsilon (fun x => φ)`). With several bound variables `x₁ ... xₙ`, the constant `cᵢ` of `xᵢ` is
    interpreted as `Classical.epsilon (fun xᵢ => ¬ ∀ xᵢ₊₁ ... xₙ, φ[x₁ := c₁, ..., xᵢ₋₁ := cᵢ₋₁])` (resp. with `∃`), as
    replayed by `sk` (one quantifier at a time). Skolem functions (applied to the variables of the context) are only
    handled for a single bound variable. -/
partial def addSkolems (proof : Proof) (tbl : SymTable) : MetaM SymTable := do
  let mut tbl := tbl
  -- names introduced by `intro-def` (Z3's Tseitin names): `(= t k)` defines `k` as `t`; similarly for the
  -- names introduced by theory lemmas (e.g., `(= pb!2 (or ...))` of Z3's pseudo-Boolean preprocessing)
  for step in proof.steps do
    if !(step.rule == "intro-def" || (step.rule == "th-lemma" && step.premises.isEmpty)) then continue
    match step.concl.stripAnnot with
    | .app "=" #[t, .sym k] | .app "=" #[.sym k, t] =>
        if !tbl.syms.contains k && (findSkolem (· == k) t fun _ => true).isNone then
          tbl := { tbl with syms := tbl.syms.insert k (.macro #[] t) }
    | _ => pure ()
  for step in proof.steps do
    if step.rule != "sk" then continue
    let .app _ #[a, b] := step.concl.stripAnnot | continue
    let (vars, body, neg) := match a.stripAnnot with
      | .app "not" #[.quant .forall vs φ] => (vs, φ, true)
      | .quant .exists vs φ => (vs, φ, false)
      | _ => (#[], .sym "true", false)
    if vars.isEmpty then continue
    if let #[(x, sort)] := vars then
      -- skolem function applied to the variables of the context: `(x!n y₁ ... yₖ)`
      if let some (c, ys) := findSkolemApp (isSkolemOf x) b (fun c => !tbl.syms.contains c) then
        tbl := { tbl with syms := tbl.syms.insert c (.skolem ys x sort body neg) }
        continue
    -- the skolem constants: for each variable `x`, a symbol of `b` named `x!n`, not occurring in `a` and not yet
    -- interpreted
    let some cs := vars.mapM fun (x, _) =>
        findSkolem (isSkolemOf x) b fun c => !tbl.syms.contains c && (findSkolem (· == c) a fun _ => true).isNone
      | continue
    try
      let es ← (do
        let mut es : Array Expr := #[]
        let mut locals : Std.HashMap String Expr := {}
        for h : i in [:vars.size] do
          let (x, sort) := vars[i]
          let ty ← sortToType sort
          let u ← getLevel ty
          let inst ← synthInstance (mkApp (mkConst ``Nonempty [u]) ty)
          -- the variables after `x` remain quantified
          let rest := vars.extract (i+1) vars.size
          let bodyᵢ := if rest.isEmpty then body else .quant (if neg then .forall else .exists) rest body
          let e ← withLocalDeclD (Name.mkSimple x) ty fun fx => do
            let φ ← withScopeCache (locals.insert x fx) (interp bodyᵢ)
            let p ← mkLambdaFVars #[fx] (if neg then mkNot φ else φ)
            return mkApp3 (mkConst ``Classical.epsilon [u]) ty inst p
          es := es.push e
          locals := locals.insert x e
        return es : InterpM (Array Expr)).run { table := tbl }
      for (c, e) in cs.zip es do
        tbl := { tbl with syms := tbl.syms.insert c (.expr e) }
    catch _ => pure ()
  return tbl
where
  /-- Whether `c` is the name of a skolem constant of the variable `x`, i.e., `x!n` (with quoted symbols: `|x!n|`
      for `|x|`). -/
  isSkolemOf (x c : String) : Bool := (unquote c).startsWith (unquote x ++ "!")
  findSkolemApp (name : String → Bool) (t : STerm) (ok : String → Bool) : Option (String × Array String) :=
    match t with
    | .app f args =>
        let syms := args.filterMap fun a => match a with | .sym s => some s | _ => none
        if name f && !args.isEmpty && syms.size == args.size && ok f then some (f, syms)
        else args.findSome? (findSkolemApp name · ok)
    | .iapp _ _ args | .qual _ _ args => args.findSome? (findSkolemApp name · ok)
    | .quant _ _ b => findSkolemApp name b ok
    | .annot t _ => findSkolemApp name t ok
    | _ => none
  findSkolem (name : String → Bool) (t : STerm) (ok : String → Bool) : Option String :=
    match t with
    | .sym s => if name s && ok s then some s else none
    | .app f args =>
        if name f && args.isEmpty && ok f then some f else args.findSome? (findSkolem name · ok)
    | .iapp _ _ args | .qual _ _ args => args.findSome? (findSkolem name · ok)
    | .quant _ _ b => findSkolem name b ok
    | .annot t _ => findSkolem name t ok
    | _ => none

end Blaster.Reconstruct.SmtProof
