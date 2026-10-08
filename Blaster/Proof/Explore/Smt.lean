import Blaster.Proof.Explore.Core

/-!
# Symbolic exploration: SMT-LIB encoding for invariant inference

A small encoder from Lean propositions to quantifier-free SMT-LIB terms, used
only to *propose* invariants with a Horn solver. Nothing encoded here is
trusted: every proposed invariant is re-checked through ordinary verification
conditions.

* `Int`, `Nat` (with a non-negativity side condition) and `Bool` are native.
* Inductive types whose fields are encodable become SMT datatypes (mutually
  recursive groups are declared together). Strings and other opaque types are
  uninterpreted sorts.
* Linear arithmetic, comparisons, equality, Boolean and propositional
  connectives, `ite`, constructors and structure projections are encoded
  directly; non-recursive definitions are unfolded.
* Every other subterm (recursive calls, nonlinear operations, matches on
  unknown values) is *abstracted*: the same subterm becomes the same variable.
  Abstraction only weakens the encoded clause.
-/
namespace Blaster.Proof.Explore.Smt
open Lean Meta

/-- An inductive type declared as an SMT datatype. -/
structure DtInfo where
  /-- For each constructor: its Lean name, its SMT name and its SMT selectors. -/
  ctors : Array (Name × String × Array String)
deriving Inhabited

/-- What the encoding of a query declares, shared by its clauses. -/
structure Global where
  /-- The SMT sort of each encoded type. -/
  sorts : Std.HashMap Expr String := {}
  /-- The datatypes among them. -/
  dts : Std.HashMap Expr DtInfo := {}
  /-- The declarations of the query, in order. -/
  commands : Array String := #[]
  /-- For fresh SMT names. -/
  counter : Nat := 0
  /-- Projection-reduced forms of encoded expressions (memo). -/
  reduced : Std.HashMap Expr Expr := {}
  /-- The variable standing for a field read by a selector term (`(sel x)`). -/
  fieldVars : Std.HashMap String Expr := {}
  /-- Whether a constant is the `==` of a lawful `BEq` instance (`isLawfulDecider`). -/
  lawful : Std.HashMap Name Bool := {}

/-- The encoding of one clause. -/
structure Local where
  /-- The clause's variables and their sorts. -/
  vars : Array (String × String) := #[]
  /-- The variable of each abstracted term. -/
  names : Std.HashMap Expr String := {}
  /-- Side conditions of the variables (`x ≥ 0` for a natural number). -/
  side : Array String := #[]
  /-- Constructor case splits used by this clause (bounded). -/
  splits : Nat := 0
  /-- Whether stuck matches may be case split here (facts: yes; observations: opt-in). -/
  allowSplit : Bool := false
  /-- Encodings of applications in this clause: one per term, whichever context
  encodes it first. -/
  memo : Std.HashMap Expr String := {}

abbrev EncM := StateRefT Local (StateRefT Global ExM)

/-- A fresh SMT name starting with `pfx`. -/
def fresh (pfx : String) : EncM String := do
  let n := (← getThe Global).counter
  modifyThe Global fun g => {g with counter := n + 1}
  return s!"{pfx}{n}"

def inMeta (k : MetaM α) : EncM α := liftM (inCtx k : ExM α)

/-- The variable for the field that selector term `sel` reads: one per term, so
every split of the same value names its fields alike and the applications over
them share their abstractions. -/
def fieldVar (sel : String) (n : Name) (fty : Expr) : EncM Expr := do
  if let some v := (← getThe Global).fieldVars[sel]? then return v
  let v ← liftM (mkVar n fty .param false : ExM Expr)
  modifyThe Global fun g => {g with fieldVars := g.fieldVars.insert sel v}
  return v

def isNat (ty : Expr) : Bool := ty.isConstOf ``Nat
def isInt (ty : Expr) : Bool := ty.isConstOf ``Int

/-- One definitional step of `e`: `unfoldDefinition?`, or else the unfold
equation of its head (recursive definitions compiled by well-founded or
structural recursion that do not delta-unfold). -/
def unfoldViaEqn? (e : Expr) : MetaM (Option Expr) := do
  if let some e' ← unfoldDefinition? e then return some e'
  let .const fn _ := e.getAppFn | return none
  let some eqn ← (try getUnfoldEqnFor? fn (nonRec := true) catch _ => pure none) | return none
  let eqTy ← inferType (← mkConstWithFreshMVarLevels eqn)
  withNewMCtxDepth do
    let (_, _, body) ← forallMetaTelescopeReducing eqTy
    let some (_, lhs, rhs) := body.eq? | return none
    unless ← isDefEq lhs e do return none
    let r ← instantiateMVars rhs
    if r.hasMVar then return none
    return some r

/-- A type up to reducible abbreviations in its arguments
(`Option ColdCommitteeCredential` is `Option Credential`). -/
def typeKey (ty : Expr) : MetaM Expr := do
  Meta.transform (← whnf ty) (pre := fun e => do
    let e' ← whnfR e
    return if e' == e then .continue else .visit e')

/-! ## Sorts -/

mutual

/-- The SMT sort of the type `ty0`, declared on first use: `Int` for `Int` and
`Nat`, `Bool`, a datatype for an inductive type whose fields are encodable,
an uninterpreted sort otherwise; `none` for a proposition, sort or function. -/
partial def sortOf (ty0 : Expr) : EncM (Option String) := do
  let ty ← inMeta (whnf ty0)
  if isInt ty || isNat ty then return some "Int"
  if ty.isConstOf ``Bool then return some "Bool"
  if ty.isSort || ty.isForall || ty.hasLooseBVars || ty.hasFVar || ty.hasMVar then return none
  if let some s := (← getThe Global).sorts[ty]? then return some s
  -- the same instance spelled through abbreviations in its arguments: one sort,
  -- recorded under both spellings (datatype lookups use the caller's spelling)
  let key ← inMeta (typeKey ty)
  if key != ty then
    let r ← sortOf key
    if let some s := r then
      modifyThe Global fun g => {g with
        sorts := g.sorts.insert ty s
        dts := match g.dts[key]? with
          | some dt => g.dts.insert ty dt
          | none => g.dts}
    return r
  let some info ← inMeta (inductiveType? ty) | return ← uninterpreted ty
  if info.numIndices != 0 || info.isUnsafe then return ← uninterpreted ty
  if info.name == ``String || info.name == ``Char || (`UInt8).isPrefixOf info.name ||
      info.name == ``Float then return ← uninterpreted ty
  if ← inMeta (isProp ty) then return none
  declareGroup ty

/-- Declare `ty` as an uninterpreted sort. -/
partial def uninterpreted (ty : Expr) : EncM (Option String) := do
  let s ← fresh "U"
  modifyThe Global fun g => {g with
    sorts := g.sorts.insert ty s
    commands := g.commands.push s!"(declare-sort {s} 0)"}
  return some s

/-- Field types of every constructor of an inductive instance. -/
partial def fieldTypes (ty : Expr) : EncM (Option (Array (Name × Array Expr))) := do
  let some (_, ctors) ← inMeta (ctorTelescopes ty) | return none
  let mut out := #[]
  for (c, cty) in ctors do
    let tys ← inMeta <| forallTelescope cty fun fields _ => fields.mapM fun f => do
      let t ← whnf (← inferType f)
      return (t, fields.any fun g => t.containsFVar g.fvarId!)
    if tys.any (·.2) then return none
    out := out.push (c, tys.map (·.1))
  return some out

/-- Declare the datatype `ty` together with every datatype mutually recursive with it. -/
partial def declareGroup (ty : Expr) : EncM (Option String) := do
  -- collect reachable inductive instances
  let mut reach : Array Expr := #[]
  let mut edges : Std.HashMap Expr (Array Expr) := {}
  let mut todo := #[ty]
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    if reach.contains t then continue
    reach := reach.push t
    let some fs ← fieldTypes t | return ← uninterpreted ty
    let mut out := #[]
    for (_, tys) in fs do
      for ft in tys do
        if isInt ft || isNat ft || ft.isConstOf ``Bool then continue
        if (← getThe Global).sorts.contains ft then continue
        if ft.isForall || ft.isSort || (← inMeta (isProp ft)) then return ← uninterpreted ty
        let some info ← inMeta (inductiveType? ft) | continue
        if info.numIndices != 0 then return ← uninterpreted ty
        if info.name == ``String || info.name == ``Char then continue
        out := out.push ft
        todo := todo.push ft
    edges := edges.insert t out
  -- the group of `ty`: instances that reach `ty` and are reached from it
  let reachesTy := fun (start : Expr) => Id.run do
    let mut seen : Array Expr := #[]
    let mut stack := #[start]
    while !stack.isEmpty do
      let x := stack.back!
      stack := stack.pop
      if x == ty then return true
      if seen.contains x then continue
      seen := seen.push x
      stack := stack ++ edges.getD x #[]
    return false
  let group := reach.filter fun t => t == ty || reachesTy t
  -- declare dependencies outside the group first
  for t in reach do
    unless group.contains t do discard <| sortOf t
  -- names
  let mut names := #[]
  for t in group do
    let s ← fresh "D"
    names := names.push s
    modifyThe Global fun g => {g with sorts := g.sorts.insert t s}
  let mut decls := #[]
  for t in group do
    let some fs ← fieldTypes t | return ← uninterpreted ty
    let mut ctors := #[]
    let mut ctorDecls := #[]
    for (c, tys) in fs do
      let cs ← fresh "c"
      let mut sels := #[]
      let mut selDecls := #[]
      for ft in tys do
        let some fs ← sortOf ft | return ← uninterpreted ty
        let sel ← fresh "s"
        sels := sels.push sel
        selDecls := selDecls.push s!"({sel} {fs})"
      ctors := ctors.push (c, cs, sels)
      ctorDecls := ctorDecls.push s!"({cs}{String.join (selDecls.toList.map (" " ++ ·))})"
    modifyThe Global fun g => {g with dts := g.dts.insert t {ctors}}
    decls := decls.push s!"({String.intercalate " " ctorDecls.toList})"
  let header := String.intercalate " " (names.toList.map fun s => s!"({s} 0)")
  modifyThe Global fun g => {g with
    commands := g.commands.push s!"(declare-datatypes ({header}) ({String.intercalate " " decls.toList}))"}
  return (← getThe Global).sorts[ty]?

end

/-! ## Terms -/

/-- The clause variable for `e` (of type `ty`), declared on first use. -/
def declareVar (e : Expr) (ty : Expr) : EncM (Option String) := do
  if let some n := (← get).names[e]? then return some n
  let some s ← sortOf ty | return none
  let n ← fresh "x"
  modify fun l => {l with vars := l.vars.push (n, s), names := l.names.insert e n}
  if isNat (← inMeta (whnf ty)) then modify fun l => {l with side := l.side.push s!"(>= {n} 0)"}
  return some n

/-- A canonical key for an abstracted application: arguments that compute
to constructors (`mkCons x r` ↦ `x :: r`) are normalized, so the same value
reached along different unfoldings gets one variable. -/
def canonKey (e : Expr) : MetaM Expr := do
  unless e.isApp do return e
  let args ← e.getAppArgs.mapM fun a => do
    if a.isFVar || !a.isApp then return a
    let w ← whnf a
    return if (← isConstructorApp w) then w else a
  return mkAppN e.getAppFn args

/-- `e` abstracted: one variable per term (up to `canonKey`). -/
def abstract (e : Expr) : EncM (Option String) := do
  let k ← inMeta (canonKey e)
  if let some n := (← get).names[k]? then return some n
  let r ← declareVar k (← inMeta (inferType e))
  if let some n := r then modify fun l => {l with names := l.names.insert e n}
  return r

/-- `e` as a natural number literal (raw or `OfNat.ofNat`), if it is one. -/
def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- `e` as an integer literal (also through `Int.ofNat`, `Int.negSucc`, negation). -/
partial def intLit? (e : Expr) : Option Int :=
  if let some n := natLit? e then some n
  else if e.isAppOfArity ``Int.ofNat 1 then (natLit? e.appArg!).map Int.ofNat
  else if e.isAppOfArity ``Int.negSucc 1 then (natLit? e.appArg!).map fun n => -(n + 1 : Int)
  else if e.isAppOfArity ``Neg.neg 3 then (intLit? e.appArg!).map (- ·)
  else none

/-- Constructor case splits per encoded proposition. -/
def splitBudget : Nat := 40

/-- An integer as an SMT-LIB term. -/
def smtInt (i : Int) : String := if i < 0 then s!"(- {-i})" else s!"{i}"

/-- Is the constant `f` (two arguments of one type `T`, result `Bool`)
definitionally the `==` of a lawful `BEq T` instance (a derived structural
equality, say)? Such a decider means equality of its arguments; unrolling its
recursion instead leaves one unrelated atom per recursive call it reaches on
unknown values. -/
def isLawfulDecider (fn : Name) (f : Expr) : EncM Bool := do
  if let some r := (← getThe Global).lawful[fn]? then return r
  let r ← inMeta do
    try
      forallTelescopeReducing (← inferType f) fun xs res => do
        unless xs.size == 2 && res.isConstOf ``Bool do return false
        let t ← inferType xs[0]!
        if t.hasFVar || !(← isDefEq t (← inferType xs[1]!)) then return false
        let some inst ← synthInstance? (← mkAppM ``BEq #[t]) | return false
        let some _ ← synthInstance? (← mkAppOptM ``LawfulBEq #[t, inst]) | return false
        let beq ← mkAppOptM ``BEq.beq #[t, inst, xs[0]!, xs[1]!]
        withTransparency .default (isDefEq (mkAppN f xs) beq)
    catch _ => pure false
  modifyThe Global fun g => {g with lawful := g.lawful.insert fn r}
  return r

/-- The SMT-LIB term for `e`: the connectives, arithmetic, comparisons,
constructors and selectors the encoding knows, applied to the encodings of
their arguments; other subterms abstracted (`abstract`); non-recursive
definitions unfolded up to `depth` times. `none` when `e` has no SMT sort. -/
partial def enc (e : Expr) (depth : Nat := 12) : EncM (Option String) := do
  let e ← inMeta (instantiateMVars e)
  -- one term, one abstraction: `f {… field := x …}.field` and `f x` must share
  -- a variable (a hypothesis unfolded to `f x` and an observation of the same
  -- value read through a record literal otherwise become unrelated)
  let e ← if !e.hasFVar then pure e else
    match (← getThe Global).reduced[e]? with
    | some r => pure r
    | none => do
      let r ← inMeta (projReduce e)
      modifyThe Global fun g => {g with reduced := g.reduced.insert e r}
      pure r
  if let some n := (← get).names[e]? then return some n
  if let some i := intLit? e then
    let ty ← inMeta (do whnf (← inferType e))
    if isInt ty || isNat ty then return some (smtInt i)
  if e.isConstOf ``Bool.true || e.isConstOf ``True then return some "true"
  if e.isConstOf ``Bool.false || e.isConstOf ``False then return some "false"
  match e with
  | .fvar _ => return ← declareVar e (← inMeta (inferType e))
  | .mdata _ b => return ← enc b depth
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return ← abstractProp e
    if !(← inMeta (isProp d)) then return ← abstractProp e
    let some a ← enc d depth | return ← abstractProp e
    let some c ← enc b depth | return ← abstractProp e
    return some s!"(=> {a} {c})"
  | .proj _ i s =>
    let sty ← inMeta (do whnf (← inferType s))
    discard <| sortOf sty
    if let some dt := (← getThe Global).dts[sty]? then
      if dt.ctors.size == 1 then
        if let some sel := dt.ctors[0]!.2.2[i]? then
          if let some x ← enc s depth then return some s!"({sel} {x})"
    return ← abstract e
  | .app .. => do
    if let some r := (← get).memo[e]? then return some r
    let r ← encApp e depth
    if let some x := r then modify fun l => {l with memo := l.memo.insert e x}
    return r
  | .lit (.strVal _) =>
    -- one variable per literal, distinct from the clause's other literals
    let some srt ← sortOf (← inMeta (inferType e)) | return ← abstract e
    let n ← fresh "s"
    let mut distinct : Array String := #[]
    for (k, v) in (← get).names.toList do
      if k.isStringLit then distinct := distinct.push ("(not (= " ++ n ++ " " ++ v ++ "))")
    let names' := (← get).names.insert e n
    let vars' := (← get).vars.push (n, srt)
    let side' := (← get).side ++ distinct
    modify fun l => {l with vars := vars', names := names', side := side'}
    return some n
  | .const fn _ =>
    -- a defined constant (`adaSymbol := ""`): its value, as the program's literal
    if depth > 0 then
      if let some (.defnInfo info) := (← getEnv).find? fn then
        if !(← inMeta (isRecursiveDefinition fn)) && !(← inMeta (isProp e)) then
          let v ← inMeta (whnfCore (info.value.instantiateLevelParams info.levelParams (match e with | .const _ ls => ls | _ => [])))
          if !v.hasLooseBVars && !v.isLambda && v != e then return ← enc v (depth - 1)
    abstract e
  | _ => abstract e
where
  abstractProp (e : Expr) : EncM (Option String) := do
    if ← inMeta (isProp e) then
      if let some n := (← get).names[e]? then return some n
      let n ← fresh "b"
      modify fun l => {l with vars := l.vars.push (n, "Bool"), names := l.names.insert e n}
      return some n
    abstract e
  bin (op : String) (a b : Expr) (depth : Nat) : EncM (Option String) := do
    let some x ← enc a depth | return none
    let some y ← enc b depth | return none
    return some s!"({op} {x} {y})"
  encApp (e : Expr) (depth : Nat) : EncM (Option String) := do
    let args := e.getAppArgs
    let .const fn _ := e.getAppFn | return ← abstractProp e
    let ty ← inMeta (do whnf (← inferType e))
    let numeric (t : Expr) : EncM Bool := do
      let t ← inMeta (whnf t); return isInt t || isNat t
    -- arithmetic
    if (fn == ``HAdd.hAdd || fn == ``HSub.hSub || fn == ``HMul.hMul) && args.size == 6 then
      if ← numeric ty then
        let op := if fn == ``HAdd.hAdd then "+" else if fn == ``HSub.hSub then "-" else "*"
        let some x ← enc args[4]! depth | return ← abstract e
        let some y ← enc args[5]! depth | return ← abstract e
        if op == "*" && (intLit? args[4]!).isNone && (intLit? args[5]!).isNone then
          return ← abstract e
        if op == "-" && isNat ty then return some s!"(ite (>= {x} {y}) (- {x} {y}) 0)"
        return some s!"({op} {x} {y})"
    if (fn == ``Int.add || fn == ``Nat.add) && args.size == 2 then return ← bin "+" args[0]! args[1]! depth
    if fn == ``Int.sub && args.size == 2 then return ← bin "-" args[0]! args[1]! depth
    if fn == ``Nat.succ && args.size == 1 then
      let some x ← enc args[0]! depth | return ← abstract e
      return some s!"(+ {x} 1)"
    if (fn == ``Neg.neg && args.size == 3) || (fn == ``Int.neg && args.size == 1) then
      if ← numeric ty then
        let some x ← enc args.back! depth | return ← abstract e
        return some s!"(- {x})"
    if fn == ``Int.ofNat || fn == ``Nat.cast || fn == ``NatCast.natCast || fn == ``Int.toNat then
      if fn == ``Int.toNat then
        let some x ← enc args.back! depth | return ← abstract e
        return some s!"(ite (>= {x} 0) {x} 0)"
      let some x ← enc args.back! depth | return ← abstract e
      return some x
    -- comparisons
    if (fn == ``LT.lt || fn == ``LE.le || fn == ``GT.gt || fn == ``GE.ge) && args.size == 4 then
      if ← numeric args[0]! then
        let op := if fn == ``LT.lt then "<" else if fn == ``LE.le then "<=" else if fn == ``GT.gt then ">" else ">="
        return ← bin op args[2]! args[3]! depth
      -- an order on encoded values: an uninterpreted relation (congruence holds)
      if let some srt ← sortOf args[0]! then
        let (rel, a, b) := if fn == ``LT.lt then ("lt", args[2]!, args[3]!)
          else if fn == ``GT.gt then ("lt", args[3]!, args[2]!)
          else if fn == ``LE.le then ("le", args[2]!, args[3]!) else ("le", args[3]!, args[2]!)
        let name := s!"{rel}_{srt}"
        unless (← getThe Global).commands.contains s!"(declare-fun {name} ({srt} {srt}) Bool)" do
          modifyThe Global fun g => {g with commands := g.commands.push s!"(declare-fun {name} ({srt} {srt}) Bool)"}
        if let some x ← enc a depth then
          if let some y ← enc b depth then
            return some s!"({name} {x} {y})"
      return ← abstractProp e
    if (fn == ``Int.lt || fn == ``Nat.lt) && args.size == 2 then return ← bin "<" args[0]! args[1]! depth
    if (fn == ``Int.le || fn == ``Nat.le) && args.size == 2 then return ← bin "<=" args[0]! args[1]! depth
    -- equality
    if fn == ``Eq && args.size == 3 then
      if (← sortOf args[0]!).isSome then
        if let some r ← bin "=" args[1]! args[2]! depth then return some r
      return ← abstractProp e
    if fn == ``Ne && args.size == 3 then
      if (← sortOf args[0]!).isSome then
        if let some r ← bin "=" args[1]! args[2]! depth then return some s!"(not {r})"
      return ← abstractProp e
    if fn == ``BEq.beq && args.size == 4 then
      if (← sortOf args[0]!).isSome then
        if let some r ← bin "=" args[2]! args[3]! depth then return some r
      return ← abstract e
    -- a lawful decider applied directly (`eqData a b`): equality
    if args.size == 2 then
      if ← isLawfulDecider fn e.getAppFn then
        if (← sortOf (← inMeta (inferType args[0]!))).isSome then
          if let some r ← bin "=" args[0]! args[1]! depth then return some r
    if fn == ``bne && args.size == 4 then
      if (← sortOf args[0]!).isSome then
        if let some r ← bin "=" args[2]! args[3]! depth then return some s!"(not {r})"
      return ← abstract e
    -- Boolean and propositional connectives
    if fn == ``Decidable.decide && args.size == 2 then return ← enc args[0]! depth
    if (fn == ``and || fn == ``And) && args.size == 2 then return ← bin "and" args[0]! args[1]! depth
    if (fn == ``or || fn == ``Or) && args.size == 2 then return ← bin "or" args[0]! args[1]! depth
    if (fn == ``not || fn == ``Not) && args.size == 1 then
      let some x ← enc args[0]! depth | return ← abstractProp e
      return some s!"(not {x})"
    if fn == ``Iff && args.size == 2 then return ← bin "=" args[0]! args[1]! depth
    if fn == ``xor && args.size == 2 then return ← bin "xor" args[0]! args[1]! depth
    -- casts along an equation (`h ▸ x`): the transported value
    -- (over-applied when the transported value is a function)
    if ((fn == ``Eq.ndrec || fn == ``Eq.rec) && args.size ≥ 6) ||
        ((fn == ``Eq.mpr || fn == ``Eq.mp || fn == ``cast) && args.size ≥ 4) then
      let k := if fn == ``Eq.ndrec || fn == ``Eq.rec then 6 else 4
      return ← enc (← inMeta (whnfCore (mkAppN args[3]! (args.extract k args.size)))) depth
    -- dependent ifs and decisions: the branch proofs are opaque hypotheses
    if (fn == ``dite && args.size == 5) ||
        ((fn == ``Decidable.rec || fn == ``Decidable.casesOn) && args.size == 5) then
      let (p, tBr, fBr) := if fn == ``dite then (args[1]!, args[3]!, args[4]!)
        else if fn == ``Decidable.rec then (args[0]!, args[3]!, args[2]!)
        else (args[0]!, args[4]!, args[3]!)
      let some x ← enc p depth | return ← abstractProp e
      let hT ← liftM (mkVar `h p .param false : ExM Expr)
      let hF ← liftM (mkVar `h (mkNot p) .param false : ExM Expr)
      let tB ← inMeta (whnfCore (tBr.beta #[hT]))
      let fB ← inMeta (whnfCore (fBr.beta #[hF]))
      let some y ← enc tB depth | return ← abstractProp e
      let some z ← enc fB depth | return ← abstractProp e
      return some s!"(ite {x} {y} {z})"
    if (fn == ``ite && args.size == 5) || (fn == ``cond && args.size == 4) then
      let (c, a, b) := if fn == ``ite then (args[1]!, args[3]!, args[4]!) else (args[1]!, args[2]!, args[3]!)
      let some x ← enc c depth | return ← abstract e
      let some y ← enc a depth | return ← abstract e
      let some z ← enc b depth | return ← abstract e
      return some s!"(ite {x} {y} {z})"
    -- constructors and projections
    if let some (.ctorInfo ci) := (← getEnv).find? fn then
      discard <| sortOf ty
      if let some dt := (← getThe Global).dts[ty]? then
        if let some (_, cs, _) := dt.ctors.find? (·.1 == fn) then
          let fields := args.extract ci.numParams args.size
          if fields.size != ci.numFields then return ← abstract e
          if fields.isEmpty then return some cs
          let mut xs := #[]
          for f in fields do
            let some x ← enc f depth | return ← abstract e
            xs := xs.push x
          return some s!"({cs} {String.intercalate " " xs.toList})"
      return ← abstract e
    if let some info := (← getEnv).getProjectionFnInfo? fn then
      if args.size == info.numParams + 1 then
        let s := args[info.numParams]!
        let sty ← inMeta (do whnf (← inferType s))
        discard <| sortOf sty
        if let some dt := (← getThe Global).dts[sty]? then
          if dt.ctors.size == 1 then
            if let some sel := dt.ctors[0]!.2.2[info.i]? then
              if let some x ← enc s depth then return some s!"({sel} {x})"
    -- a recursor used as a case analysis (`casesOn` after reduction: the
    -- induction hypotheses unused), stuck on a value of an encoded datatype
    if let some (.recInfo info) := (← getEnv).find? fn then
      if (← get).allowSplit then
        if let some r ← encRecCases e info depth then return some r
    -- unfold non-recursive definitions (including matchers on known constructors)
    if depth > 0 then
      if let some e' ← unfoldOnce e then
        if e' != e then return ← enc e' (depth - 1)
      if (← get).allowSplit then
        let saved ← get
        let r ← try encMatch e (depth - 1) catch _ => do
          set saved; pure none
        if let some r := r then return some r
    abstractProp e
  /-- A match stuck on a value of an encoded datatype: a case split on its
  constructor testers, each alternative reduced with the constructor's fields
  read through the SMT selectors. -/
  encMatch (e : Expr) (depth : Nat) : EncM (Option String) := do
    let some m ← inMeta (matchMatcherApp? e (alsoCasesOn := true)) | return none
    unless m.discrs.size == 1 do return none
    let d := m.discrs[0]!
    -- a discriminant that computes (a recursive definition at a constructor,
    -- `find p (x :: xs)`): match on its step, an `if` as an `if` of matches,
    -- before any split on its variables
    if let some d' ← unfoldOnce d then
      if d' != d then
        if let some r ← encMatchOn m d' depth then return some r
    -- the variable to split: the discriminant itself, or a variable inside it
    -- that a nested pattern inspects (`(k, v) :: rest` stuck on `v`)
    -- a discriminant computed by a recursive definition that does not step
    -- (`find p refs`) is split as a whole first: its value is one abstraction
    -- shared by every term that inspects it, where splitting its variables
    -- unrolls the recursion to a fixed depth
    let recDiscr ← match d.getAppFn with
      | .const f _ => inMeta (isRecursiveDefinition f)
      | _ => pure false
    let vars := (collectFVars {} d).fvarIds.map Expr.fvar
    let cands := if d.isFVar then #[d] else if recDiscr then #[d] ++ vars else vars.push d
    for x in cands do
      if let some r ← splitOn e x depth then return some r
    return none
  /-- The match `m` on discriminant `d` (a step of its original one); a match on
  an `if` is the `if` of the matches on its branches. -/
  encMatchOn (m : MatcherApp) (d : Expr) (depth : Nat) : EncM (Option String) := do
    if depth == 0 then return none
    let rebuild := fun (x : Expr) => ({ m with discrs := #[x] } : MatcherApp).toExpr
    if d.isAppOfArity ``ite 5 || d.isAppOfArity ``cond 4 then
      let args := d.getAppArgs
      let (c, a, b) := if d.isAppOfArity ``ite 5 then (args[1]!, args[3]!, args[4]!)
        else (args[1]!, args[2]!, args[3]!)
      let some x ← enc c depth | return none
      let some y ← enc (← inMeta (whnfCore (rebuild a))) (depth - 1) | return none
      let some z ← enc (← inMeta (whnfCore (rebuild b))) (depth - 1) | return none
      return some s!"(ite {x} {y} {z})"
    enc (← inMeta (whnfCore (rebuild d))) (depth - 1)
  /-- Case split of `e` on the constructors of `x` (an encoded datatype), each
  alternative reduced with the constructor's fields read through the selectors. -/
  splitOn (e x : Expr) (depth : Nat) : EncM (Option String) := do
    if depth < 4 then return none
    if (← get).splits ≥ splitBudget then return none
    let xty ← inMeta (do whnf (← inferType x))
    let .const tn ls := xty.getAppFn | return none
    discard <| sortOf xty
    let some dt := (← getThe Global).dts[xty]? | return none
    let ind ← inMeta (getConstInfoInduct tn)
    let params := xty.getAppArgs.extract 0 ind.numParams
    let m0 ← inMeta (matchMatcherApp? e (alsoCasesOn := true))
    let some xx ← enc x depth | return none
    let mut bodies : Array (String × Expr) := #[]
    let mut progress := false
    for (cn, cs, sels) in dt.ctors do
      let cinfo ← inMeta (getConstInfoCtor cn)
      let cty ← inMeta (instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams ls) params)
      let mut fields := #[]
      let mut ty := cty
      for i in [0:cinfo.numFields] do
        let .forallE n fty b _ := ty | return none
        let some sel := sels[i]? | return none
        let v ← fieldVar s!"({sel} {xx})" n fty
        fields := fields.push v
        ty := b.instantiate1 v
        modify fun l => {l with names := l.names.insert v s!"({sel} {xx})"}
      let app := mkAppN (mkAppN (mkConst cn ls) params) fields
      let e' := if x.isFVar then e.replaceFVar x app else replaceTerm e x app
      let body ← inMeta (whnfCore e')
      let stuck ← match (← inMeta (matchMatcherApp? body (alsoCasesOn := true))), m0 with
        | some m', some m => pure (m'.matcherName == m.matcherName && m'.discrs == (m.discrs.map fun d => if x.isFVar then d.replaceFVar x app else replaceTerm d x app))
        | _, _ => pure false
      unless stuck do progress := true
      bodies := bodies.push (cs, body)
    -- a split no alternative reduces under (a structure the match does not
    -- inspect) is refused before its branches spend the budget
    unless progress do return none
    let mut outs : Array (String × String) := #[]
    for (cs, body) in bodies do
      modify fun l => {l with splits := l.splits + 1}
      let some bx ← enc body (depth - 2) | return none
      outs := outs.push (s!"((_ is {cs}) {xx})", bx)
    if outs.isEmpty then return none
    let mut out := outs.back!.2
    for (t, b) in outs.pop.reverse do
      out := s!"(ite {t} {b} {out})"
    return some out
  encRecCases (e : Expr) (info : RecursorVal) (depth : Nat) : EncM (Option String) := do
    if info.numIndices != 0 then return none
    if depth < 4 then return none
    -- one motive, or a nested inductive's recursor (`Data` with its `List Data`
    -- motive) used as a case analysis of the major's own type; mutual blocks
    -- (one motive per member) stay out
    if info.numMotives != 1 && info.numMotives == info.all.length then return none
    let args := e.getAppArgs
    unless args.size == info.getMajorIdx + 1 do return none
    if (← get).splits ≥ splitBudget then return none
    let x ← inMeta (whnf args[info.getMajorIdx]!)
    let xty ← inMeta (do whnf (← inferType x))
    discard <| sortOf xty
    let some dt := (← getThe Global).dts[xty]? | return none
    let some xx ← enc x depth | return none
    let mut outs : Array (String × String) := #[]
    for i in [0:dt.ctors.size] do
      let (cn, cs, sels) := dt.ctors[i]!
      let some ci := info.rules.findIdx? (·.ctor == cn) | return none
      let minor := args[info.numParams + info.numMotives + ci]!
      let cinfo ← inMeta (getConstInfoCtor cn)
      -- bind the minor premise's fields to selectors, its hypotheses to fresh variables
      let mut body := minor
      let mut ihs : Array Expr := #[]
      -- the fields, then one hypothesis per field of the recursor's own type
      let mut nrec := 0
      for j in [0:cinfo.numFields] do
        let .lam n fty b _ := body | return none
        let some sel := sels[j]? | return none
        let v ← fieldVar s!"({sel} {xx})" n fty
        modify fun l => {l with names := l.names.insert v s!"({sel} {xx})"}
        let fw ← inMeta (whnf fty)
        -- a field of the block's type, directly or nested (`List Data`,
        -- `List (Data × Data)`), comes with an induction hypothesis
        if (fw.find? fun s => s.isConst && info.all.contains s.constName!).isSome then
          nrec := nrec + 1
        body := b.instantiate1 v
      for _ in [0:nrec] do
        let .lam n fty b _ := body | return none
        let v ← liftM (mkVar n fty .param false : ExM Expr)
        ihs := ihs.push v
        body := b.instantiate1 v
      let red ← inMeta (whnfCore body)
      if ihs.any (fun h => red.containsFVar h.fvarId!) then return none
      modify fun l => {l with splits := l.splits + 1}
      let some bx ← enc red (depth - 2) | return none
      outs := outs.push (s!"((_ is {cs}) {xx})", bx)
    if outs.isEmpty then return none
    let mut out := outs.back!.2
    for (t, b) in outs.pop.reverse do
      out := s!"(ite {t} {b} {out})"
    return some out
  /-- One non-recursive unfolding followed by structural reduction. -/
  unfoldOnce (e : Expr) : EncM (Option Expr) := do
    let .const fn _ := e.getAppFn | return none
    if ← inMeta (isRecursiveDefinition fn) then
      -- a recursive definition at a constructor argument (`f []`, `f (x :: xs)`):
      -- one equation step, as the definition computes it
      -- arguments that compute to constructors (`mkCons x r`) count as such
      let args' ← inMeta <| e.getAppArgs.mapM fun a => do
        let w ← whnf a
        return if (← isConstructorApp w) then w else a
      let hasCtorArg ← inMeta <| args'.anyM fun a => isConstructorApp a
      unless hasCtorArg do return none
      let e := mkAppN e.getAppFn args'
      let some e' ← inMeta (unfoldViaEqn? e) | return none
      let r ← inMeta (whnfCore e')
      -- only when the step resolved (no stuck recursor/matcher on the head)
      if r == e then return none
      -- a step stuck on a match is kept when matches are split by constructor
      if (← inMeta (matchMatcherApp? r)).isSome then
        if !(← get).allowSplit then return none
      if let .const h _ := r.getAppFn then
        if let some (.recInfo _) := (← getEnv).find? h then return none
      return some r
    let env ← getEnv
    if isMatcherCore env fn || isCasesOnRecursor env fn then
      let r ← inMeta (whnfCore e)
      if r != e then return some r
      -- a match on constructor values stuck inside, on literal patterns
      -- (`Constr 0 [B "lit"]`): its compiled form decides the literals
      if isMatcherCore env fn then
        if let some m ← inMeta (matchMatcherApp? e) then
          let ctorDiscrs ← inMeta <| m.discrs.allM fun d => do
            let w ← whnf d
            return (← isConstructorApp w) || w.isLit
          if ctorDiscrs then
            let some e' ← inMeta (delta? e) | return none
            let r ← inMeta (whnfCore e')
            return if r == e then none else some r
      return none
    -- a type-class method at a known instance (`IsData.toData (C a)`): take the
    -- instance's implementation, so the value is computed as the program does
    if let some pinfo := env.getProjectionFnInfo? fn then
      if pinfo.fromClass then
        let some r ← inMeta (unfoldProjInst? e) | return none
        let r ← inMeta (whnfCore r.headBeta)
        return if r == e then none else some r
    let some info := env.find? fn | return none
    unless info.hasValue do return none
    let some e' ← inMeta (unfoldDefinition? e) | return none
    inMeta (whnfCore e')

/-- Encode a proposition; abstraction applies to unencodable parts. -/
def encProp (p : Expr) : EncM String := do
  -- hypotheses and facts get a small case-split budget of their own
  modify fun l => {l with splits := splitBudget - 12, allowSplit := true}
  let r := (← enc p 24).getD "true"
  modify fun l => {l with allowSplit := false}
  return r

end Blaster.Proof.Explore.Smt
