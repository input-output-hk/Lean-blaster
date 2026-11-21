import Lean

/-!
# Static detection of cyclic rewriting between `@[blaster]` rules

Every optimization function generated from a theorem/axiom (registered or not) is recorded in the
scoped environment extension `blasterRuleExt`, together with the normalized statement it was
generated from (`∀ x₁ … xₙ, P₁ → … → Pₖ → lhs = rhs`, see `Blaster.ThmOptFn.generate`) and, when it
can be recovered, the same statement normalized with unfolding of the non-recursive functions.

Before the optimization function of a new theorem `N` is generated, the graph whose nodes are the
recorded rules (plus `N`) is explored from `N`: there is an edge `A ⟶ B` when the lhs pattern of `B`
matches a sub-term of the rhs of `A`, either in its folded form (the term handed to the matcher
before its arguments are normalized) or in its unfolded form (the term handed to the matcher once
its arguments are normalized). Only the pattern variables of `B` may be instantiated, the variables
of the rhs of `A` are rigid: `len (a :: xs) = Nat.add 1 (len xs)` has no edge to itself (`len xs` is
not an instance of `len (?a :: ?xs)`), whereas `f n = f (Nat.add 1 n)` has one. A warning is logged
when a path leads from `N` back to `N`, and no optimization function is generated for `N`.

The check is an over-approximation of the rewriting performed at run time:
  - premises are ignored (a cycle may be closed by rules whose premises are never satisfied together);
  - universe levels and sorts are not compared;
  - built-in normalization rules are not modelled, they are confluent and both normal forms of a
    rhs are examined.
Hand-written optimization functions (`@[blaster Head]` on a definition of type `Blaster.OptFn`) are
not recorded: a cycle through such a function is only detected at run time (see `applyExtension?`).
-/

open Lean Meta

namespace Blaster.ThmOptFn

/-- Rewriting rule recorded for the static cyclic check (serialized in the .olean file). -/
structure Rule where
  /-- Name of the theorem/axiom. -/
  thmName : Name
  /-- Head constant of the lhs. -/
  head : Name
  /-- Normalized statement the optimization function was generated from (`NormalizeMode.Restricted`),
      the lhs is tagged with `__Blaster.rewriteLhs`. -/
  stmt : Expr
  /-- Statement normalized with unfolding of the non-recursive functions (`NormalizeMode.Partial`),
      `none` when the orientation of its conclusion could not be guaranteed. -/
  stmtUnfolded : Option Expr
  deriving Inhabited, BEq, Repr

/-- Rules recorded for the static cyclic check, indexed by the head constant of their lhs. -/
initialize blasterRuleExt : SimpleScopedEnvExtension Rule (NameMap (Array Rule)) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun m r => m.insert r.head (((m.find? r.head).getD #[]).push r)
  }

/-- Split the conclusion of a theorem into `(eqSort, lhs, rhs)`:
      - `lhs = rhs`
      - `lhs ↔ rhs` (handled as `lhs = rhs`)
      - `¬ p`        (handled as `p = False`)
      - `p`          (handled as `p = True`)
-/
def splitConclusion (concl : Expr) : MetaM (Expr × Expr × Expr) := do
  match concl.getAppFn, concl.getAppArgs with
  | .const ``Eq _, #[psort, lhs, rhs] => return (psort, lhs.consumeMData, rhs)
  | .const ``Iff _, #[lhs, rhs] => return (.sort .zero, lhs, rhs)
  | .const ``Not _, #[p] => return (.sort .zero, p, mkConst ``False)
  | _, _ => return (.sort .zero, concl, mkConst ``True)

/-! ## Pattern matching -/

/-- Match the pattern `p` against the term `t` under the substitution `σ`: only the meta variables
    of `pvars` (the binders of the statement `p` comes from) may be instantiated, consistently over
    their occurrences; every other variable is rigid. Universe levels and sorts are not compared.
    Mirrors the structural match performed by the generated optimization functions (`mkPat`). -/
partial def matchPattern (pvars : Std.HashSet MVarId) (p t : Expr) (σ : Std.HashMap MVarId Expr)
  : Option (Std.HashMap MVarId Expr) :=
  let p := p.consumeMData
  let t := t.consumeMData
  match p with
  | .mvar id =>
      if pvars.contains id then
        match σ.get? id with
        | some t' => if t' == t then some σ else none
        | none => some (σ.insert id t)
      else if p == t then some σ else none
  | .app pf pa =>
      match t with
      | .app tf ta => matchPattern pvars pf tf σ >>= matchPattern pvars pa ta
      | _ => none
  | .const n _ =>
      match t with
      | .const n' _ => if n == n' then some σ else none
      | _ => none
  | .lit l =>
      match t with
      | .lit l' => if l == l' then some σ else none
      | _ => none
  | .lam _ pd pb _ =>
      match t with
      | .lam _ td tb _ => matchPattern pvars pd td σ >>= matchPattern pvars pb tb
      | _ => none
  | .forallE _ pd pb _ =>
      match t with
      | .forallE _ td tb _ => matchPattern pvars pd td σ >>= matchPattern pvars pb tb
      | _ => none
  | .letE _ pd pv pb _ =>
      match t with
      | .letE _ td tv tb _ =>
          matchPattern pvars pd td σ >>= matchPattern pvars pv tv >>= matchPattern pvars pb tb
      | _ => none
  | .proj n i ps =>
      match t with
      | .proj n' i' ts => if n == n' && i == i' then matchPattern pvars ps ts σ else none
      | _ => none
  | .sort _ =>
      match t with
      | .sort _ => some σ
      | _ => none
  | .bvar i =>
      match t with
      | .bvar j => if i == j then some σ else none
      | _ => none
  | .fvar _ => if p == t then some σ else none
  | .mdata .. => none -- unreachable, consumed above

/-- Match the arguments of a pattern against the arguments of an application (same arity). -/
def matchArgs (pvars : Std.HashSet MVarId) (pargs targs : Array Expr) : Bool := Id.run do
  if pargs.size != targs.size then return false
  let mut σ : Std.HashMap MVarId Expr := {}
  for i in [:pargs.size] do
    match matchPattern pvars pargs[i]! targs[i]! σ with
    | some σ' => σ := σ'
    | none => return false
  return true

/-! ## Rule graph -/

/-- lhs of a rule opened with meta variables: the pattern tried by its optimization function. -/
structure Pattern where
  thmName : Name
  pvars : Std.HashSet MVarId
  args : Array Expr

structure CheckState where
  /-- Rules under consideration, indexed by theorem name. -/
  rules : NameMap Rule
  /-- Theorem names of the rules, indexed by the head constant of their lhs. -/
  byHead : NameMap (Array Name)
  /-- Patterns of the rules, indexed by head constant (computed on demand). -/
  patterns : NameMap (Array Pattern) := {}
  /-- Forms of the rhs of the rules (folded, then unfolded when available), indexed by theorem name
      (computed on demand). -/
  rhsForms : NameMap (Array Expr) := {}

abbrev CheckM := StateRefT CheckState MetaM

/-- Patterns of the rules whose lhs has head `head`. -/
def getPatterns (head : Name) : CheckM (Array Pattern) := do
  if let some ps := (← get).patterns.find? head then return ps
  let mut ps := #[]
  for n in ((← get).byHead.find? head).getD #[] do
    let some r := (← get).rules.find? n | continue
    let (xs, _, concl) ← forallMetaTelescope r.stmt
    let (_, lhs, _) ← splitConclusion concl
    let pvars := xs.foldl (fun s x => s.insert x.mvarId!) ({} : Std.HashSet MVarId)
    ps := ps.push { thmName := n, pvars, args := lhs.consumeMData.getAppArgs }
  modify fun s => { s with patterns := s.patterns.insert head ps }
  return ps

/-- Forms of the rhs of rule `thm`, with the binders of its statement opened with (rigid)
    meta variables. -/
def getRhsForms (thm : Name) : CheckM (Array Expr) := do
  if let some fs := (← get).rhsForms.find? thm then return fs
  let some r := (← get).rules.find? thm | return #[]
  let mut fs := #[]
  for stmt in [r.stmt] ++ r.stmtUnfolded.toList do
    let (_, _, concl) ← forallMetaTelescope stmt
    let (_, _, rhs) ← splitConclusion concl
    fs := fs.push rhs
  modify fun s => { s with rhsForms := s.rhsForms.insert thm fs }
  return fs

/-- Add to `acc` the rules whose pattern matches a sub-term of `e` (every application node of `e`
    is examined with its full list of arguments, as done by the optimizer). -/
partial def collectSuccessors (e : Expr) (acc : NameSet) : CheckM NameSet := do
  match e with
  | .mdata _ b => collectSuccessors b acc
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const h _ := f.consumeMData then
        for p in (← getPatterns h) do
          if matchArgs p.pvars p.args args then acc := acc.insert p.thmName
      else
        acc ← collectSuccessors f acc
      for a in args do
        acc ← collectSuccessors a acc
      return acc
  | .lam _ d b _ | .forallE _ d b _ => collectSuccessors b (← collectSuccessors d acc)
  | .letE _ d v b _ => collectSuccessors b (← collectSuccessors v (← collectSuccessors d acc))
  | .proj _ _ s => collectSuccessors s acc
  | _ => return acc

/-- Rules whose lhs matches a sub-term of a form of the rhs of `thm`. -/
def successors (thm : Name) : CheckM (Array Name) := do
  let mut acc : NameSet := {}
  for rhs in (← getRhsForms thm) do
    acc ← collectSuccessors rhs acc
  let mut res := #[]
  for n in acc do res := res.push n
  return res

/-- Depth-first search of a path from `start` back to `start`; the path is returned as the sequence
    of theorem names visited (starting and ending with `start`). -/
partial def findCycle (start : Name) : CheckM (Option (Array Name)) := do
  let (r, _) ← go start #[] {}
  return r
 where
  go (cur : Name) (path : Array Name) (visited : NameSet) : CheckM (Option (Array Name) × NameSet) := do
    let path := path.push cur
    let succs ← successors cur
    if succs.contains start then return (some (path.push start), visited)
    let mut visited := visited
    for s in succs do
      unless visited.contains s do
        visited := visited.insert s
        let (r, visited') ← go s path visited
        visited := visited'
        if r.isSome then return (r, visited)
    return (none, visited)

/-- Return the cycle (as a sequence of theorem names starting and ending with `rule.thmName`) that
    the rule `rule` would close with the rules recorded in `blasterRuleExt`, if any. -/
def findCyclicRewriting (rule : Rule) : MetaM (Option (Array Name)) := do
  let mut rules : NameMap Rule := {}
  let mut byHead : NameMap (Array Name) := {}
  for (h, rs) in blasterRuleExt.getState (← getEnv) do
    for r in rs do
      rules := rules.insert r.thmName r
    byHead := byHead.insert h (rs.map (·.thmName))
  rules := rules.insert rule.thmName rule
  byHead := byHead.insert rule.head (((byHead.find? rule.head).getD #[]).push rule.thmName)
  (findCycle rule.thmName).run' { rules, byHead }

/-- Log the warning reporting the cycle `cycle` found by `findCyclicRewriting`. -/
def logCyclicRules (cycle : Array Name) : MetaM Unit := do
  let path := " ↦ ".intercalate (cycle.toList.map fun n => s!"`{n}`")
  logWarning m!"[blaster]: Cyclic rewriting detected: {path} (the rhs of each rule contains an instance of the lhs of the next one).\nNo optimization function generated for `{cycle[0]!}`."

end Blaster.ThmOptFn
