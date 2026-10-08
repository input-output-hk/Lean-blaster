import Blaster.Proof.Explore.Success
import Blaster.Proof.Explore.Proof
import Blaster.Proof.Explore.Smt
import Blaster.Proof.Explore.Houdini

/-!
# Symbolic exploration: invariant proposals by constrained Horn clauses

Each cut point `c` gets an unknown relation `R_c` over *observations*: its
scalar variables, goal-directed scalar functions of its structured variables,
and the scalar subterms of the goal and hypotheses. Every recorded path yields
one Horn clause:

* entry:  `H → R_root(obs_root σ_root)`
* edge:   `R_c(obs_c σ) ∧ facts σ → R_c'(obs_c' σ')`
* accept: `R_c(obs_c σ) ∧ facts σ ∧ leaf σ → G σ`

`σ` is the path's constructor substitution; an observation applied to a known
constructor is unfolded, so its value is related to the observations of the
constructor's fields. The invariant search (`Houdini.lean`) proposes
interpretations of the `R_c`; they are translated back to Lean propositions and
returned as *candidates*. They are never assumed: the proof replay checks them
through verification conditions.
-/
namespace Blaster.Proof.Explore.Chc

register_option blaster.explore.modelFile : String := {
  defValue := ""
  descr := "Read the invariant model from this file instead of searching (for testing the \
    checker: the model is only a proposal, every obligation is still proved)" }
open Lean Meta

/-! ## Paths -/

/-- Where a path of a cut point's transition tree ends. -/
inductive PathEnd where
  /-- The machine accepts: the goal must hold. -/
  | accept
  /-- A leaf proposition, which must imply the goal. -/
  | leaf (p : Expr)
  /-- Another cut point, at its template under `σ`. -/
  | goto (cut : Nat) (σ : Subst)
  /-- A procedure exit: the state is the region's exit shape under `σ`. -/
  | exit (σ : Subst)
  /-- A call: the callee entry (a cut) under `σ` must satisfy its precondition. -/
  | call (cut : Nat) (σ : Subst)
  /-- A point the exploration recorded as unreachable: the path must be infeasible. -/
  | unreachable
deriving Inhabited

/-- A path from a cut point to where its clause ends. -/
structure Path where
  /-- The constructor values the path gave variables. -/
  subst : Subst := {}
  /-- The decisions and generalization equations of the path. -/
  facts : Array Expr := #[]
  /-- Callee postconditions assumed after calls: callee entry template, entry
  substitution, and the substitution of the exit holes by the returned values. -/
  posts : Array (Nat × Subst × Subst) := #[]
  last : PathEnd := .accept
deriving Inhabited

/-- `σ` with `atom := value`, also inside the values of `σ`. -/
def substAdd (σ : Subst) (atom value : Expr) : Subst :=
  let one : Subst := ({} : Subst).insert atom.fvarId! value
  let σ' : Subst := σ.fold (init := ({} : Subst)) fun acc k v => acc.insert k (Subst.apply one v)
  σ'.insert atom.fvarId! value

/-- Apply a substitution to a fixpoint (fields of fields). -/
partial def applyFix (σ : Subst) (e : Expr) (fuel : Nat := 8) : Expr :=
  let e' := Subst.apply σ e
  if e' == e || fuel == 0 then e' else applyFix σ e' (fuel - 1)

/-- `atom = C fields` as a full constructor application. -/
def ctorApp (atom : Expr) (c : Name) (fields : Array Expr) : ExM Expr := inCtx do
  let ty ← whnf (← inferType atom)
  let .const _ ls := ty.getAppFn | throwError "chc: split on non-inductive"
  let info ← getConstInfoInduct ty.getAppFn.constName!
  let params := ty.getAppArgs.extract 0 info.numParams
  return mkAppN (mkAppN (mkConst c ls) params) fields

/-- Every path from a node to the next cut points, exits, calls, or leaves.
A call yields a path to the callee's precondition and continues, assuming the
callee's postcondition, at its return point. -/
partial def paths (plan : Plan) (entry? : Option Nat) (node : Nat) (p : Path) (acc : Array Path) :
    ExM (Array Path) := do
  if acc.size ≥ 200000 then throwError "chc: too many paths"
  match plan.result.search.nodes[node]! with
  | .split atom alts =>
    let mut acc := acc
    for (c, fields, next) in alts do
      let app ← ctorApp atom c fields
      acc ← paths plan entry? next {p with subst := substAdd p.subst atom app} acc
    return acc
  | .gen e g _ next =>
    let eq ← inCtx (mkEq e g)
    paths plan entry? next {p with facts := p.facts.push eq} acc
  | .known _ _ next | .knownCond _ _ _ _ next | .rewrite _ _ _ next => paths plan entry? next p acc
  | .cond _ prop _ _ t f =>
    let acc ← paths plan entry? t {p with facts := p.facts.push prop} acc
    paths plan entry? f {p with facts := p.facts.push (mkNot prop)} acc
  | .accept => return acc.push {p with last := .accept}
  | .leaf q => return acc.push {p with last := .leaf q}
  | .unreachable _ => return acc.push {p with last := .unreachable}
  -- an incomplete exploration proves nothing: never drop it silently
  | .abort why => throwError "chc: exploration was incomplete ({why})"
  | .exit s =>
    let some e := entry? | return acc
    let some shape := plan.graph.shapes[e]? | return acc
    let some σ ← instanceOf? shape s | throwError "chc: exit does not match its shape"
    return acc.push {p with last := .exit σ}
  | .call s _ entry _ ret? =>
    let some ce := plan.cutOf[entry]? | return acc
    let tplE := plan.result.search.tpls[entry]!
    let some σc ← instanceOf? tplE.body (← normState s) | throwError "chc: call does not match its entry"
    let acc := acc.push {p with last := .call ce σc}
    let some ret := ret? | return acc
    let some shape := plan.graph.shapes[entry]? | return acc
    let retState := match plan.result.search.nodes[ret]! with
      | .goto st _ => st
      | .call st .. => st
      | _ => shape
    let some ρ ← instanceOf? (Subst.apply σc shape) retState | throwError "chc: return does not match its shape"
    paths plan entry? ret {p with posts := p.posts.push (entry, σc, ρ)} acc
  | .goto .. =>
    match plan.graph.targets[node]? with
    | some (v, σ) =>
      match plan.cutOf[v]? with
      | some ci => return acc.push {p with last := .goto ci σ}
      | none =>
        match plan.result.search.tpls[v]!.node? with
        | some n => paths plan entry? n p acc
        | none => return acc
    | none => return acc
  | _ => return acc

/-! ## Observations -/

/-- A goal-directed observer: `fun x => f a₁ … x … aₙ` with a scalar result. -/
structure Observer where
  fn : Expr
  domain : Expr
deriving Inhabited

/-- Whether `ty` is `Int`, `Nat` or `Bool`. -/
def isScalarType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isConstOf ``Int || ty.isConstOf ``Nat || ty.isConstOf ``Bool

/-- Values a relation can carry whole: scalars, strings, and non-recursive
constructions of such fields (a byte string, a credential). Constant inputs
of these types are carried as relation arguments so that every clause speaks
about the same value. -/
partial def isCarriedType (ty : Expr) (depth : Nat := 3) : MetaM Bool := do
  let ty ← whnf ty
  if ← isScalarType ty then return true
  if ty.isConstOf ``String then return true
  if depth == 0 then return false
  let .const n ls := ty.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? n | return false
  if info.isRec || info.numIndices != 0 || info.ctors.length > 4 then return false
  for c in info.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ls)
      (ty.getAppArgs.extract 0 info.numParams)
    let ok ← forallTelescope cty fun fields _ => fields.allM fun f => do
      isCarriedType (← inferType f) (depth - 1)
    unless ok do return false
  return true

/-- The propositions together with bounded unfoldings of the non-recursive
definitions they apply: scalar checks hidden behind wrappers (for example a
per-element validity scan inside a validity predicate) become visible. -/
partial def unfoldProps (props : Array Expr) (depth : Nat := 4) : MetaM (Array Expr) := do
  let out ← IO.mkRef props
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let rec go (e : Expr) (d : Nat) : MetaM Unit := do
    if d == 0 then return
    let subs ← IO.mkRef (#[] : Array Expr)
    e.forEach fun t => do
      unless t.isApp && !t.hasLooseBVars && t.hasFVar do return
      let .const fn _ := t.getAppFn | return
      if (← seen.get).contains t then return
      seen.modify (·.insert t)
      let env ← getEnv
      if isMatcherCore env fn || (env.find? fn |>.any (·.isCtor)) then return
      unless ← isScalarType (← inferType t) do return
      if ← isRecursiveDefinition fn then return
      let some u ← (try unfoldDefinition? t catch _ => pure none) | return
      let u ← whnfCore u
      let u ← Blaster.Proof.Explore.projReduce u
      subs.modify (·.push u)
    for u in ← subs.get do
      out.modify (·.push u)
      go u (d - 1)
  for p in props do go p depth
  out.get

/-- Observers and root observations from the goal and hypotheses. -/
def observers (props : Array Expr) (isRoot : FVarId → Bool) (context : Bool := false) :
    MetaM (Array Observer × Array Expr) := do
  let obs ← IO.mkRef (#[] : Array Observer)
  let roots ← IO.mkRef (#[] : Array Expr)
  for p in props do
    p.forEach fun t => do
      unless t.isApp && !t.hasLooseBVars do return
      let .const _ _ := t.getAppFn | return
      unless ← isScalarType (← inferType t) do
        -- a carried value a recursive definition computes (an `Option` of a
        -- credential): the goal may inspect it by a match
        let .const f _ := t.getAppFn | return
        unless (← isRecursiveDefinition f) && (← isCarriedType (← inferType t)) do return
      let args := t.getAppArgs
      for i in [0:args.size] do
        let a := args[i]!
        let aty ← whnf (← inferType a)
        if (← isScalarType aty) || aty.isSort || aty.isForall || (← isProp aty) then continue
        -- only recursive data (lists, trees, encoded data) needs an observer:
        -- values of non-recursive types are split into their fields anyway
        let some info ← inductiveType? aty | continue
        unless info.isRec || info.isNested do continue
        unless a.hasFVar do continue
        let others := (args.eraseIdxIfInBounds i)
        -- the remaining arguments are fixed: closed or roots
        unless others.all fun o => (collectFVars {} o).fvarIds.all isRoot do continue
        unless (collectFVars {} a).fvarIds.all isRoot do continue
        let fn ← withLocalDeclD `x aty fun x => mkLambdaFVars #[x] (mkAppN t.getAppFn (args.set! i x))
        unless (← obs.get).any (·.fn == fn) do obs.modify (·.push {fn, domain := aty})
        unless (← roots.get).contains t do roots.modify (·.push t)
  -- a scalar match over recursive root data (`match find … refs with
  -- | some c => check c wdrl | none => false`): each such root, the rest of the
  -- match fixed, is observed as a whole
  -- only for the goal: a hypothesis's validity matches would each give an
  -- observer (and a root link to prove) per root they mention
  if context then
    for p in props do
      p.forEach fun t => do
        unless t.isApp && !t.hasLooseBVars && t.hasFVar do return
        let .const fn _ := t.getAppFn | return
        unless isMatcherCore (← getEnv) fn do return
        unless ← isScalarType (← inferType t) do return
        let fvs := (collectFVars {} t).fvarIds
        unless fvs.all isRoot do return
        for id in fvs do
          let aty ← whnf (← inferType (.fvar id))
          let some info ← inductiveType? aty | continue
          unless info.isRec || info.isNested do continue
          let fn ← withLocalDeclD `x aty fun x => mkLambdaFVars #[x] (t.replaceFVar (.fvar id) x)
          unless (← obs.get).any (·.fn == fn) do obs.modify (·.push {fn, domain := aty})
          unless (← roots.get).contains t do roots.modify (·.push t)
  -- Recursive data a hypothesis equation fixes in terms of the roots (the
  -- encoded credential in `lookup … = some (key, encode credential)`): the
  -- program may carry that value in its state, so observe equality with it.
  let equations ← IO.mkRef (#[] : Array Expr)
  for p in props do
    p.forEach fun t => do
      if let some (_, _, rhs) := t.eq? then
        unless rhs.hasLooseBVars do equations.modify (·.push rhs)
  for rhs in ← equations.get do
    let found ← IO.mkRef (#[] : Array Expr)
    rhs.forEach fun t => do
      unless t.isApp && !t.hasLooseBVars && t.hasFVar do return
      let .const _ _ := t.getAppFn | return
      unless (collectFVars {} t).fvarIds.all isRoot do return
      let ty ← whnf (← inferType t)
      let some info ← inductiveType? ty | return
      unless info.isRec || info.isNested do return
      found.modify (·.push t)
    for t0 in (← found.get).toList.take 12 do
      -- in normal form, as the program computes it (`toData (C a)` becomes
      -- the constructor term the machine evaluates it to)
      let t ← try Meta.reduce t0 (skipTypes := true) catch _ => pure t0
      let ty ← inferType t
      let fn? ← withLocalDeclD `x ty fun x => do
        try
          let d ← mkDecide (← mkEq x t)
          return some (← mkLambdaFVars #[x] d)
        catch _ => return none
      let some fn := fn? | continue
      unless (← obs.get).any (·.fn == fn) do obs.modify (·.push {fn, domain := ty})
  return (← obs.get, ← roots.get)

/-- Scalar-valued applications inside `e` with exactly one argument of a
recursive inductive type (the observed data), as `(application, index)`. -/
def scalarApplications (e : Expr) : MetaM (Array (Expr × Nat)) := do
  let out ← IO.mkRef (#[] : Array (Expr × Nat))
  e.forEach fun t => do
    unless t.isApp && !t.hasLooseBVars && t.getAppFn.isConst do return
    unless ← isScalarType (← inferType t) do return
    let args := t.getAppArgs
    let mut recursiveArgs := #[]
    for i in [0:args.size] do
      let aty ← whnf (← inferType args[i]!)
      if let some info ← inductiveType? aty then
        if info.isRec || info.isNested then recursiveArgs := recursiveArgs.push i
    if recursiveArgs.size == 1 then out.modify (·.push (t, recursiveArgs[0]!))
  out.get

/-- Observers transported through proved facts. A fact that mentions a known
observer's function at the observer's fixed arguments also relates other
scalar functions of recursive data; with their remaining arguments fixed by
that match they become observers too. For example a decoding law
`decode d = ok v → read c t v = readEncoded c t d` transports the observer
`readEncoded c t` on encoded data to `read c t` on decoded values, and its
validity premises to Boolean observers of the same values. -/
def transport (facts : Array Expr) (known : Array Observer) : MetaM (Array Observer) := do
  let mut result := known
  for _ in [:6] do
    let before := result.size
    for fact in facts do
      let found ← withNewMCtxDepth do
        let (args, _, body) ← forallMetaTelescopeReducing (← inferType fact)
        -- the premises too: a validity premise (`valid v = true → …`) names a
        -- Boolean observer of the same data as the conclusion
        let mut apps ← scalarApplications body
        for arg in args do
          let type ← inferType arg
          if ← isProp type then apps := apps ++ (← scalarApplications type)
        let mut found : Array Observer := #[]
        for (app, _) in apps do
          for o in result do
            let pattern := o.fn.bindingBody!
            unless pattern.getAppFn == app.getAppFn && pattern.getAppNumArgs == app.getAppNumArgs do
              continue
            let saved ← getMCtx
            let hole ← mkFreshExprMVar o.domain
            let ok ← isDefEq app (pattern.instantiate1 hole)
            if ok then
              for (other, j) in apps do
                let other ← instantiateMVars other
                if other == app then continue
                let args := other.getAppArgs
                let data ← instantiateMVars args[j]!
                -- the observed argument may have any shape (for example a
                -- constructor of the decoded value); the other arguments are fixed
                let fixed := (args.eraseIdxIfInBounds j).all fun a => !a.hasMVar
                unless fixed do continue
                let domain ← instantiateMVars (← inferType data)
                if domain.hasMVar then continue
                let fn ← withLocalDeclD `x domain fun x =>
                  mkLambdaFVars #[x] (mkAppN other.getAppFn (args.set! j x))
                unless fn.hasMVar || found.any (·.fn == fn) || result.any (·.fn == fn) do
                  found := found.push {fn, domain}
            setMCtx saved
        return found
      result := result ++ found.filter fun f => !result.any (·.fn == f.fn)
    if result.size == before then break
  -- one observer per function: the domain spelled through abbreviations
  -- (`Value` and `List (Data × Data)`) is the same domain
  let mut out : Array Observer := #[]
  for o in result do
    let domain ← Smt.typeKey o.domain
    let fn := match o.fn with
      | .lam n _ b bi => Expr.lam n domain b bi
      | f => f
    unless out.any (·.fn == fn) do out := out.push {fn, domain}
  return out

/-- Memo of `isDefEq type domain` for observation assignment (types repeat
across thousands of cut variables). -/
private initialize domainMatches : IO.Ref (Std.HashMap (Expr × Expr) Bool) ← IO.mkRef {}

private def matchesDomain (ty domain : Expr) : MetaM Bool := do
  if let some r := (← domainMatches.get)[(ty, domain)]? then return r
  let r ← isDefEq ty domain
  domainMatches.modify (·.insert (ty, domain) r)
  return r

/-- Observation terms of a cut point. -/
def cutObservations (vars : Array Expr) (observers : Array Observer) (rootObs : Array Expr)
    (scalarRoots : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for v in vars do
    let declared ← inferType v
    let ty ← whnf declared
    if ← isScalarType ty then out := out.push v; continue
    -- a carried value (a byte string, a credential) held apart from the roots:
    -- whether it is one of the roots of its type (the key a step compared)
    if !(scalarRoots.contains v) then
      if ← isCarriedType ty then
        for r in scalarRoots do
          if ← matchesDomain (← inferType r) declared then
            try out := out.push (← mkDecide (← mkEq v r)) catch _ => pure ()
    -- a record (non-recursive, one constructor): observe its fields
    if let .const n _ := ty.getAppFn then
      if let some info := getStructureInfo? (← getEnv) n then
        if (← inductiveType? ty).any (!·.isRec) then
          for i in [0:info.fieldNames.size] do
            let field ← try mkProjection v info.fieldNames[i]! catch _ => continue
            let fty ← whnf (← inferType field)
            if ← isScalarType fty then out := out.push field; continue
            for o in observers do
              if ← matchesDomain fty o.domain then out := out.push (o.fn.beta #[field])
    for o in observers do
      -- compare the declared type too: an abbreviation (`Value`) and its
      -- weak-head normal form need not unify under the caller's transparency
      if (← matchesDomain declared o.domain) || (← matchesDomain ty o.domain) then
        out := out.push (o.fn.beta #[v])
  for r in rootObs ++ scalarRoots do
    unless out.contains r do out := out.push r
  -- the same observation may arise from several observers
  let mut seen : Std.HashSet Expr := {}
  let mut uniq := #[]
  for o in out do
    unless seen.contains o do
      seen := seen.insert o
      uniq := uniq.push o
  return uniq

/-! ## Unfolding observations at known constructors -/

/-- Whether `e` is a match or recursor application that does not reduce. -/
def isStuckMatch (e : Expr) : MetaM Bool := do
  if (← matchMatcherApp? e (alsoCasesOn := true)).isSome then return true
  match e.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.recInfo _) => return true
    | _ => return false
  | _ => return false

/-- Beta-reduce every redex (repeatedly, as a reduct may expose another). -/
partial def betaAll (e : Expr) : Expr :=
  let e' := e.replace fun t => if t.isHeadBetaTarget then some (betaAll t.headBeta) else none
  e'

/-- Unfold an observation application whose recursion argument is a known
constructor: delta, then structural reduction. The result is kept only when it
is not stuck on an unknown value. -/
partial def unfoldObsCore (e : Expr) (fuel : Nat := 4) : MetaM Expr := do
  if fuel == 0 then return e
  let .const fn _ := e.getAppFn | return e
  if (← getEnv).find? fn |>.any (·.isCtor) then return e
  -- a match on a constructor (`match some v with …`) reduces; other definitions unfold
  let e1? ← if isMatcherCore (← getEnv) fn then do
      let r ← whnfCore e
      pure (if r == e then none else some r)
    else unfoldDefinition? e
  let some e1 := e1? | return e
  -- structure literals read through projections (`{ … }.txInfoOutputs`) as their fields
  let e2 ← Blaster.Proof.Explore.projReduce (← whnfCore e1)
  if e2 == e || (← isStuckMatch e2) then return e
  let e3 ← unfoldObsCore e2 (fuel - 1)
  -- the step of a higher-order check applies its predicate: `(fun x => E x) h`
  return betaAll e3

private initialize unfoldObsMemo : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

/-- `unfoldObsCore`, memoized. -/
def unfoldObs (e : Expr) : MetaM Expr := do
  if let some r := (← unfoldObsMemo.get)[e]? then return r
  let r ← unfoldObsCore e
  unfoldObsMemo.modify (·.insert e r)
  return r

/-! ## Clause encoding -/

open Smt in
/-- Encode the application of relation `rel` (see `Problem.procs`) to `args`. -/
def relApp (rel : Nat) (args : Array Expr) : EncM Houdini.App := do
  let mut xs := #[]
  -- observations get the depth to read a nested constructor pattern (a datum
  -- `Constr _ (B h :: _)`: an option, a constructor, its list, its head) and
  -- their own (small) case-split budget
  for a in args do
    let a' ← Smt.inMeta (unfoldObs a)
    modify fun (l : Smt.Local) => {l with splits := Smt.splitBudget - 16, allowSplit := true}
    let x ← match ← enc a' 24 with
      | some x => pure x
      | none => pure "0"
    modify fun (l : Smt.Local) => {l with allowSplit := false}
    xs := xs.push x
  return {rel, args := xs}

/-- The Horn query of a plan: a relation per cut point and per procedure
summary, over observations. -/
structure Problem where
  plan : Plan
  /-- Observations of every cut point (without ghost arguments). -/
  observations : Array (Array Expr)
  /-- Entry template ↦ entry observations, exit observations, ghost placeholders. -/
  obsIn : Std.HashMap Nat (Array Expr)
  obsOut : Std.HashMap Nat (Array Expr)
  ghosts : Std.HashMap Nat (Array Expr)
  /-- The entry templates of the procedures. Cut `c` has relation `c`, the
  summary of procedure `procs[k]` relation `plan.cuts.size + k`. -/
  procs : Array Nat
  /-- Proved closed facts `∀ xs, premise → conclusion`, instantiated at the
  observation terms of each clause. -/
  facts : Array Expr := #[]

/-- The relation of the summary of the procedure entered at template `e`. -/
def Problem.post (prob : Problem) (e : Nat) : Nat := prob.plan.cuts.size + prob.procs.idxOf e

open Smt in
/-- The SMT sort of an observation. -/
def sortOfObs (o : Expr) : EncM String := do
  let ty ← Smt.inMeta (do whnf (← inferType o))
  if ty.isConstOf ``Bool then return "Bool"
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then return "Int"
  -- a carried value of a data type (a byte string, a credential)
  return (← Smt.sortOf ty).getD "Int"

/-- Ghost arguments of cut `c`'s relation: the region's entry observations for
inner cut points, nothing otherwise. -/
def Problem.ghostArgs (prob : Problem) (c : Nat) : Array Expr :=
  let ci := prob.plan.cuts[c]!
  if ci.inner then prob.ghosts.getD ci.entry?.get! #[] else #[]

/-- Subterms of `e` with the same head and arity as `t`. -/
partial def subtermsLike (e t : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isApp && e.getAppFn == t.getAppFn && e.getAppNumArgs == t.getAppNumArgs &&
      !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app f a => subtermsLike a t (subtermsLike f t acc)
  | .lam _ d b _ | .forallE _ d b _ => subtermsLike b t (subtermsLike d t acc)
  | .mdata _ b | .proj _ _ b => subtermsLike b t acc
  | .letE _ d v b _ => subtermsLike b t (subtermsLike v t (subtermsLike d t acc))
  | _ => acc

/-- Constant-headed applications in `e` without loose bound variables. -/
partial def appSubterms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isApp && e.getAppFn.isConst && !e.hasLooseBVars then
    acc.push e else acc
  match e with
  | .app .. => e.getAppArgs.foldl (fun acc a => appSubterms a acc) acc
  | .forallE _ d b _ => appSubterms b (appSubterms d acc)
  | .mdata _ b | .proj _ _ b => appSubterms b acc
  | _ => acc

/-- Head symbols (with arity) of the applications in a fact's conclusion: a term
can only match the conclusion when its own head is among them. -/
private initialize conclusionHeads : IO.Ref (Std.HashMap Expr (Std.HashSet (Name × Nat))) ←
  IO.mkRef {}

private def headsOf (f : Expr) : MetaM (Std.HashSet (Name × Nat)) := do
  if let some hs := (← conclusionHeads.get)[f]? then return hs
  let fty ← inferType f
  let hs ← forallTelescopeReducing fty fun _ body => do
    let concl := body.getForallBody
    let acc ← IO.mkRef ({} : Std.HashSet (Name × Nat))
    concl.forEach fun t => do
      if t.isApp then
        if let .const n _ := t.getAppFn then
          -- logical structure matches every clause equation: not a key
          unless #[``Eq, ``Iff, ``And, ``Or, ``Not, ``HEq, ``Ne].contains n do
            acc.modify (·.insert (n, t.getAppNumArgs))
    acc.get
  conclusionHeads.modify (·.insert f hs)
  return hs

/-- Premise matches known to fail, across clauses: `(pattern, candidate)` with
the pattern's open values abstracted (`abstractMVars`, types included), so the
key does not mention the clause's metavariables. `isDefEq` is a function of
the two terms and of the (shared, append-only) local context, so a pair that
failed once fails again; only `false` results are recorded (exceptions and
successes are not). Most failing pairs are decided only after unfolding both
heads, which dominated the instantiation time. -/
private initialize premiseFail : IO.Ref (Std.HashSet (Expr × Expr)) ← IO.mkRef {}

/-- `isDefEq pat t` for a premise pattern `pat` whose key is `patKey`,
skipping (and recording) pairs known to fail. -/
def premiseDefEq (patKey pat t : Expr) : MetaM Bool := do
  let key := (patKey, t)
  if (← premiseFail.get).contains key then return false
  let saved ← getMCtx
  if ← isDefEq pat t then return true
  setMCtx saved
  premiseFail.modify (·.insert key)
  return false

/-- Hypothesis-independent conclusion matches: `(fact, term) ↦` the matched
implication with its open values abstracted. -/
private initialize factConcl :
    IO.Ref (Std.HashMap (Expr × Expr × Array Expr) (Array AbstractMVarsResult)) ← IO.mkRef {}

/-- Forget the memo tables of this module. They are valid for one exploration
(its environment and reducibility settings) and hold its expressions, so each
exploration starts without them. -/
def clearCaches : IO Unit := do
  domainMatches.set {}
  unfoldObsMemo.set {}
  conclusionHeads.set {}
  premiseFail.set {}
  factConcl.set {}

/-- The free variables of `e` in order of first occurrence. -/
def fvarsInOrder (e : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet FVarId := {}
  for t in (collectFVars {} e).fvarIds do
    unless seen.contains t do
      seen := seen.insert t
      out := out.push (.fvar t)
  return out

/-- A cheap key for premise/hypothesis matching: the head of an equation's left
side (or of the proposition). -/
def premiseKey (ty : Expr) : Name :=
  let t := match ty.eq? with | some (_, lhs, _) => lhs | none => ty
  match t.getAppFn with
  | .const n _ => n
  | .mvar _ => .anonymous
  | _ => `other

/-- `a ≤ b` as `(type, a, b)`. -/
def leOf? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``LE.le 4 then some (e.getArg! 0, e.getArg! 2, e.getArg! 3)
  else if e.isAppOfArity ``Int.le 2 then some (mkConst ``Int, e.getArg! 0, e.getArg! 1)
  else none

/-- Instances of proved facts whose conclusion mentions one of `terms`.
Quantified values not fixed by that match are fixed by matching the fact's
premises against the clause's own facts `hyps` (for example a decoding
premise `decode d = ok v` against the path's decoding equation). -/
def factInstances (facts : Array Expr) (terms : Array Expr) (hyps : Array Expr := #[])
    (allPremiseMatches : Bool := false) :
    MetaM (Array Expr) := do
  let mut out := #[]
  let mut outSet : Std.HashSet Expr := {}
  -- index the facts by the heads of their conclusions
  let mut byHead : Std.HashMap (Name × Nat) (Array Expr) := {}
  for f in facts do
    for h in ← headsOf f do
      byHead := byHead.insert h ((byHead.getD h #[]).push f)
  let mut seen : Std.HashSet Expr := {}
  -- the terms and their nested applications; then, for a few rounds, the
  -- applications inside new instances (a premise `ascending a` of one fact is
  -- the conclusion of another)
  let mut queue := terms.foldl (fun acc t => appSubterms t acc) #[]
  -- the clause's applications by head, for premises whose values they fix
  let mut termsByHead : Std.HashMap (Name × Nat) (Array Expr) := {}
  for u in queue do
    if u.hasLooseBVars then continue
    if let .const g _ := u.getAppFn then
      let k := (g, u.getAppNumArgs)
      let arr := termsByHead.getD k #[]
      if arr.size < 64 && !arr.contains u then termsByHead := termsByHead.insert k (arr.push u)
  let mut round := 0
  while !queue.isEmpty && round < 4 do
   round := round + 1
   let current := queue
   queue := #[]
   let before := out.size
   for t in current do
    if seen.contains t then continue
    seen := seen.insert t
    let .const tn _ := t.getAppFn | continue
    for f in byHead.getD (tn, t.getAppNumArgs) #[] do
       -- the conclusion match does not depend on the clause: cached, with the
       -- values it leaves open abstracted
       -- keyed by the term's shape: its free variables abstracted (with their
       -- types), so clauses that differ only in their variables share the match
       let fvs := fvarsInOrder t
       let key := (f, t.abstract fvs, ← fvs.mapM inferType)
       let concls ← match (← factConcl.get)[key]? with
         | some r => pure r
         | none => do
           let fty ← inferType f
           -- every conclusion subterm the term unifies with gives an instance
           let r ← withNewMCtxDepth do
             let (_, _, body0) ← forallMetaTelescopeReducing fty
             let cands := subtermsLike body0 t
             let mut found := #[]
             for i in [0:cands.size] do
               let saved ← getMCtx
               let (xs, _, body) ← forallMetaTelescopeReducing fty
               let cands' := subtermsLike body t
               if h : i < cands'.size then
                 if ← isDefEq cands'[i] t then
                   let mut inst ← instantiateMVars body
                   for x in xs.reverse do
                     let ty ← instantiateMVars (← inferType x)
                     if ← isProp ty then inst := mkForall `h .default ty inst
                   let r ← abstractMVars inst
                   found := found.push {r with expr := r.expr.abstract fvs}
               setMCtx saved
             return found
           factConcl.modify (·.insert key r)
           pure r
       for r in concls do
         let instances ←
           if r.numMVars == 0 then pure #[r.expr.instantiateRev fvs]
           else withNewMCtxDepth do
             let (_, _, imp0) ← openAbstractMVarsResult r
             let imp := imp0.instantiateRev fvs
             -- premises: kept as hypotheses of the instance; values they alone
             -- fix are fixed by matching them against the clause's own facts
             -- premises with open values: first all against the clause's own
             -- facts, then (for those still open) against the clause's terms
             let mut prems : Array Expr := #[]
             let mut rest := imp
             while rest.isForall do
               prems := prems.push rest.bindingDomain!
               rest := rest.bindingBody!
             -- A condition may contain several selections from the same list.
             -- Replay must retain each matching selection, not only the first.
             -- Bound branching; every result is still a theorem instance.
             let mut states := #[(← getMCtx)]
             for pr in prems do
               let mut next := #[]
               for state in states do
                 setMCtx state
                 let ty ← instantiateMVars pr
                 if !ty.hasMVar then
                   next := next.push state
                   continue
                 let key := premiseKey ty
                 let tyKey := (← abstractMVars ty).expr
                 let mut matched := false
                 for h in hyps do
                   unless key == .anonymous || premiseKey h == key do continue
                   setMCtx state
                   if ← premiseDefEq tyKey ty h then
                     next := next.push (← getMCtx)
                     matched := true
                     if !allPremiseMatches || next.size ≥ 64 then break
                 unless matched do next := next.push state
                 if next.size ≥ 64 then break
               states := next
             let mut instances := #[]
             for state in states do
               setMCtx state
               for pr in prems do
                 let ty ← instantiateMVars pr
                 unless ty.hasMVar do continue
                 if let some (_, lhs, _) := ty.eq? then
                   if let .const g _ := lhs.getAppFn then
                     let lhsKey := (← abstractMVars lhs).expr
                     for u in termsByHead.getD (g, lhs.getAppNumArgs) #[] do
                       if ← premiseDefEq lhsKey lhs u then break
               let inst ← instantiateMVars imp
               unless inst.hasMVar || instances.contains inst do
                 instances := instances.push inst
             return instances
         for i in instances do
           unless outSet.contains i do
             outSet := outSet.insert i; out := out.push i
   for inst in out.extract before out.size do
     for t in appSubterms inst do
       unless seen.contains t do queue := queue.push t
  -- congruence-shaped facts (`f … xs = f … ys`): instantiate at pairs of terms
  let byHeadT : Std.HashMap (Name × Nat) (Array Expr) := seen.toArray.foldl (init := {}) fun m t =>
    match t.getAppFn with
    | .const n _ => m.insert (n, t.getAppNumArgs) ((m.getD (n, t.getAppNumArgs) #[]).push t)
    | _ => m
  for f in facts do
    let fty ← inferType f
    let shape? ← forallTelescopeReducing fty fun _ body => do
      let (l, r) ← match body.eq?, leOf? body with
        | some (_, l, r), _ => pure (l, r)
        | none, some (_, l, r) => pure (l, r)
        | _, _ => return none
      let .const ln _ := l.getAppFn | return none
      let .const rn _ := r.getAppFn | return none
      if ln == rn && l.getAppNumArgs == r.getAppNumArgs then return some (ln, l.getAppNumArgs) else return none
    let some key := shape? | continue
    -- terms applied to a list in cons form (directly, or through a definition
    -- that unfolds to one), where congruence matters
    let consForm (a : Expr) : MetaM Bool := do
      if a.isAppOf ``List.cons then return true
      unless a.isApp && a.getAppFn.isConst do return false
      return (← try unfoldDefinition? a catch _ => pure none).any (·.isAppOf ``List.cons)
    let ts ← (byHeadT.getD key #[]).filterM fun t => t.getAppArgs.anyM consForm
    if ts.size < 2 || ts.size > 40 then continue
    for t1 in ts do
      for t2 in ts do
        if t1 == t2 then continue
        let inst? ← withNewMCtxDepth do
          let (xs, _, body) ← forallMetaTelescopeReducing fty
          let (l, r) ← match body.eq?, leOf? body with
            | some (_, l, r), _ => pure (l, r)
            | none, some (_, l, r) => pure (l, r)
            | _, _ => return none
          unless ← isDefEq l t1 do return none
          unless ← isDefEq r t2 do return none
          let mut inst ← instantiateMVars body
          for x in xs.reverse do
            let ty ← instantiateMVars (← inferType x)
            if ← isProp ty then inst := mkForall `h .default ty inst
          if inst.hasMVar then return none
          return some inst
        if let some i := inst? then
          unless outSet.contains i do
            outSet := outSet.insert i; out := out.push i
  return out

/-- Reduce a path equation's dispatch after its arguments have acquired
constructor values. Keep recursive operation calls folded for fact matching. -/
def normalizeFact (e : Expr) : MetaM Expr := do
  let some (ty, l, r) := e.eq? | return e
  let .const n _ := l.getAppFn | return e
  let env ← getEnv
  let args := l.getAppArgs
  -- the arguments the head dispatches on: reduced to constructors, then the
  -- dispatch (iota/beta) only; the program's own definitions stay folded
  let ctlIdx : Array Nat ← match env.find? n with
    | some (.recInfo rv) => pure #[rv.getMajorIdx]
    | _ =>
      if n == ``ite || n == ``dite then pure #[2]
      else if let some mi := Meta.getMatcherInfoCore? env n then
        pure ((List.range mi.numDiscrs).toArray.map (· + mi.numParams + 1))
      else pure #[]
  if ctlIdx.isEmpty then return e
  let mut args' := args
  for i in ctlIdx do
    if h : i < args'.size then
      let a := args'[i]
      let a' ← try withTransparency .default (whnf a) catch _ => pure a
      args' := args'.set! i a'
  let l' ← whnfCore (mkAppN l.getAppFn args')
  if l' == l then return e
  return mkApp3 (mkConst ``Eq [← getLevel ty]) ty l' r

/-- The substitution under which `clause` reads path `p` of cut `c`: the
cut's defining facts `x = C fields` (so that hypotheses over the roots
reduce), the path's own splits, and a nullary constructor that a path
condition singles out (`isEmpty l = true`: observations of `l` then reduce at
it; every constructor must decide the condition). -/
def clauseSubst (prob : Problem) (c : Nat) (p : Path) : MetaM Subst := do
  let ci := prob.plan.cuts[c]!
  let σ0 : Subst := ci.facts.foldl (init := {}) fun acc f =>
    match f.eq? with
    | some (_, .fvar x, rhs) => if rhs.getAppFn.isConst then acc.insert x rhs else acc
    | _ => acc
  let mut σ := p.subst.fold (init := σ0) fun acc k v => acc.insert k v
  for f in p.facts do
    let (pos, body) := match f.not? with
      | some b => (false, b)
      | none => (true, f)
    let some (_, lhs, rhs) := body.eq? | continue
    let want? := if rhs.isConstOf ``Bool.true then some pos
      else if rhs.isConstOf ``Bool.false then some !pos else none
    let some want := want? | continue
    let [x] := (collectFVars {} lhs).fvarIds.toList | continue
    if σ.contains x then continue
    let xty ← whnf (← inferType (.fvar x))
    let some (info, ctors) ← ctorTelescopes xty | continue
    let params := xty.getAppArgs.extract 0 info.numParams
    let ls := xty.getAppFn.constLevels!
    let mut hit : Option Expr := none
    let mut exact := true
    for (c, cty) in ctors do
      let r? ← forallTelescope cty fun fields _ => do
        let app := mkAppN (mkAppN (mkConst c ls) params) fields
        let v ← whnf (lhs.replaceFVar (.fvar x) app)
        if v.isConstOf ``Bool.true then return some (true, fields.isEmpty, app)
        if v.isConstOf ``Bool.false then return some (false, fields.isEmpty, app)
        return none
      match r? with
      | some (val, nullary, app) =>
        if val == want then
          if nullary && hit.isNone then hit := some app else exact := false
      | none => exact := false
    if exact then
      if let some app := hit then σ := σ.insert x app
  return σ

/-- The fact instances `clause` offers for path `p` of cut `c` under `σ`
(`clauseSubst`): the facts at the cut's observations, at its target's (a fact
about the updated state, the accumulator after an addition, is matched at the
target's terms) and at the summaries' results, and at the applications inside
the path's own conditions (a branch on an encoded comparison is linked to the
typed comparison by a fact about it). An instance concluding `x = t` (a
variable) also lets the others speak about `x` where they speak about `t`
(same premises): the program's own terms then meet the facts' terms. -/
def clauseInstances (prob : Problem) (c : Nat) (p : Path) (σ : Subst) : MetaM (Array Expr) := do
  if prob.facts.isEmpty then return #[]
  let ci := prob.plan.cuts[c]!
  let apply := fun (e : Expr) => Chc.applyFix σ e
  let target : Array Expr := match p.last with
    | .goto c' τ => prob.observations[c']!.map fun o => apply (Subst.apply τ o)
    | .call c' τ => prob.observations[c']!.map fun o => apply (Subst.apply τ o)
    | .exit τ => match ci.entry? with
      | some e => (prob.obsOut.getD e #[]).map fun o => apply (Subst.apply τ o)
      | none => #[]
    | _ => #[]
  let postTerms := p.posts.foldl (init := #[]) fun acc (q, σc, ρ) =>
    acc ++ (prob.obsOut.getD q #[]).map fun o => apply (Subst.apply ρ (Subst.apply σc o))
  let all := prob.observations[c]!.map apply ++ target ++ postTerms
  let terms ← all.mapM unfoldObs
  let hyps ← (p.facts ++ ci.facts).mapM fun f => normalizeFact (apply f)
  let hypTerms := hyps.foldl (init := #[]) fun acc h => appSubterms h acc
  let instances ← factInstances prob.facts (all ++ terms ++ hypTerms) hyps
  -- premises as an implication chain (non-dependent arrows)
  let rec split (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
    match e with
    | .forallE _ d b _ => if b.hasLooseBVars then (acc, e) else split b (acc.push d)
    | _ => (acc, e)
  let mut eqs : Array (Array Expr × Expr × Expr) := #[]
  for i in instances do
    let (prems, concl) := split i #[]
    if let some (_, l, r) := concl.eq? then
      if l.isFVar && !r.isFVar && !r.containsFVar l.fvarId! then eqs := eqs.push (prems, l, r)
      else if r.isFVar && !l.isFVar && !l.containsFVar r.fvarId! then eqs := eqs.push (prems, r, l)
  if eqs.isEmpty then return instances
  let mut extra := #[]
  for i in instances do
    for (prems, x, t) in eqs do
      if extra.size ≥ 200 then break
      if i.containsFVar x.fvarId! then continue
      unless (i.find? (· == t)).isSome do continue
      let mut j := i.replace fun s => if s == t then some x else none
      for prem in prems.reverse do j := mkForall `h .default prem j
      extra := extra.push j
  return instances ++ extra

open Smt in
/-- The Horn clause of path `p` of cut `c`, read under `σ` (`clauseSubst`),
with the fact instances `instances` (`clauseInstances`) as further facts. -/
def clause (prob : Problem) (c : Nat) (p : Path) (hyps goal : Expr) (σ : Subst)
    (instances : Array Expr) : EncM Houdini.Clause := do
  modify fun _ => ({} : Smt.Local)
  let ci := prob.plan.cuts[c]!
  let apply := fun (e : Expr) => Chc.applyFix σ e
  -- a fact generalized before its arguments were split may reduce now (an
  -- `if isEmpty (x :: xs) then … else g …` becomes `g …`): its left side is
  -- reduced once the substitution applies, so facts about `g` match it
  let normFact (e : Expr) : Smt.EncM Expr := Smt.inMeta (normalizeFact e)
  let own := prob.observations[c]!.map apply
  -- the region's ghost values: placeholders at inner cuts, entry observations at the entry
  let gvals := match ci.entry? with
    | some _ => if ci.inner then prob.ghostArgs c else own
    | none => #[]
  let body ← relApp c (prob.ghostArgs c ++ own)
  -- the head's observations first: they get the full case-split budget, and
  -- later hypotheses reuse their encodings
  let mut leafFacts : Array String := #[]
  let head ← match p.last with
    | .accept => Houdini.Head.goal <$> encProp (apply goal)
    | .leaf q => do
      leafFacts := leafFacts.push (← encProp (apply q))
      Houdini.Head.goal <$> encProp (apply goal)
    | .unreachable => pure (.goal "false")
    | .goto c' τ => do
      let args := prob.observations[c']!.map fun o => apply (Subst.apply τ o)
      let g := if prob.plan.cuts[c']!.inner then gvals else #[]
      .app <$> relApp c' (g ++ args)
    | .exit τ => do
      let e := ci.entry?.get!
      let outs := (prob.obsOut.getD e #[]).map fun o => apply (Subst.apply τ o)
      .app <$> relApp (prob.post e) (gvals ++ outs)
    | .call c' τ => do
      let args := prob.observations[c']!.map fun o => apply (Subst.apply τ o)
      .app <$> relApp c' args
  let mut premises := #[body]
  for (q, σc, ρ) in p.posts do
    let ins := (prob.obsIn.getD q #[]).map fun o => apply (Subst.apply σc o)
    let outs := (prob.obsOut.getD q #[]).map fun o => apply (Subst.apply ρ (Subst.apply σc o))
    premises := premises.push (← relApp (prob.post q) (ins ++ outs))
  let mut conj := leafFacts
  for f in p.facts do conj := conj.push (← encProp (← normFact (apply f)))
  for f in ci.facts do conj := conj.push (← encProp (apply f))
  conj := conj.push (← encProp (apply hyps))
  -- distinct instances often encode alike (their differences are abstracted
  -- to the same variables): each encoded conjunct once
  let mut seen : Std.HashSet String := Std.HashSet.ofArray conj
  for i in instances do
    let x ← encProp i
    if x == "true" then continue
    if seen.contains x then continue
    seen := seen.insert x
    conj := conj.push x
  let l ← get
  let facts := (conj ++ l.side).foldl (init := (#[], ({} : Std.HashSet String)))
    (fun (acc, seen) x => if seen.contains x then (acc, seen) else (acc.push x, seen.insert x)) |>.1
  return {vars := l.vars, premises, facts, head}

open Smt in
/-- The clause entering the root cut point: the hypotheses imply its relation. -/
def entryClause (prob : Problem) (hyps : Expr) (rootCut : Nat) (σ : Subst) : EncM Houdini.Clause := do
  modify fun _ => ({} : Smt.Local)
  let args := prob.observations[rootCut]!.map (Subst.apply σ)
  let head ← relApp rootCut args
  let h ← encProp hyps
  let l ← get
  return {vars := l.vars, premises := #[], facts := #[h] ++ l.side, head := .app head}

/-! ## Solver interaction and model translation -/

/-- An s-expression of a solver's answer or an invariant. -/
inductive SExpr where
  | atom : String → SExpr
  | list : Array SExpr → SExpr
deriving Inhabited

/-- The position after the whitespace and comments at `i`. -/
partial def skipWs (input : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < input.size do
    if input[j]!.isWhitespace then j := j + 1
    else if input[j]! == ';' then
      while j < input.size && input[j]! != '\n' do j := j + 1
    else break
  return j

/-- The s-expression at `i`, and the position after it. -/
partial def parseS (input : Array Char) (i : Nat) : Except String (SExpr × Nat) := do
  let i := skipWs input i
  if i ≥ input.size then throw "unexpected end"
  if input[i]! == '(' then
    let mut items := #[]
    let mut j := skipWs input (i + 1)
    while j < input.size && input[j]! != ')' do
      let (it, k) ← parseS input j
      items := items.push it
      j := skipWs input k
    return (.list items, j + 1)
  let mut j := i
  while j < input.size && !input[j]!.isWhitespace && input[j]! != '(' && input[j]! != ')' do j := j + 1
  return (.atom (String.mk (input.extract i j).toList), j)

/-- A function of a model: its parameters and body. -/
structure Def where
  params : Array String
  body : SExpr

/-- The functions of a model (`sat` and its `define-fun`s), by name. -/
def parseModel (out : String) : Except String (Std.HashMap String Def) := do
  let input := out.toList.toArray
  let (st, off) ← parseS input 0
  unless st matches .atom "sat" do throw "no sat"
  let (.list entries, _) ← parseS input off | throw "model is not a list"
  let mut res := {}
  for e in entries do
    let .list fs := e | continue
    unless fs.size == 5 do continue
    let .atom "define-fun" := fs[0]! | continue
    let .atom name := fs[1]! | continue
    let .list ps := fs[2]! | continue
    let names := ps.filterMap fun p => match p with
      | .list #[.atom n, _] => some n
      | _ => none
    res := res.insert name {params := names, body := fs[4]!}
  return res

/-- `a < b` over `Int`. -/
def mkIntLT' (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LT.lt [levelZero]) (mkConst ``Int) (mkConst ``Int.instLTInt) a b

/-- `e` as a proposition (`e = true` for a Boolean). -/
def asProp (e : Expr) : MetaM Expr := do
  if ← isProp e then return e
  if (← whnf (← inferType e)).isConstOf ``Bool then return ← mkEq e (mkConst ``Bool.true)
  throwError "chc model: expected a Boolean expression"

/-- `e` as an integer (cast from `Nat`). -/
def asInt (e : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isConstOf ``Nat then return mkIntNatCast e
  if ty.isConstOf ``Int then return e
  throwError "chc model: expected an integer expression"

/-- The Lean proposition or integer the model term `s` denotes, with the
symbols `b` bound and the model's functions `defs` applied. -/
partial def interp (defs : Std.HashMap String Def) (b : Std.HashMap String Expr) (s : SExpr) (depth : Nat := 200) :
    MetaM Expr := do
  if depth == 0 then throwError "chc model: too deep"
  match s with
  | .atom "true" => return mkConst ``True
  | .atom "false" => return mkConst ``False
  | .atom a =>
    if let some e := b[a]? then return e
    if let some n := a.toInt? then return mkIntLit n
    throwError "chc model: unknown symbol {a}"
  | .list items =>
    let some (SExpr.atom op) := items[0]? | throwError "chc model: bad operator"
    if op == "let" then
      let (some (SExpr.list bs), some body) := (items[1]?, items[2]?) | throwError "chc model: bad let"
      let mut b' := b
      for x in bs do
        let .list #[.atom n, v] := x | throwError "chc model: bad binding"
        b' := b'.insert n (← interp defs b v (depth - 1))
      return ← interp defs b' body (depth - 1)
    let args ← items[1:].toArray.mapM (interp defs b · (depth - 1))
    -- (a model the solver or a file gives can be malformed: never index past its arguments)
    let arity (n : Nat) : MetaM Unit := do
      unless args.size == n do throwError "chc model: `{op}` applied to {args.size} arguments"
    -- SMT-LIB chains comparisons (`(< a b c)` is `a < b ∧ b < c`) and folds
    -- arithmetic (`(- a b c)` is `(a - b) - c`) and implication (to the right)
    let chain (rel : Expr → Expr → MetaM Expr) : MetaM Expr := do
      if args.size < 2 then throwError "chc model: `{op}` applied to {args.size} arguments"
      let mut out ← rel args[0]! args[1]!
      for i in [2:args.size] do out := mkAnd out (← rel args[i - 1]! args[i]!)
      return out
    let fold (f : Expr → Expr → Expr) : MetaM Expr := do
      let some first := args[0]? | throwError "chc model: `{op}` applied to no arguments"
      args[1:].foldlM (init := ← asInt first) fun r a => do return f r (← asInt a)
    let equal (x y : Expr) : MetaM Expr := do
      if (← isProp x) || (← whnf (← inferType x)).isConstOf ``Bool then
        return mkApp2 (mkConst ``Iff) (← asProp x) (← asProp y)
      let ty ← whnf (← inferType x)
      unless ty.isConstOf ``Int || ty.isConstOf ``Nat do return ← mkEq x y
      return mkIntEq (← asInt x) (← asInt y)
    match op with
    | "and" => do
      let ps ← args.mapM asProp
      if ps.isEmpty then return mkConst ``True
      return ps.pop.foldr (fun a acc => mkAnd a acc) ps.back!
    | "or" => do
      let ps ← args.mapM asProp
      if ps.isEmpty then return mkConst ``False
      return ps.pop.foldr (fun a acc => mkOr a acc) ps.back!
    | "not" => arity 1; return mkNot (← asProp args[0]!)
    | "=>" =>
      if args.size < 2 then throwError "chc model: `=>` applied to {args.size} arguments"
      let ps ← args.mapM asProp
      ps.pop.foldrM (init := ps.back!) fun p acc => mkArrow p acc
    | "=" => chain equal
    | "<" => chain fun x y => do return mkIntLT' (← asInt x) (← asInt y)
    | "<=" => chain fun x y => do return mkIntLE (← asInt x) (← asInt y)
    | ">" => chain fun x y => do return mkIntLT' (← asInt y) (← asInt x)
    | ">=" => chain fun x y => do return mkIntLE (← asInt y) (← asInt x)
    | "+" => fold mkIntAdd
    | "-" => if args.size == 1 then return mkIntNeg (← asInt args[0]!) else fold mkIntSub
    | "*" => fold mkIntMul
    | "ite" =>
      arity 3
      let c ← asProp args[0]!
      if ← isProp args[1]! then
        return mkOr (mkAnd c (← asProp args[1]!)) (mkAnd (mkNot c) (← asProp args[2]!))
      mkAppM ``ite #[c, ← asInt args[1]!, ← asInt args[2]!]
    | _ =>
      if let some d := defs[op]? then
        arity d.params.size
        let b' := Std.HashMap.ofList (d.params.zip args).toList
        return ← interp defs b' d.body (depth - 1)
      throwError "chc model: unsupported operator {op}"

/-- Proposed invariants (one per cut point) and procedure postconditions (by
entry template), with the ghost placeholders they mention and their values. -/
structure Proposal where
  invs : Array Expr
  posts : Std.HashMap Nat Expr
  ghostVars : Std.HashMap Nat (Array Expr)
  ghostVals : Std.HashMap Nat (Array Expr)

/-- The goal-directed observers, as functions of the observed value (for fact discovery). -/
def observerPatterns (hyps goal : Expr) (isRoot : FVarId → Bool) (facts : Array Expr := #[]) :
    ExM (Array Expr) := do
  let (obsFns, _) ← inCtx do observers (← unfoldProps #[goal, hyps]) isRoot
  let obsFns ← inCtx (transport facts obsFns)
  return obsFns.map (·.fn)

/-- Boolean conjuncts of `e` (through `&&`). -/
partial def boolConjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``and 2 then boolConjuncts e.appArg! (boolConjuncts e.appFn!.appArg! acc)
  else acc.push e

/-- Element observers of list observers: `f (x :: xs)` unfolds to a
combination of a contribution of `x` and `f xs` (the quantity one input adds to
a sum, the test one element passes). The maximal scalar subterms mentioning `x`
but not `xs` observe single elements, so a state that holds an element apart
from its list (the input being processed) keeps that element's contribution. -/
def elementObservers (known : Array Observer) : MetaM (Array Observer) := do
  let mut out := #[]
  for o in known do
    let dom ← whnf o.domain
    unless dom.isAppOfArity ``List 1 do continue
    let α := dom.appArg!
    let found ← withLocalDeclD `x α fun x => withLocalDeclD `xs dom fun xs => do
      let cons ← mkAppM ``List.cons #[x, xs]
      let e := o.fn.beta #[cons]
      let e' ← unfoldObsCore e
      if e' == e then return (#[] : Array (Expr × Expr))
      let subs ← IO.mkRef (#[] : Array Expr)
      let rec visit (t : Expr) : MetaM Unit := do
        if t.hasLooseBVars || !t.containsFVar x.fvarId! then return
        if !t.containsFVar xs.fvarId! && t != x && t.isApp then
          if ← isScalarType (← inferType t) then
            unless (← subs.get).contains t do subs.modify (·.push t)
            return
        match t with
        | .app f a => visit f; visit a
        | .mdata _ b => visit b
        | _ => return
      visit e'
      let elems ← (← subs.get).mapM fun t => do return (← mkLambdaFVars #[x] t, α)
      -- the recursive data an element check walks (`hasCurrencySymbol c
      -- x.value`), observed on its own with the rest of the check fixed: a
      -- loop over that data keeps what the check will find
      let mut nested : Array (Expr × Expr) := #[]
      let inner ← IO.mkRef (#[] : Array Expr)
      for t0 in ← subs.get do
        -- every scalar read inside the element check (`lovelaceOf x.value` under `&&`, `≤`)
        t0.forEach fun s => do
          unless s.isApp && !s.hasLooseBVars && s.getAppFn.isConst do return
          if ← isScalarType (← inferType s) then
            unless (← inner.get).contains s do inner.modify (·.push s)
      for t in ← inner.get do
        let .const _ _ := t.getAppFn | continue
        let args := t.getAppArgs
        for i in [0:args.size] do
          let a := args[i]!
          unless a.containsFVar x.fvarId! do continue
          let others := args.eraseIdxIfInBounds i
          if others.any fun o => o.containsFVar x.fvarId! || o.containsFVar xs.fvarId! then continue
          let aty ← whnf (← inferType a)
          let some info ← inductiveType? aty | continue
          unless info.isRec || info.isNested do continue
          let fn ← withLocalDeclD `v aty fun v => mkLambdaFVars #[v] (mkAppN t.getAppFn (args.set! i v))
          unless nested.any (·.1 == fn) do nested := nested.push (fn, aty)
      -- each conjunct of an element check on its own (`address = seller`,
      -- `lovelace ≥ price`): the program tests them at different points
      let mut conj : Array (Expr × Expr) := #[]
      for t in ← subs.get do
        for c in boolConjuncts t do
          if c != t && c.containsFVar x.fvarId! && !c.containsFVar xs.fvarId! then
            let fn ← mkLambdaFVars #[x] c
            unless conj.any (·.1 == fn) do conj := conj.push (fn, α)
      return elems ++ nested ++ conj
    for (fn, domain) in found.toList.take 6 do
      unless out.any (·.fn == fn) || known.any (·.fn == fn) do
        out := out.push {fn, domain}
  return out

/-- Universal observers of recursive checks: a recursive Boolean function `f`
over a list whose step at `x :: xs` requires a condition `E x` of the element
alone (`validTxOutValue x.value` in an input-list check) gives the observer
`fun l => l.all E` and the element observer `E`, together with the candidate
fact `f … l … = true → l.all E = true`. A state that holds a suffix of the list,
or one element of it, keeps what the check established about it. Only lists of
the element types in `domains` are considered. -/
def allObservers (props : Array Expr) (domains : Array Expr) :
    MetaM (Array (Observer × Observer × Expr)) := do
  let mut out := #[]
  let mut consts : Std.HashSet Name := {}
  for p in props do
    for c in p.getUsedConstants do consts := consts.insert c
  for f in consts.toArray do
    let some (.defnInfo info) := (← getEnv).find? f | continue
    unless info.levelParams.isEmpty do continue
    unless ← isRecursiveDefinition f do continue
    let found ← forallTelescopeReducing info.type fun params result => do
      unless (← whnf result).isConstOf ``Bool do return #[]
      let mut found := #[]
      for i in [0:params.size] do
        let dom ← whnf (← inferType params[i]!)
        unless dom.isAppOfArity ``List 1 do continue
        let α := dom.appArg!
        if params.any fun q => α.containsFVar q.fvarId! then continue
        unless ← domains.anyM (isDefEq α ·) do continue
        let r? ← withLocalDeclD `x α fun x => withLocalDeclD `xs dom fun xs => do
          let cons ← mkAppM ``List.cons #[x, xs]
          let e := mkAppN (mkConst f) (params.set! i cons)
          let e' ← unfoldObsCore e
          if e' == e then return none
          let others := params.push xs
          let cs := (boolConjuncts e').filter fun c =>
            !c.hasLooseBVars && c.containsFVar x.fvarId! && !others.any (c.containsFVar ·.fvarId!)
          if cs.isEmpty then return none
          let mut body := cs[0]!
          for c in cs[1:] do body := mkApp2 (mkConst ``and) body c
          let E ← mkLambdaFVars #[x] body
          let fn ← withLocalDeclD `l dom fun l => do mkLambdaFVars #[l] (← mkAppM ``List.all #[l, E])
          let premise ← mkEq (mkAppN (mkConst f) params) (mkConst ``Bool.true)
          let concl ← mkEq (← mkAppM ``List.all #[params[i]!, E]) (mkConst ``Bool.true)
          let fact ← mkForallFVars params (← mkArrow premise concl)
          return some (({fn, domain := dom} : Observer), ({fn := E, domain := α} : Observer), fact)
        if let some r := r? then found := found.push r
      return found
    for r in found do
      -- the same universal observer may come from several checks: keep each
      -- check's linking fact
      unless out.any (·.2.2 == r.2.2) do out := out.push r
  return out

/-- Boolean disjuncts of `e` (through `||`). -/
partial def disjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``or 2 then disjuncts e.appArg! (disjuncts e.appFn!.appArg! acc)
  else acc.push e

/-- Membership facts of existential checks: a recursive Boolean function `f`
over a list whose step at `x :: xs` holds when a condition `E x` of the element
(and the other arguments) holds (`current x || f xs`) satisfies
`List.drop n l = x :: rest → E x = true → f … l = true`. A program that
selects an element by index (`headList (drop n l)`) and checks the condition
on it has thereby established `f … l`. Candidates only; each is proved. -/
def anyCandidates (props : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  let mut consts : Std.HashSet Name := {}
  for p in props do
    for c in p.getUsedConstants do consts := consts.insert c
  for f in consts.toArray do
    let some (.defnInfo info) := (← getEnv).find? f | continue
    unless info.levelParams.isEmpty do continue
    unless ← isRecursiveDefinition f do continue
    let found ← forallTelescopeReducing info.type fun params result => do
      unless (← whnf result).isConstOf ``Bool do return #[]
      let mut found := #[]
      for i in [0:params.size] do
        let dom ← whnf (← inferType params[i]!)
        unless dom.isAppOfArity ``List 1 do continue
        let α := dom.appArg!
        if params.any fun q => α.containsFVar q.fvarId! then continue
        let r? ← withLocalDeclD `x α fun x => withLocalDeclD `rest dom fun rest => do
          let cons ← mkAppM ``List.cons #[x, rest]
          let e := mkAppN (mkConst f) (params.set! i cons)
          let e' ← unfoldObsCore e
          if e' == e then return none
          let ds := (disjuncts e').filter fun d =>
            !d.hasLooseBVars && d.containsFVar x.fvarId! && !d.containsFVar rest.fvarId! &&
              !d.containsFVar params[i]!.fvarId!
          if ds.isEmpty || (disjuncts e').size < 2 then return none
          let mut body := ds[0]!
          for d in ds[1:] do body := mkApp2 (mkConst ``or) body d
          withLocalDeclD `n (mkConst ``Nat) fun n => do
            let dropEq ← mkEq (← mkAppM ``List.drop #[n, params[i]!]) cons
            let holds ← mkEq body (mkConst ``Bool.true)
            let concl ← mkEq (mkAppN (mkConst f) params) (mkConst ``Bool.true)
            let stmt ← mkArrow dropEq (← mkArrow holds concl)
            let binders := (params.push n).push x |>.push rest
            return some (← mkForallFVars binders stmt)
        if let some r := r? then found := found.push r
      return found
    out := out ++ found
  return out

/-- Element observers of existential checks applied to the roots: for a
hypothesis application `f a… l` of a recursive Boolean function whose step is
`E x || f … xs`, the observer `fun x => E x` (with the application's other
arguments). A state that holds an element selected from `l` keeps whether it
satisfies the condition, which the membership fact fixes where it is selected. -/
def anyElementObservers (props : Array Expr) (isRoot : FVarId → Bool) : MetaM (Array Observer) := do
  let apps ← IO.mkRef (#[] : Array Expr)
  for p in props do
    p.forEach fun t => do
      unless t.isApp && !t.hasLooseBVars do return
      let .const f _ := t.getAppFn | return
      unless (← apps.get).contains t do
        if (← isRecursiveDefinition f) then apps.modify (·.push t)
  let mut out := #[]
  for t in ← apps.get do
    unless (← whnf (← inferType t)).isConstOf ``Bool do continue
    let args := t.getAppArgs
    for i in [0:args.size] do
      let dom ← whnf (← inferType args[i]!)
      unless dom.isAppOfArity ``List 1 do continue
      let others := args.eraseIdxIfInBounds i
      unless others.all fun o => (collectFVars {} o).fvarIds.all isRoot do continue
      let α := dom.appArg!
      let fn? ← withLocalDeclD `x α fun x => withLocalDeclD `xs dom fun xs => do
        let cons ← mkAppM ``List.cons #[x, xs]
        let e := mkAppN t.getAppFn (args.set! i cons)
        let e' ← unfoldObsCore e
        if e' == e then return none
        let all := disjuncts e'
        if all.size < 2 then return none
        let ds := all.filter fun d =>
          !d.hasLooseBVars && d.containsFVar x.fvarId! && !d.containsFVar xs.fvarId!
        if ds.isEmpty then return none
        let mut body := ds[0]!
        for d in ds[1:] do body := mkApp2 (mkConst ``or) body d
        -- also one observer per conjunct of the condition (the rest of its
        -- structure, e.g. the matches around it, kept): a state between two
        -- of the program's checks relates to the parts separately
        let mut fns := #[← mkLambdaFVars #[x] body]
        let chain? := body.find? fun t => t.isAppOfArity ``and 2
        if let some chain := chain? then
          for c in boolConjuncts chain do
            let b' := body.replace fun t => if t == chain then some c else none
            unless b'.hasLooseBVars && !body.hasLooseBVars do
              fns := fns.push (← mkLambdaFVars #[x] b')
        return some fns
      if let some fns := fn? then
        for fn in fns do
          unless out.any (·.fn == fn) do out := out.push {fn, domain := α}
  return out

/-- The list element types observed by the goal's own list observers. -/
def goalElementTypes (goal : Expr) (isRoot : FVarId → Bool) : MetaM (Array Expr) := do
  let (fromGoal, _) ← observers (← unfoldProps #[goal]) isRoot (context := true)
  let mut out := #[]
  for o in fromGoal do
    let dom ← whnf o.domain
    if dom.isAppOfArity ``List 1 then
      unless ← out.anyM (isDefEq dom.appArg! ·) do out := out.push dom.appArg!
  return out

/-- Does `t` (with its non-recursive definitions unfolded, bounded) walk the
variable `v` with the recursive check `f`: apply `f` to `v`, or match on `v`
with an alternative that applies `f` (`match l with | x :: xs => … f xs …`)? -/
def walksWith (t : Expr) (f : Name) (v : FVarId) : MetaM Bool := do
  let env ← getEnv
  for u in ← unfoldProps #[t] do
    let hit := u.find? fun s =>
      match s.getAppFn with
      | .const n _ =>
        if n == f then s.getAppArgs.any (· == .fvar v)
        else match Meta.getMatcherInfoCore? env n with
          | some mi =>
            let args := s.getAppArgs
            let discrs := args.extract (mi.numParams + 1) (mi.numParams + 1 + mi.numDiscrs)
            discrs.any (· == .fvar v) && (s.find? (·.getAppFn.isConstOf f)).isSome
          | none => false
      | _ => false
    if hit.isSome then return true
  return false

/-- Candidate facts for the universal observers: the recursive check implies
the universal statement, and every root observation that mentions a list the
observer applies to implies it at that list (`validInputs ctx` unfolded to a
match on `ctx.inputs`). Closed; each must be proved before use. -/
def allCandidates (hyps goal : Expr) (isRoot : FVarId → Bool) : MetaM (Array Expr) := do
  let props ← unfoldProps #[goal, hyps]
  let alls ← allObservers props (← goalElementTypes goal isRoot)
  let (_, rootObs) ← observers props isRoot
  let mut out := alls.map (·.2.2)
  out := out ++ (← anyCandidates props)
  let mut seenObs : Array Expr := #[]
  for (o, _, fact) in alls do
    if seenObs.contains o.fn then continue
    seenObs := seenObs.push o.fn
    -- the recursive check behind the observer: the linking fact's premise head
    -- (`f … l = true → l.all E = true`)
    let checkFn? ← forallTelescope fact fun _ b => do
      let .forallE _ prem _ _ := b | return none
      return prem.eq?.bind fun (_, l, _) => l.getAppFn.constName?
    for t in rootObs do
      unless (← whnf (← inferType t)).isConstOf ``Bool do continue
      -- the link mentions only the fields the observation reads (a record
      -- literal's other fields would be quantified for nothing)
      let t ← Blaster.Proof.Explore.projReduce t
      let fvs := (collectFVars {} t).fvarIds
      if fvs.size > 1000 then continue
      for v in fvs do
        let vty ← inferType (.fvar v)
        unless ← isDefEq vty o.domain do continue
        -- only the list the observation's own check walks (a check of the
        -- reference inputs says nothing about the inputs)
        if let some f := checkFn? then
          unless ← walksWith t f v do continue
        let premise ← mkEq t (mkConst ``Bool.true)
        let concl ← mkEq (o.fn.beta #[.fvar v]) (mkConst ``Bool.true)
        let closed ← mkForallFVars (fvs.map Expr.fvar) (← mkArrow premise concl)
        if closed.hasFVar then continue
        unless out.contains closed do out := out.push closed
  return out

/-- Observers that a premise-free equality fact makes equal to an earlier one
(`valueOf c t v = dataQuantity c t v`) add nothing: drop them. -/
def dropEqualObservers (facts : Array Expr) (obs : Array Observer) : MetaM (Array Observer) := do
  let mut dropped : Std.HashSet Nat := {}
  for f in facts do
    let fty ← inferType f
    let pair? ← forallTelescopeReducing fty fun xs body => do
      for x in xs do
        if ← isProp (← inferType x) then return none
      let some (_, lhs, rhs) := body.eq? | return none
      return some (← mkLambdaFVars xs lhs, ← mkLambdaFVars xs rhs, xs.size)
    let some (lhsF, rhsF, n) := pair? | continue
    for i in [0:obs.size] do
      if dropped.contains i then continue
      for j in [0:obs.size] do
        if i == j || dropped.contains j then continue
        let same ← withNewMCtxDepth do
          let ms ← (List.range n).toArray.mapM fun _ => mkFreshExprMVar none
          let l := lhsF.beta ms
          let r := rhsF.beta ms
          let dom ← mkFreshExprMVar none
          let y ← mkFreshExprMVar dom
          let oi := obs[i]!.fn.beta #[y]
          let oj := obs[j]!.fn.beta #[y]
          if !(← isDefEq obs[i]!.domain obs[j]!.domain) then return false
          if ← isDefEq oi l then
            if ← isDefEq oj r then return true
          return false
        if same then dropped := dropped.insert j
  return (List.range obs.size).toArray.filterMap fun k => if dropped.contains k then none else some obs[k]!

/-- Observers connected to the goal: those of the goal (with its definitions
unfolded) and of the hypotheses as stated, closed under transport through the
facts. Observers that only an unfolded hypothesis mentions (the conjuncts of
a validity predicate) are left out unless a fact connects them; they would
otherwise be applied to every compatible variable of every cut. -/
def connectedObservers (hyps goal : Expr) (isRoot : FVarId → Bool) (facts : Array Expr) :
    MetaM (Array Observer) := do
  let (fromGoal, _) ← observers (← unfoldProps #[goal]) isRoot (context := true)
  let (fromHyps, _) ← observers #[hyps] isRoot
  let mut base := fromGoal
  for o in fromHyps do
    unless base.any (·.fn == o.fn) do base := base.push o
  let result ← transport facts base
  let elements ← elementObservers (fromGoal.filter fun o => result.any (·.fn == o.fn))
  -- element observers' own laws (a quantity read of an element and the walk that computes it)
  let transported ← transport facts (result ++ elements)
  let mut all := transported
  for o in ← anyElementObservers (← unfoldProps #[hyps]) isRoot do
    unless all.any (·.fn == o.fn) do all := all.push o
  let mut domains := #[]
  for o in fromGoal do
    let dom ← whnf o.domain
    if dom.isAppOfArity ``List 1 then domains := domains.push dom.appArg!
  for (o, e, _) in ← allObservers (← unfoldProps #[goal, hyps]) domains do
    unless all.any (·.fn == o.fn) do all := all.push o
    unless all.any (·.fn == e.fn) do all := all.push e
  return all

/-- Unfold applications of non-recursive program definitions to constructor
arguments (and reduce the resulting matches and projections), bottom-up: an
observation of a rebuilt value then depends only on the fields it reads. -/
partial def unfoldAtCtors (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let budget ← IO.mkRef fuel
  Meta.transform e (post := fun t => do
    if (← budget.get) == 0 then return .done t
    let .const fn _ := t.getAppFn | return .done t
    let env ← getEnv
    let some (.defnInfo _) := env.find? fn | return .done t
    if isMatcherCore env fn then return .done t
    if let some idx := env.getModuleIdxFor? fn then
      let module := env.header.moduleNames[idx.toNat]!
      if #[`Init, `Std, `Lean].any (·.isPrefixOf module) then return .done t
    if (← isRecursiveDefinition fn) then return .done t
    let hasCtorArg ← t.getAppArgs.anyM fun a => do
      let .const c _ := a.getAppFn | return false
      return (env.find? c).any (·.isCtor)
    unless hasCtorArg do return .done t
    let some t1 ← unfoldDefinition? t | return .done t
    let t2 ← projReduce (← whnfCore t1)
    if (← isStuckMatch t2) then return .done t
    budget.modify (· - 1)
    return .visit t2)

/-- Observations of the constructed values a cut's state holds (a map rebuilt
from a key, a token map and a remaining tail): observations of their fields
alone can lose the relation between the value the program compares and the
original total. -/
private def constructedObservations (plan : Plan) (obsFns : Array Observer)
    (obs : Array (Array Expr)) : ExM (Array (Array Expr)) := do
  let core ← get
  let numeric ← inCtx <| obsFns.filterM fun o =>
    lambdaTelescope o.fn fun _ b => do return (← whnf (← inferType b)).isConstOf ``Int
  let mut out := obs
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let terms ← inCtx do
      let mut found : Array Expr := #[]
      let mut work := #[plan.result.search.tpls[c.tpl]!.body]
      let env ← getEnv
      while !work.isEmpty do
        let e := work.back!
        work := work.pop
        unless e.hasFVar do continue
        if e.isApp && !e.hasLooseBVars then
          if e.getAppFn.constName?.any (fun n => (env.find? n).any (·.isCtor)) then
            let fs := (collectFVars {} e).fvarIds
            if fs.any (fun f => (core.vars[f]?).any (!·.rootish)) then
              unless found.contains e do found := found.push e
        match e with
        | .app .. => work := work ++ e.getAppArgs
        | .lam _ _ b _ | .forallE _ _ b _ | .mdata _ b => work := work.push b
        | .letE _ _ v b _ => work := (work.push v).push b
        | .proj _ _ b => work := work.push b
        | _ => pure ()
      pure found
    let extra ← inCtx do
      let mut extra := #[]
      for t in terms do
        let ty ← inferType t
        for o in numeric do
          if ← matchesDomain ty o.domain then
            let e := o.fn.beta #[t]
            unless out[i]!.contains e || extra.contains e do extra := extra.push e
      return extra
    out := out.set! i (out[i]! ++ extra)
  return out

/-- Observations of values a cut holds split into fields, rebuilt from those
fields: at a procedure's inner cuts its entry variables (so the region's ghost
`f L` can be related to `f (head :: tail)`), and at every cut a split value
whose fields the cut holds (the list a loop walks, held as its current element
and its rest). -/
private def rebuiltObservations (plan : Plan) (obsFns : Array Observer)
    (obs : Array (Array Expr)) : ExM (Array (Array Expr)) := do
  let core ← get
  let mut out := obs
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let cutVars : Std.HashSet FVarId := Std.HashSet.ofArray (c.vars.map (·.fvarId!))
    let entryVars := match c.entry? with
      | some e => if c.inner then (collectFVars {} (plan.result.search.tpls[e]!.body)).fvarIds else #[]
      | none => #[]
    let held :=
      core.splitVars.toList.toArray.filterMap fun ((a, _), fields) =>
        if !cutVars.contains a && fields.any (fun f => f.isFVar && cutVars.contains f.fvarId!)
        then some a else none
    let mut targets := entryVars
    for a in held do
      unless targets.contains a do targets := targets.push a
    let mut extra := #[]
    for L in targets do
      if cutVars.contains L then continue
      -- `v` rebuilt from the cut's variables through its split fields
      let rec rebuildT (v : FVarId) (fuel : Nat) : ExM (Option Expr) := do
        if cutVars.contains v then return some (.fvar v)
        match fuel with
        | 0 => return none
        | fuel + 1 =>
          for ((a, ctor), fields) in core.splitVars.toList do
            -- a split alternative belongs to this cut only when its fields
            -- reach the cut's variables; a field-less one (the other branch's
            -- `[]`) says nothing
            if a != v || fields.isEmpty then continue
            let mut fs := #[]
            let mut ok := true
            for f in fields do
              match f with
              | .fvar id =>
                match ← rebuildT id fuel with
                | some x => fs := fs.push x
                | none => ok := false
              | _ => ok := false
            if ok then return some (← ctorApp (.fvar v) ctor fs)
          return none
      let rebuilt? ← rebuildT L 4
      let some rebuilt := rebuilt? | continue
      for o in obsFns do
        if ← inCtx (do isDefEq (← inferType (.fvar L)) o.domain) then
          extra := extra.push (o.fn.beta #[rebuilt])
    unless extra.isEmpty do
      out := out.set! i (out[i]! ++ extra.filter (!out[i]!.contains ·))
  return out

/-- Element observers of existential hypothesis checks, and the integer
observers, applied to the elements a cut holds split into fields (rebuilt
from the cut's variables). -/
private def heldElementObservations (plan : Plan) (hyps : Expr) (isRoot : FVarId → Bool)
    (obsFns : Array Observer) (obs : Array (Array Expr)) : ExM (Array (Array Expr)) := do
  let core ← get
  let elemObs ← inCtx do
    let es ← anyElementObservers (← unfoldProps #[hyps]) isRoot
    -- also the integer observers (quantities): a value held split into its
    -- entries is still read by them
    obsFns.filterM fun o => do
      if es.any (·.fn == o.fn) then return true
      let ty ← lambdaTelescope o.fn fun _ b => do whnf (← inferType b)
      return ty.isConstOf ``Int
  if elemObs.isEmpty then return obs
  -- split index and the split variables of an element type
  let mut index : Std.HashMap FVarId (Array (Name × Array Expr)) := {}
  for ((a, ctor), fields) in core.splitVars.toList do
    index := index.insert a ((index.getD a #[]).push (ctor, fields))
  let mut targets : Array (FVarId × Array Observer) := #[]
  for (a, _) in index.toList do
    let os ← inCtx do
      let some d := (← getLCtx).find? a | pure #[]
      elemObs.filterM fun o => isDefEq d.type o.domain
    unless os.isEmpty do targets := targets.push (a, os)
  let mut out := obs
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let cutVars : Std.HashSet FVarId := Std.HashSet.ofArray (c.vars.map (·.fvarId!))
    -- rebuild from the split tree; a leaf that is neither split nor a cut
    -- variable stays itself (the observation is kept only if it does not
    -- depend on such leaves after projections reduce)
    let rec rebuild (v : FVarId) (fuel : Nat) : ExM (Option Expr) := do
      if cutVars.contains v then return some (.fvar v)
      match fuel with
      | 0 => return some (.fvar v)
      | fuel + 1 =>
        let alts := (index.getD v #[]).filter (!·.2.isEmpty)
        if alts.isEmpty then return some (.fvar v)
        -- the alternative whose fields reach the cut
        for (ctor, fields) in alts do
          let mut fs := #[]
          let mut ok := true
          for f in fields do
            match f with
            | .fvar id =>
              match ← rebuild id fuel with
              | some x => fs := fs.push x
              | none => ok := false; break
            | _ => ok := false; break
          unless ok do continue
          let reaches := fs.any fun x => (collectFVars {} x).fvarIds.any cutVars.contains
          if reaches then return some (← ctorApp (.fvar v) ctor fs)
        return some (.fvar v)
    let mut extra := #[]
    for (a, os) in targets do
      if cutVars.contains a then continue
      let rebuilt? ← rebuild a 10
      let some rebuilt := rebuilt? | continue
      -- only elements actually held by the cut (some field is a cut variable)
      unless (collectFVars {} rebuilt).fvarIds.any cutVars.contains do continue
      for o in os do
        let applied ← inCtx (unfoldAtCtors (← projReduce (o.fn.beta #[rebuilt])))
        let bad := (collectFVars {} applied).fvarIds.filter fun id => !(cutVars.contains id || isRoot id)
        if bad.isEmpty then extra := extra.push applied
    unless extra.isEmpty do
      out := out.set! i (out[i]! ++ extra.filter (!out[i]!.contains ·))
  return out

/-- Boolean decisions taken on a path into a cut, over values the cut still
holds, as observations of the cut (the invariant search keeps one only if
every entry establishes it). -/
private def pathFactObservations (plan : Plan) (isRoot : FVarId → Bool)
    (obs : Array (Array Expr)) : ExM (Array (Array Expr)) := do
  let mut out := obs
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let some node := plan.result.search.tpls[c.tpl]!.node? | continue
    for p in ← (paths plan c.entry? node {} #[] : ExM (Array Path)) do
      let .goto c' τ := p.last | continue
      let tgt := plan.cuts[c']!
      let tgtVars : Std.HashSet FVarId := Std.HashSet.ofArray (tgt.vars.map (·.fvarId!))
      -- source variable ↦ target variable, where the target holds it unchanged
      let mut inv : Std.HashMap FVarId Expr := {}
      for v in tgt.vars do
        match Subst.apply τ v with
        | .fvar u => inv := inv.insert u v
        | _ => pure ()
      let σ := p.subst
      for f in p.facts do
        let f' := Chc.applyFix σ f
        let some (_, lhs, rhs) := f'.eq? | continue
        unless rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false do continue
        let fvs := (collectFVars {} lhs).fvarIds
        if fvs.isEmpty then continue
        unless fvs.all (fun u => inv.contains u || isRoot u) do continue
        let b := lhs.replace fun t => match t with
          | .fvar u => inv[u]?
          | _ => none
        unless (collectFVars {} b).fvarIds.all (fun u => tgtVars.contains u || isRoot u) do continue
        unless out[c']!.contains b do
          out := out.set! c' (out[c']!.push b)
  return out

/-- The shape of the lists a cut holds (empty, singleton), tails introduced by
a constructor split included: a later singleton or empty check can constrain
such a tail although the tail itself was never a template parameter. -/
private def listShapeObservations (plan : Plan) (obs : Array (Array Expr)) :
    ExM (Array (Array Expr)) := do
  let mut out := obs
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let mut extra := #[]
    for v in c.vars do
      let r? ← inCtx do
        let ty ← whnf (← inferType v)
        unless ty.isAppOfArity ``List 1 do return none
        let e1 ← mkAppM ``List.isEmpty #[v]
        let e2 ← mkAppM ``List.isEmpty #[← mkAppM ``List.tail #[v]]
        return some #[e1, e2]
      if let some es := r? then
        for e in es do
          unless out[i]!.contains e || extra.contains e do extra := extra.push e
    unless extra.isEmpty do
      out := out.set! i (out[i]! ++ extra)
  return out

/-- The kind of observation `o` for the invariant search: its sort, its
observer's head (`var` for a program value itself), its role (`root` when it
reads only roots, unless `role?` says otherwise) and the variables it reads. -/
private def kindOf (isRoot : FVarId → Bool) (role? : Option Houdini.Role) (o : Expr) :
    MetaM Houdini.Kind := do
  let o ← instantiateMVars o
  let head := match o.getAppFn with
    | .const n _ => n.components.getLast!.toString
    | .fvar _ => "var"
    | _ => "other"
  let fvs := (collectFVars {} o).fvarIds
  let ty ← whnf (← inferType o)
  let sort := if ty.isConstOf ``Int || ty.isConstOf ``Nat then .int
    else if ty.isConstOf ``Bool then .bool else .data
  return {sort, head, role := role?.getD (if fvs.all isRoot then .root else .var), ids := fvs.map (·.name)}

/-- Encode the Horn query of `prob` (one relation per cut point and per
procedure summary, one clause per recorded path) and search its invariants:
the query and the conjuncts of each relation's invariant. -/
private def search (prob : Problem) (hyps goal : Expr) (isRoot : FVarId → Bool) (timeoutMs : Nat) :
    ExM (Houdini.Query × Array (Array String)) := do
  let plan := prob.plan
  let mut kinds := #[]
  for i in [0:plan.cuts.size] do
    let ci := plan.cuts[i]!
    -- (a region's entry observations, as ghosts of its inner cut points)
    let ghosts := if ci.inner then prob.obsIn.getD ci.entry?.get! #[] else #[]
    kinds := kinds.push (← inCtx do
      return (← ghosts.mapM (kindOf isRoot (some .ghost))) ++ (← prob.observations[i]!.mapM (kindOf isRoot none)))
  for e in prob.procs do
    kinds := kinds.push (← inCtx ((prob.obsIn.getD e #[] ++ prob.obsOut.getD e #[]).mapM (kindOf isRoot none)))
  -- the paths of every cut, and what their clauses read: the fact matching
  -- is independent per path, so it runs in parallel before the encoding
  let mut cutPaths : Array (Nat × Path) := #[]
  for i in [0:plan.cuts.size] do
    let c := plan.cuts[i]!
    let some node := plan.result.search.tpls[c.tpl]!.node? | continue
    for p in ← (paths plan c.entry? node {} #[] : ExM (Array Path)) do
      cutPaths := cutPaths.push (i, p)
  -- failed premise matches are valid for this query's reducibility settings only
  premiseFail.set {}
  -- (matching only: no solver, so twice as many threads as provers)
  let prepared ← inCtx <| parallelMap (2 * (← jobCount)) cutPaths fun (i, p) => do
    let σ ← clauseSubst prob i p
    return (σ, ← clauseInstances prob i p σ)
  let go : Smt.EncM Houdini.Query := do
    let mut relations := #[]
    for i in [0:plan.cuts.size] do
      let sorts ← (prob.ghostArgs i ++ prob.observations[i]!).mapM sortOfObs
      relations := relations.push {sorts, kinds := kinds[i]!}
    for e in prob.procs do
      let ins := prob.obsIn.getD e #[]
      let sorts ← (ins ++ prob.obsOut.getD e #[]).mapM sortOfObs
      relations := relations.push {sorts, kinds := kinds[prob.post e]!, entry := ins.size}
    let root := plan.cutOf[plan.graph.rootTpl]!
    let mut clauses := #[← entryClause prob hyps root plan.graph.rootSubst]
    for ((i, p), (σ, instances)) in cutPaths.zip prepared do
      clauses := clauses.push (← clause prob i p hyps goal σ instances)
    return {preamble := "\n".intercalate (← getThe Smt.Global).commands.toList, relations, clauses}
  let ((query, _), _) ← (go.run {}).run {}
  let report ← progressEnabled
  let log := fun s => if report then IO.eprintln s!"[chc] {s}" else pure ()
  -- (z3 processes, not threads of this process: four per job)
  match ← Houdini.search query (4 * (← jobCount)) timeoutMs log with
  | .ok invariants => return (query, invariants)
  | .error why => throwError "explore: invariant search failed: {why}"

/-- Propose invariants for the cut points of a plan, and postconditions for its
procedures. The proposal is only a candidate: the proof replay must prove all
of its obligations before it can establish the caller's theorem. -/
def propose (plan : Plan) (hyps goal : Expr) (isRoot : FVarId → Bool) (scalarRoots : Array Expr)
    (timeoutMs : Nat := 60000) (facts : Array Expr := #[]) : ExM Proposal := do
  let (_, rootObs) ← inCtx do observers (← unfoldProps #[goal, hyps]) isRoot
  -- the goal's matches over recursive roots, as root observations
  let (_, goalRoots) ← inCtx do observers (← unfoldProps #[goal]) isRoot (context := true)
  let rootObs := rootObs ++ goalRoots.filter (!rootObs.contains ·)
  let obsFns ← inCtx (connectedObservers hyps goal isRoot facts)
  let obsFns ← inCtx (dropEqualObservers facts obsFns)
  -- root observations: only those of the connected observers (the others are
  -- validity conjuncts the hypotheses restate in every clause, or unrelated)
  let rootObs ← inCtx do
    let heads : Array Name := obsFns.filterMap fun o =>
      match o.fn.getNumHeadLambdas, o.fn with
      | _, .lam _ _ b _ => b.getAppFn.constName?
      | _, _ => none
    let mut kept := #[]
    for r in rootObs do
      let r' ← projReduce1 r
      let recursive ← match r'.getAppFn.constName? with
        | some n => isRecursiveDefinition n
        | none => pure false
      if !(kept.contains r') && (recursive || r'.getAppFn.constName?.any heads.contains) then
        kept := kept.push r'
    return kept
  let obs ← plan.cuts.mapM fun c => inCtx (cutObservations c.vars obsFns rootObs scalarRoots)
  let obs ← constructedObservations plan obsFns obs
  let obs ← rebuiltObservations plan obsFns obs
  let obs ← heldElementObservations plan hyps isRoot obsFns obs
  let obs ← pathFactObservations plan isRoot obs
  let obs ← listShapeObservations plan obs
  -- procedures: entry observations, exit observations, ghost placeholders
  let mut obsIn : Std.HashMap Nat (Array Expr) := {}
  let mut obsOut : Std.HashMap Nat (Array Expr) := {}
  let mut ghosts : Std.HashMap Nat (Array Expr) := {}
  for (e, _) in plan.graph.shapes.toList do
    let some ce := plan.cutOf[e]? | continue
    let ins := obs[ce]!
    obsIn := obsIn.insert e ins
    obsOut := obsOut.insert e (← inCtx (cutObservations (plan.holes.getD e #[]) obsFns #[] #[]))
    let gs ← ins.mapM fun o => do
      let ty ← inCtx (inferType o)
      mkVar `ĝ ty .param false
    ghosts := ghosts.insert e gs
  let procs := (obsIn.toList.map (·.1)).toArray
  let prob : Problem := {plan, observations := obs, obsIn, obsOut, ghosts, procs, facts}
  -- the relations' names in a model: `R{cut}` and `P{entry template}`
  let names := (List.range plan.cuts.size).toArray.map (s!"R{·}") ++ procs.map (s!"P{·}")
  -- the invariant of each relation, as a definition over its arguments
  let defs ← match blaster.explore.modelFile.get (← getOptions) with
    | "" => do
      let (query, invariants) ← search prob hyps goal isRoot timeoutMs
      let mut defs := {}
      for r in [0:names.size] do
        let cs := invariants[r]!
        let text := if cs.isEmpty then "true" else s!"(and {" ".intercalate cs.toList})"
        let .ok (body, _) := parseS text.toList.toArray 0
          | throwError "explore: malformed invariant {text}"
        let params := (List.range query.relations[r]!.sorts.size).toArray.map (s!"p{·}")
        defs := defs.insert names[r]! {params, body}
      pure defs
    -- (a supplied model is only a proposal too: every obligation is still proved)
    | path => do
      let text ← try IO.FS.readFile path
        catch e => throwError "explore: cannot read the invariant model {path}: {e.toMessageData}"
      match parseModel text with
      | .ok defs => pure defs
      | .error why => throwError "explore: cannot read the invariant model {path}: {why}"
  let interpret (r : Nat) (args : Array Expr) : ExM Expr := do
    let some d := defs[names[r]!]? | return mkConst ``True
    inCtx (interp defs (Std.HashMap.ofList (d.params.zip args).toList) d.body)
  let invs ← (List.range plan.cuts.size).toArray.mapM fun i => interpret i (prob.ghostArgs i ++ obs[i]!)
  let mut posts := {}
  for e in procs do
    posts := posts.insert e (← interpret (prob.post e) (ghosts.getD e #[] ++ obsOut.getD e #[]))
  return {invs, posts, ghostVars := ghosts, ghostVals := obsIn}

end Blaster.Proof.Explore.Chc
