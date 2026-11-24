import Lean
import Blaster.Command.Syntax
import Blaster.Smt.Translate
import Blaster.Optimize
import Blaster.Logging.Basic

open Lean Elab Tactic Meta
open Blaster.Optimize Blaster.Smt Blaster.Options Blaster.Syntax

namespace Blaster.Tactic

/--
`blaster` is an SMT-based tactic that automatically proves goals using Z3.

Options:
  - `timeout`: specifying the timeout (in second) to be used for the backend smt solver (defaut: ∞)
  - `verbose:` activating debug info (default: 0)
  - `only-smt-lib`: only translating unsolved goals to smt-lib without invoking the backend solver (default: 0)
  - `only-optimize`: only perform optimization on lean specification and do not translate to smt-lib (default: 0)
  - `dump-smt-lib`: display the smt lib query to stdout (default: 0)
  - `gen-cex`: generate counterexample for falsified theorems (default: 1)
  - `unfold-depth`: specifying the number of unfolding to be performed on recursive functions (default: 100)
  - `random-seed`: seed for the random number generator (default: none)
  - `solve-result`: specify the expected result from the blaster tactic, i.e.,
                    0 for 'Valid', 1 for 'Falsified' and 2 for 'Undetermined'. (default: 0)
Example: `blaster (timeout: 10) (verbose: 1)`
-/
syntax (name := blasterTactic) "blaster" (solveOption)* : tactic

/-- Work item of `toElabForm`: a subterm to visit, or how to combine the last results
    into the conversion of `e`, the last two or the last one. -/
private inductive ElabTask where
  | visit (e : Expr)
  | bin (e : Expr) (op : Expr → Expr → Expr)
  | un (e : Expr) (op : Expr → Expr)
  deriving Inhabited

/-- Convert core Nat/Int operators, `String.append` and the raw Int literals `Int.ofNat n`,
    `Int.negSucc n` to their elaborated form, `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv`,
    `HMod.hMod`, `HAppend.hAppend`, `Neg.neg` and `OfNat.ofNat`,
    so that proof term LHS patterns structurally match goal expressions.
    An operator is converted at any arity, so that `Nat.add x` and `fun y => Nat.add x y` stay
    eta-equal.
    The operator fixes the instances, so the result is definitional whatever the operand type.
    `cache` maps the subterms converted so far to their result, and each result to itself, and
    is returned extended, so each subterm is converted once, also when shared (up to binder
    names), and a result is not converted again.
    Uses an explicit stack, so a deep `e` cannot overflow the native stack. -/
def toElabForm (e : Expr) (cache : Std.HashMap Expr Expr) : Expr × Std.HashMap Expr Expr := Id.run do
  -- children are visited left to right, then combined, as a post-order recursion would
  let mut todo : Array ElabTask := #[.visit e]
  let mut done : Array Expr := #[]
  let mut cache := cache
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    match t with
    | .visit e =>
      -- `e` itself when it converts to itself, so that the nodes above it are kept
      if let some r := cache[e]? then done := done.push (if r == e then e else r)
      else match visit e with
        | .inl r => done := done.push r
        | .inr ts => todo := todo ++ ts
    | .bin e op =>
      let r := op done.pop.back! done.back!
      cache := cache.insert e r
      if r != e then cache := cache.insert r r
      done := done.pop.pop.push r
    | .un e op =>
      let r := op done.back!
      cache := cache.insert e r
      if r != e then cache := cache.insert r r
      done := done.pop.push r
  return (done.back!, cache)
where
  /-- Tasks that convert `a` and `b`, then combine them with `op`, in reverse order since `todo`
      is a stack. -/
  bin (e : Expr) (op : Expr → Expr → Expr) (a b : Expr) : Array ElabTask :=
    #[.bin e op, .visit b, .visit a]
  /-- The converted leaf `e`, or the tasks converting it. -/
  visit (e : Expr) : Expr ⊕ Array ElabTask :=
  match e with
  | .const ``Nat.add _ => .inl (binOp ``HAdd.hAdd Nat.mkType Nat.mkInstHAdd)
  | .const ``Nat.sub _ => .inl (binOp ``HSub.hSub Nat.mkType Nat.mkInstHSub)
  | .const ``Nat.mul _ => .inl (binOp ``HMul.hMul Nat.mkType Nat.mkInstHMul)
  -- `/` and `%` on Nat elaborate to `HDiv.hDiv`/`HMod.hMod`, the raw forms come from the optimizer
  -- or an unfold step
  | .const ``Nat.div _ => .inl (binOp ``HDiv.hDiv Nat.mkType Nat.mkInstHDiv)
  | .const ``Nat.mod _ => .inl (binOp ``HMod.hMod Nat.mkType Nat.mkInstHMod)
  | .const ``Int.add _ => .inl (binOp ``HAdd.hAdd Int.mkType Int.mkInstHAdd)
  | .const ``Int.sub _ => .inl (binOp ``HSub.hSub Int.mkType Int.mkInstHSub)
  | .const ``Int.mul _ => .inl (binOp ``HMul.hMul Int.mkType Int.mkInstHMul)
  | .const ``Int.ediv _ => .inl (binOp ``HDiv.hDiv Int.mkType Int.mkInstHDiv)
  | .const ``Int.emod _ => .inl (binOp ``HMod.hMod Int.mkType Int.mkInstHMod)
  | .const ``Int.neg _ => .inl (mkApp2 (mkConst ``Neg.neg [0]) Int.mkType Int.mkInstNeg)
  | Expr.app (Expr.const ``Int.ofNat _) (Expr.lit (Literal.natVal n)) => .inl (mkIntLit n)
  -- `Int.negSucc n` denotes `-(n+1)`.
  | Expr.app (Expr.const ``Int.negSucc _) (Expr.lit (Literal.natVal n)) => .inl (mkIntLit (.negSucc n))
  -- `++` on String elaborates to `HAppend.hAppend`, the optimizer works on `String.append`
  | .const ``String.append _ => .inl (binOp ``HAppend.hAppend (mkConst ``String)
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) (mkConst ``String) (mkConst ``String.instAppend)))
  -- an unchanged node is kept, so that the result shares the subterms of `e`; the children
  -- are read off `e`, as the patterns above would rebuild the head of an application
  | .app .. => .inr (bin e e.updateApp! e.appFn! e.appArg!)
  -- the conversion is syntactic, so it applies below binders too
  | .lam .. => .inr (bin e e.updateLambdaE! e.bindingDomain! e.bindingBody!)
  | .forallE .. => .inr (bin e e.updateForallE! e.bindingDomain! e.bindingBody!)
  | .mdata _ b => .inr #[.un e e.updateMData!, .visit b]
  | .proj _ _ b => .inr #[.un e e.updateProj!, .visit b]
  | _ => .inl e
  /-- The homogeneous operator `op` on `α`, with its instance `inst`, before its operands. -/
  binOp (op : Name) (α inst : Expr) : Expr := mkApp4 (mkConst op [0, 0, 0]) α α α inst

/-- The optimizer binders `optBinders` (see `Blaster.Optimize.OptBinders`) paired by position with
    `xs`, without the positions of the binders dropped before they were opened. -/
def pairBinders (optBinders : Array (Option FVarId)) (xs : Array α) : Array FVarId × Array α :=
  ((optBinders.zip xs).filterMap fun (o, x) => o.map (·, x)).unzip

/-- Replace optimizer-context FVarIds with goal-context FVarIds in the proof steps that `applies`
    accepts. The goal binders among those a step was pushed below are dropped, as the replay
    introduces them. -/
def substProofStackFVars (steps : Array Blaster.Optimize.ProofStep)
    (optBinders goalFVarIds : Array FVarId)
    (applies : Blaster.Optimize.ProofStep → Bool := fun _ => true) :
    Array Blaster.Optimize.ProofStep :=
  if optBinders.isEmpty then steps
  else
    let n := min optBinders.size goalFVarIds.size
    let from_ := (optBinders[:n].toArray).map mkFVar
    let to_ := (goalFVarIds[:n].toArray).map mkFVar
    let goal : Std.HashSet FVarId := optBinders[:n].foldl (·.insert ·) {}
    steps.map fun s => if !applies s then s else match s with
      | .rewrite proof symm bs => .rewrite (proof.replaceFVars from_ to_) symm
          (bs.filterMap fun b =>
            if goal.contains b.fvar then none else some { b with type := b.type.replaceFVars from_ to_ })
      | .exact proof => .exact (proof.replaceFVars from_ to_)
      | s@(.unfold _) => s

/-- Whether the COI rule of `optimizeForall` eliminates each binder of `vs`, `body` being the body
    under them, deciding from the last binder to the first as the optimizer does: neither `body`
    nor the type of a later binder that stays mentions it, and `isSortOrInhabited` accepts its
    type with only the earlier binders of `vs` in scope. The binders of the other side, `others`,
    leave the context too, with their instances, as the types of `vs` do not mention them.
    The optimizer checks the optimized body instead, so a binder that only a part it drops
    mentions is eliminated there but not here. -/
private def coiEliminated (vs : Array Expr) (body : Expr) (others : Array Expr) :
    MetaM (Array Bool) := do
  let lctx ← getLCtx
  -- the binders of `vs` from `scope` on are already out of `lctx`, and `others` once one is
  let rec go (i scope : Nat) (lctx : LocalContext) (localInsts : LocalInstances)
      (later : CollectFVars.State) (elim : Array Bool) : MetaM (Array Bool) := do
    match i with
    | 0 => return elim
    | i + 1 =>
      let v := vs[i]!.fvarId!
      let t := (lctx.get! v).type
      if body.containsFVar v || later.fvarSet.contains v then
        go i scope lctx localInsts (collectFVars later t) elim
      else
        let out := if scope == vs.size then vs.extract i scope ++ others else vs.extract i scope
        let lctx := out.foldl (fun l x => l.erase x.fvarId!) lctx
        let localInsts := localInsts.filter fun l => !out.contains l.fvar
        -- read only, so a fresh optimizer environment does, given the local context as
        -- `Optimize.main` gives it, since the optimizer infers types in that context
        let e ← withLCtx lctx localInsts do
          (do updateLocalContext (← mkLocalContext); isSortOrInhabited t : TranslateEnvT Bool).run'
            default
        go i i lctx localInsts (if e then later else collectFVars later t) (elim.set! i e)
  go vs.size vs.size lctx (← getLocalInstances) {} (Array.replicate vs.size false)

/-- The binders of `ys` that `idx` matches, and the binders of `xs` they stand for. -/
private def matchedPairs (xs ys : Array Expr) (idx : Array (Option Nat)) :
    Array Expr × Array Expr := Id.run do
  let mut f := #[]
  let mut t := #[]
  for j in [:ys.size] do
    if let some i := idx[j]! then
      f := f.push ys[j]!
      t := t.push xs[i]!
  return (f, t)

/-- The index of the binder of `xs` that each binder of `ys` stands for, given the binders
    `coiEliminated` eliminates on each side, `xElim` and `yElim`, or `none` when a kept `y` has
    no counterpart.
    The binders that survive optimization keep their order, so the candidates of a kept `y` are
    the kept `xs` after the previous match. A hypothesis or an unused binder of an empty type is
    kept, so it stays a candidate. The candidates of an eliminated `y` are all the `xs` after
    the previous match, and without one it stands for no binder. Nothing uses it, so matching
    it leaves the replayed equation as is, and only holds its position for the next `ys`.
    A binder keeps its name, so `y` stands for one of the candidates with its name, when some
    have it. When the `ys` from `y` on carry that name as many times as these candidates, `y` is
    the first of them, as binders keep their order. Otherwise the name does not tell which one,
    e.g. the name every anonymous `→` binder gets: with fewer such `ys` some of these candidates
    were eliminated, with more some of these `ys` stand for no candidate. Then `y` is the first of
    them whose type is its type, given the previous matches, so when one of them was eliminated
    and the kept ones were rewritten to other types, `y` has no match, as the stack does not tell
    which binder a step dropped.
    Without a candidate with its name, `y` is the first candidate whose type is its type.
    The type covers a renamed binder and an anonymous instance binder, whose name has fresh
    macro scopes in each elaboration.
    `coiEliminated` sees the body before optimization, so an `x` that only a dropped part
    mentions stays a candidate, and a renamed `y` can match it, which leaves a gap.
    No test locks the order rule for same-named binders, as the only known goal where it
    changes the outcome needs the COI rule to eliminate a binder whose type may be empty, which
    is unsound: `isSortOrInhabited` accepts such types, e.g. a type variable, or an indexed
    family whose only nullary constructor has another index. -/
def matchBinders (ys xs : Array Expr) (xElim yElim : Array Bool) :
    MetaM (Option (Array (Option Nat))) := do
  let mut idx := #[]
  let mut next := 0
  for j in [:ys.size] do
    let n ← ys[j]!.fvarId!.getUserName
    let later := (List.range' next (xs.size - next)).filter fun i => yElim[j]! || !xElim[i]!
    let (f, t) := matchedPairs xs (ys.extract 0 j) idx
    let ty := (← inferType ys[j]!).replaceFVars f t
    let named ← later.filterM fun i => return (← xs[i]!.fvarId!.getUserName) == n
    let carried ← (ys.extract j ys.size).filterM fun y => return (← y.fvarId!.getUserName) == n
    let found ← if !named.isEmpty && named.length == carried.size then pure named.head?
      else (if named.isEmpty then later else named).findM? fun i => do
        isDefEq (← inferType xs[i]!) ty
    match found with
    | some i =>
      idx := idx.push (some i)
      next := i + 1
    | none =>
      unless yElim[j]! do return none
      idx := idx.push none
  return some idx

/-- `true` iff `e` contains a `let` binding anywhere.
    `noLet` holds subterms known to have no `let`, which are skipped, and is returned extended,
    so each subterm is visited once, also when shared (up to binder names).
    Tail recursive on a stack of pending subterms, so a deep `e` cannot overflow. -/
private partial def hasLet (e : Expr) (noLet : Std.HashSet Expr) : Bool × Std.HashSet Expr :=
  go [(e, false)] noLet
where
  -- `(e, true)` marks `e` as explored, once all its subterms were
  go : List (Expr × Bool) → Std.HashSet Expr → Bool × Std.HashSet Expr
  | [], noLet => (false, noLet)
  | (e, true) :: es, noLet => go es (noLet.insert e)
  | (e, false) :: es, noLet =>
    if noLet.contains e then go es noLet else
    match e with
    | .letE .. => (true, noLet)
    | .app f a => go ((f, false) :: (a, false) :: (e, true) :: es) noLet
    | .lam _ t b _ => go ((t, false) :: (b, false) :: (e, true) :: es) noLet
    | .forallE _ t b _ => go ((t, false) :: (b, false) :: (e, true) :: es) noLet
    | .mdata _ b => go ((b, false) :: (e, true) :: es) noLet
    | .proj _ _ b => go ((b, false) :: (e, true) :: es) noLet
    | _ => go es noLet

/-- `true` iff `e` contains `sorryAx` anywhere.
    Tail recursive on a stack of pending subterms, so a deep `e` cannot overflow, as core's
    `Expr.hasSorry` does. Each compound subterm is explored once, by pointer, also when shared,
    and an atom is matched at each of its occurrences, so the cost is linear in the edges of
    the DAG of `e`, not in the size of its tree. -/
private partial def containsSorry (e : Expr) : Bool :=
  go [e] {}
where
  go : List Expr → Std.HashSet PtrExpr → Bool
  | [], _ => false
  | e :: es, seen =>
    match e with
    | .const ``sorryAx _ => true
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => go es seen
    | _ =>
      let (visited, seen) := seen.containsThenInsert ⟨e⟩
      if visited then go es seen else
      match e with
      | .app f a => go (f :: a :: es) seen
      | .lam _ t b _ | .forallE _ t b _ => go (t :: b :: es) seen
      | .letE _ t v b _ => go (t :: v :: b :: es) seen
      | .mdata _ b | .proj _ _ b => go (b :: es) seen
      | _ => go es seen

/-- Memo of `toElabForm` and `hasLet` over one replay, shared by every `canonicalForm` call. -/
private structure CanonCache where
  /-- `toElabForm` of the subterms converted so far, each the result of the `Core.transform` of
      `canonicalForm`, so the canonical form of each, and each result mapped to itself. -/
  converted : Std.HashMap Expr Expr := {}
  /-- The subterms known to have no `let`. -/
  noLet : Std.HashSet Expr := {}

/-- Instantiate every `let` and `have` of `e` with its value. -/
private def zetaLets (e : Expr) : MetaM Expr :=
  Core.transform e (pre := fun
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- The one spelling of the replay, so that the user and optimizer spellings of a term agree:
    no `let`, no beta redex, `((n : Nat) : Int)` written `Int.ofNat n`, Nat numerals under
    `Int.ofNat` and `Int.negSucc` raw literals, then `toElabForm`. Subterms in `cache` are not
    visited again; the result is `e` itself when `e` is canonical. -/
private def canonicalForm (cache : IO.Ref CanonCache) (e : Expr) : MetaM Expr := do
  -- taken out of the ref, so that the maps are updated in place; a throw below leaves the ref
  -- empty, and nothing reads it again: the cache lives for one `applyProofStack` call, which
  -- the exception leaves
  let { converted, noLet } ← cache.swap {}
  let (l, noLet) := hasLet e noLet
  -- `e` in place of an equal `c`, so that the result keeps the objects of the input
  let same (c e : Expr) := if c == e then e else c
  -- the raw literal of a Nat numeral
  let raw? (n : Expr) :=
    if n.isAppOfArity ``OfNat.ofNat 3 && (n.getArg! 2).isAppOf ``instOfNatNat then
      some (n.getArg! 1)
    else none
  let ofNat (n : Expr) := mkApp (mkConst ``Int.ofNat) ((raw? n).getD n)
  -- the nodes entered and not yet left, innermost last, since `post` gets a node rebuilt from the
  -- results of its children
  let entered ← IO.mkRef (#[] : Array Expr)
  let e ← if l then zetaLets e else pure e
  let e ← Core.transform e
    (pre := fun e => do
      if let some c := converted[e]? then return .done (same c e)
      entered.modify (·.push e)
      return .continue)
    (post := fun e => do
      let orig := (← entered.get).back!
      entered.modify (·.pop)
      -- the node entered, when its children are left as they were
      let e := same e orig
      return match e with
      -- the optimizer keeps applied lambdas reduced, without a step; the result is visited
      -- again for the redexes substituting the arguments creates
      | .app .. => if e.getAppFn.isLambda then .visit e.headBeta else .done <| match e with
        | .app (.app (.app (.const ``Nat.cast _) _) (.const ``instNatCastInt _)) n => ofNat n
        -- the spelling left by the unfold step of `Nat.cast`
        | .app (.app (.app (.const ``NatCast.natCast _) _) (.const ``instNatCastInt _)) n => ofNat n
        | .app (.const ``Int.ofNat _) n => match raw? n with
          | some r => mkApp (mkConst ``Int.ofNat) r
          | none => e
        | .app (.const ``Int.negSucc _) n => match raw? n with
          | some r => mkApp (mkConst ``Int.negSucc) r
          | none => e
        | _ => e
      | _ => .done e)
  let (e, converted) := toElabForm e converted
  cache.set { converted, noLet }
  return e

/-- The step proof `p` with its statement in the spelling of `canonicalForm`, as the goal is, since
    a lemma applied to a literal states it in its own spelling, e.g. `Int.ofNat 3`. For `rewrite`,
    which reads the statement off the proof's type. -/
private def withCanonicalType (cache : IO.Ref CanonCache) (p : Expr) : MetaM Expr := do
  let ty ← inferType p
  let ty' ← canonicalForm cache ty
  if ty' == ty then return p else mkExpectedTypeHint p ty'

/-- Whether the kernel accepts a step proof with free variables, since a hypothesis left out of
    normal form by the replay makes a proof built on it ill-typed. A leftover metavariable also
    fails. -/
private def wellTypedStep (proof : Expr) : MetaM Bool := do
  unless proof.hasFVar do return true
  return Kernel.check (← getEnv) (← getLCtx) (← instantiateMVars proof) matches .ok _

/-- Throw on a step proof that `wellTypedStep` rejects. -/
private def checkHypStep (g : MVarId) (proof : Expr) : MetaM Unit := do
  unless ← g.withContext (wellTypedStep proof) do throwError "ill-typed proof step"

/-- A rewrite step pushed below binders the replay does not introduce (of a `∃`, a `fun`, a nested
    `∀`), out of the reach of `kabstract`. `thm` is its proof closed over the binders it mentions,
    outermost first, and `depth` the position of each among the binders open at the step,
    innermost first. A step out of binders, which `kabstract` applies, has none, and is
    `outside`. -/
private structure BinderStep where
  thm : Expr
  symm : Bool
  depth : Array Nat
  outside : Bool := false
  deriving Inhabited

/-- The step `p`, pushed below `bs` (innermost first), closed over those the replay does not
    introduce. `outside` when there are none, or when `p` is an instance free of them, which
    `kabstract` finds anywhere. `none` when the replay cannot map an fvar of `p`. -/
private def closeOverBinders (p : Expr) (symm : Bool) (bs : List Blaster.Optimize.OpenBinder) :
    MetaM (Option BinderStep) := do
  let lctx ← getLCtx
  let bs := bs.filter (!lctx.contains ·.fvar)
  -- an fvar in neither the context nor `bs`
  if p.hasAnyFVar (fun f => !lctx.contains f && !bs.any (·.fvar == f)) then return none
  let outside : BinderStep := { thm := p, symm, depth := #[], outside := true }
  if bs.isEmpty then return some outside
  -- a lemma left to unify is applied below binders
  unless p.hasAnyFVar (fun f => bs.any (·.fvar == f)) do
    unless (← whnfR (← inferType p)).isForall do return some outside
  -- the binders `p` mentions, and those their types mention, which are outer ones
  let mut need : Std.HashSet FVarId := (collectFVars {} p).fvarIds.foldl (·.insert ·) {}
  for b in bs do
    if need.contains b.fvar then
      need := (collectFVars {} b.type).fvarIds.foldl (·.insert ·) need
  let xs := (bs.filter (need.contains ·.fvar)).reverse
  let lctx' := xs.foldl (fun l b => l.mkLocalDecl b.fvar `x b.type) lctx
  let thm ← withLCtx lctx' (← getLocalInstances) do mkLambdaFVars (xs.map (mkFVar ·.fvar)).toArray p
  -- the type of a binder may mention one that was not recorded
  if thm.hasAnyFVar (!lctx.contains ·) then return none
  return some { thm, symm, depth := xs.toArray.map fun b => bs.findIdx (·.fvar == b.fvar) }

/-- The key of a step below binders: the head and arity of the side it rewrites, `none` when one of
    its binders heads it, and `none` outside when its type is not an equation. -/
private abbrev BinderKey := Option (Option (HeadIndex × Nat))

/-- The steps below binders by the head and arity of the side they rewrite, as `kabstract`
    filters its instances, in `anyHead` those headed by one of their binders, and the type and the
    key of each step. -/
private structure BinderIndex where
  byHead : Std.HashMap (HeadIndex × Nat) (Array Nat) := {}
  anyHead : Array Nat := #[]
  types : Array Expr := #[]
  keys : Array BinderKey := #[]

/-- The index of the steps with these keys and types. -/
private def BinderIndex.ofKeys (keys : Array BinderKey) (types : Array Expr) : BinderIndex := Id.run do
  let mut d : BinderIndex := { types, keys }
  for h : i in [:keys.size] do
    match keys[i] with
    | some (some k) => d := { d with byHead := d.byHead.insert k ((d.byHead.getD k #[]).push i) }
    | some none => d := { d with anyHead := d.anyHead.push i }
    | none => pure ()
  return d

/-- The steps that may rewrite `e`, in stack order. -/
private def BinderIndex.candidates (d : BinderIndex) (e : Expr) : Array Nat :=
  ((d.byHead.getD (e.toHeadIndex, e.headNumArgs) #[]) ++ d.anyHead).qsort (· < ·)

/-- The steps that may rewrite `e` or the application of its head to its first `k` arguments,
    paired with `k`, in stack order. `kabstract` finds a partial application too, e.g. the side
    `dite' True` of a lemma stated by `funext`. -/
private def BinderIndex.prefixCandidates (d : BinderIndex) (e : Expr) : Array (Nat × Nat) :=
  let n := e.headNumArgs
  let byPrefix := (List.range (n + 1)).foldl (init := #[]) fun a k =>
    a ++ (d.byHead.getD (e.toHeadIndex, k) #[]).map (·, k)
  (byPrefix ++ d.anyHead.map (·, n)).qsort (·.1 < ·.1)

/-- The key and the type of the step `b`. -/
private def binderStepKey (cache : IO.Ref CanonCache) (b : BinderStep) :
    MetaM (BinderKey × Expr) := do
  -- the statement in the spelling of the target, which the traversal matches
  let ty ← canonicalForm cache (← inferType b.thm)
  let key ← withNewMCtxDepth do
    let (xs, _, ty) ← forallMetaTelescopeReducing ty
    let some (_, l, r) := (← whnfR ty).eq? | return none
    let l := if b.symm then r else l
    return some <| if xs[:b.depth.size].toArray.contains l.getAppFn then none
      else some (l.toHeadIndex, l.headNumArgs)
  return (key, ty)

private def indexBinderSteps (cache : IO.Ref CanonCache) (bs : Array BinderStep) :
    MetaM BinderIndex := do
  let ks ← bs.mapM (binderStepKey cache)
  return .ofKeys (ks.map (·.1)) (ks.map (·.2))

/-- `d` once a replaced hypothesis renamed the fvars of the steps `old` into `new`: only the steps
    whose proof changed are indexed again, and the map is built again only if a key changed. -/
private def BinderIndex.reindex (d : BinderIndex) (cache : IO.Ref CanonCache)
    (old new : Array BinderStep) : MetaM BinderIndex := do
  let mut keys := d.keys
  let mut types := d.types
  for h : i in [:new.size] do
    if new[i].thm != old[i]!.thm then
      let (k, t) ← binderStepKey cache new[i]
      keys := keys.set! i k
      types := types.set! i t
  return if keys == d.keys then { d with types } else .ofKeys keys types

/-- The traversal of `rewriteBelowBinders`: no lemma or simproc of its own, and an arrow's
    premise is a local, for the premises of the steps. -/
private def binderPassConfig : Simp.Config :=
  { contextual := true, singlePass := true, failIfUnchanged := false, beta := false, eta := false,
    etaStruct := .none, iota := false, proj := false, zeta := false, zetaDelta := false,
    dsimp := false, zetaUnused := false, zetaHave := false, letToHave := false,
    implicitDefEqProofs := false, index := false }

/-- Rewrite `e` with the steps `bs`, in one traversal. At a subterm the steps that match apply
    in stack order, each once, as in a round of the replay. A binder of a step is the one entered
    at its depth, a premise a hypothesis or an instance. Only steps `allowed` apply. With
    `dependent`, the traversal also rewrites the condition of a `dite'` (see `condition`).
    Returns `e'` and a proof of `e = e'`, `none` when no step applies. -/
private def rewriteBelowBinders (e : Expr) (bs : Array BinderStep) (index : BinderIndex)
    (allowed : Nat → Bool) (dependent := false) : MetaM (Option (Expr × Expr)) := do
  let lctx0 ← getLCtx
  let (r, _) ← Simp.main e (← Simp.mkContext binderPassConfig)
    (methods := { pre := pre lctx0, post := post lctx0 })
  return r.proof?.map (r.expr, ·)
where
  /-- The condition of the `dite'` that `e` applies, which the traversal leaves alone since the
      branches bind a hypothesis on it, rewritten on its own. The branches cast their hypothesis
      back to the old condition. -/
  condition (e : Expr) : SimpM (Option Simp.Result) := do
    let n := e.getAppNumArgs
    unless dependent && e.isAppOf ``Blaster.dite' && n ≥ 4 do return none
    let args := e.getAppArgs
    let r ← Simp.simp args[1]!
    let some h := r.proof? | return none
    if r.expr == args[1]! then return none
    let pf ← mkAppM ``Blaster.dite'_congr_cond #[h, args[2]!, args[3]!]
    -- the old branches applied to the casts, which `inferType` beta reduces
    let some (_, _, d) := (← inferType pf).eq? | return none
    let extra := args.extract 4 n
    let eNew := mkAppN d extra
    let pf ← extra.foldlM (init := pf) fun p a => mkCongrFun p a
    return some { expr := eNew, proof? := ← mkExpectedTypeHint pf (← mkEq e eNew) }
  /-- An arrow whose domain or body is not a Prop, which `simpArrow` traverses without entering
      its binder, rewritten with the binder entered, so that the binders entered are the binders
      open at the steps (see `BinderStep`). -/
  arrow (e : Expr) : SimpM (Option Simp.Result) := do
    let .forallE n d b bi := e | return none
    if b.hasLooseBVars then return none
    if (← isProp d) && (← isProp b) then return none
    let rd ← Simp.simp d
    let r ← Simp.mkImpCongr e rd { expr := b }
    withLocalDecl n bi rd.expr fun x => Simp.withNewLemmas #[x] do
      let rb ← Simp.simp b
      let some h := rb.proof? | return some r
      let eNew ← mkForallFVars #[x] rb.expr
      return some (← r.mkEqTrans { expr := eNew, proof? := ← mkAppM ``pi_congr #[← mkLambdaFVars #[x] h] })
  /-- The binders the traversal entered, innermost first, with their types. -/
  entered (lctx0 : LocalContext) : MetaM (Array (Expr × Expr)) :=
    return ((← getLCtx).foldl (init := #[]) fun a d =>
      if lctx0.contains d.fvarId then a else a.push (mkFVar d.fvarId, d.type)).reverse
  /-- A binder domain with a step instance, which the traversal leaves alone, is rewritten first,
      as `rewrite` does, since the steps below were pushed after it. A `∀` is rewritten whole, a
      `fun` with its application, as its own type changes with its domain. -/
  pre (lctx0 : LocalContext) (e : Expr) : SimpM Simp.Step := do
    -- not visited again, so that steps undoing each other at the condition stop
    if let some r ← condition e then return .continue r
    -- the steps on the arrow itself apply here, as `post` would
    if let some r ← arrow e then
      return .done <| ← match ← post lctx0 r.expr with
        | .visit r' | .continue (some r') => r.mkEqTrans r'
        | _ => pure r
    let ds ← match e with
      | .forallE _ d b _ => pure (if b.hasLooseBVars && !(← isProp d) then #[d] else #[])
      | .app .. => pure (e.getAppArgs.filterMap fun | .lam _ d _ _ => some d | _ => none)
      | _ => pure #[]
    if ds.isEmpty then return .continue
    let subs ← IO.mkRef (#[] : Array Expr)
    for d in ds do
      d.forEach fun x => unless x.hasLooseBVars do subs.modify (·.push x)
    let found := (← subs.get).foldl (init := #[]) fun a x =>
      a ++ ((index.candidates x).filter allowed).map (·, x)
    if found.isEmpty then return .continue
    let entered ← entered lctx0
    -- the motive depends on the instance only, not on the step
    let mut motives : Std.HashMap Expr (Option (Expr × Expr)) := {}
    for (i, x) in found.qsort (·.1 < ·.1) do
      let some r ← apply entered i x | continue
      let some pf := r.proof? | continue
      let m ← match motives[x]? with
        | some m => pure m
        | none => motiveOf e x
      motives := motives.insert x m
      let some (eAbst, motive) := m | continue
      let eNew := eAbst.instantiate1 r.expr
      return .visit { expr := eNew, proof? := ← mkExpectedTypeHint (← mkCongrArg motive pf) (← mkEq e eNew) }
    return .continue
  /-- `e` with the instances of `x` abstracted, and the motive that rewrites them, when it is type
      correct and the type of `e` does not depend on `x`. -/
  motiveOf (e x : Expr) : MetaM (Option (Expr × Expr)) := do
    let eAbst ← kabstract e x
    unless eAbst.hasLooseBVars do return none
    let motive := mkLambda `x .default (← inferType x) eAbst
    unless ← isTypeCorrect motive do return none
    -- an equation between the two sides needs a type the instance does not change
    if (← inferType motive).bindingBody!.hasLooseBVars then return none
    return some (eAbst, motive)
  post (lctx0 : LocalContext) (e : Expr) : SimpM Simp.Step := do
    unless (index.prefixCandidates e).any (allowed ·.1) do return .continue
    let entered ← entered lctx0
    let mut r : Simp.Result := { expr := e }
    let mut next := 0
    repeat
      let some (i, r') ← firstStep entered r.expr next | break
      r ← r.mkEqTrans r'
      next := i + 1
    return if r.proof?.isSome then .visit r else .continue
  /-- The first step from `next` on, in stack order, that rewrites `e` or a prefix of its
      application, and its result. -/
  firstStep (entered : Array (Expr × Expr)) (e : Expr) (next : Nat) :
      MetaM (Option (Nat × Simp.Result)) := do
    let n := e.headNumArgs
    for (i, k) in (index.prefixCandidates e).filter fun (i, _) => i ≥ next && allowed i do
      let some r ← apply entered i (e.getBoundedAppFn (n - k)) | continue
      if k == n then return some (i, r)
      let some pf := r.proof? | continue
      let args := e.getAppArgs.extract k n
      let pf ← args.foldlM (init := pf) mkCongrFun
      return some (i, { expr := mkAppN r.expr args, proof? := pf })
    return none
  apply (entered : Array (Expr × Expr)) (i : Nat) (e : Expr) : MetaM (Option Simp.Result) := do
    let s := bs[i]!
    -- each binder of the step is the binder entered at its depth, of its type
    unless s.depth.all (· < entered.size) do return none
    let es := s.depth.map (entered[·]!)
    let vs := es.map (·.1)
    let some (rest, differ) := pin index.types[i]! es vs | return none
    let saved ← saveState
    for (d, t) in differ do
      unless ← isDefEq d t do
        saved.restore
        return none
    let (xs, bis, ty) ← forallMetaTelescopeReducing rest
    let some (_, l, r) := (← whnfR ty).eq? | do saved.restore; return none
    let (l, r) := if s.symm then (r, l) else (l, r)
    -- at the transparency of `rewrite` in the replay
    if ← withReducible (isDefEq l e) <&&> premises xs bis then
      let pf ← instantiateMVars (mkAppN (s.thm.beta vs) xs)
      -- a step left with a metavariable or ill-typed is not applied
      if !pf.hasMVar && (← wellTypedStep pf) then
        return some { expr := ← instantiateMVars r, proof? := ← if s.symm then mkEqSymm pf else pure pf }
    saved.restore
    return none
  /-- `ty` instantiated with the binders `vs`, and each binder type of `ty` paired with the type
      in `es` of its binder when the two differ syntactically. -/
  pin (ty : Expr) (es : Array (Expr × Expr)) (vs : Array Expr) :
      Option (Expr × Array (Expr × Expr)) := Id.run do
    let mut rest := ty
    let mut differ := #[]
    for h : k in [:es.size] do
      let .forallE _ d b _ := rest | return none
      let d := d.instantiateRevRange 0 k vs
      if d != es[k].2 then differ := differ.push (d, es[k].2)
      rest := b
    return some (rest.instantiateRev vs, differ)
  /-- The arguments of the step's lemma that matching left open: an instance, or a premise. -/
  premises (xs : Array Expr) (bis : Array BinderInfo) : MetaM Bool := do
    for k in [:xs.size] do
      let x := xs[k]!
      if ← x.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType x)
      let v? ← if bis[k]!.isInstImplicit then synthInstance? ty
        else if ← isProp ty then pure ((← findLocalDeclWithType? ty).map mkFVar)
        else pure none
      let some v := v? | return false
      x.mvarId!.assign v
    return true

/-- Whether `e` may have a position the rest of the term depends on, where `kabstract` cannot
    rewrite: the condition of a `dite'`, or the domain of a `∀` over a proof its body uses. -/
private def hasDependentPosition (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  e.forEach fun s => do
    unless ← found.get do
      match s with
      | .forallE _ d b _ => if b.hasLooseBVar 0 && (← isPropQuick d) != .false then found.set true
      | _ => if s.isAppOfArity ``Blaster.dite' 4 then found.set true
  found.get

/-- How the replay left one intro'd binder. Its terms are in the context of the replayed goal. -/
structure ReplayedBinder where
  /-- The fvar and type of the binder before the replay rewrote it, up to unfolding. -/
  fvar : FVarId
  type : Expr
  /-- The fvar and type the replay left it with. -/
  final : FVarId
  finalType : Expr
  /-- A proof of `type = finalType`, when the replay rewrote the binder.
      The arguments of its lemmas are metavariables assigned by the replay. -/
  eq? : Option Expr
  deriving Inhabited

/-- Rewrite the intro'd Prop hypotheses with the recorded steps, so they reach the
    optimizer normal form that hypothesis-driven steps expect. `binders` records how each was
    left so far. With `dependent`, the traversal of every rewrite step rewrites those with a
    position `kabstract` cannot rewrite, as on the target once its rounds stall (see
    `replaySteps`), and not `kabstract`.
    Returns the new goal, the steps and the rewrite steps `all` with the replaced hypothesis fvars
    renamed, how each binder was left, and whether one is left with a dependent position. -/
private def rewriteHypotheses (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (all : Array BinderStep) (binders : Array ReplayedBinder) (dependent : Bool)
    (cache : IO.Ref CanonCache) :
    MetaM (MVarId × Array Blaster.Optimize.ProofStep × Array BinderStep ×
      Array ReplayedBinder × Bool) := do
  let mut g := goal
  let mut steps := steps
  let mut all := all
  -- whether a step is below binders, which the traversal applies anywhere
  let below := all.any (!·.outside)
  -- the index of `all`, built when a traversal first runs
  let mut index? : Option BinderIndex := none
  let mut binders := binders
  let mut hs := binders.map (·.final)
  let mut pending := false
  for i in [:binders.size] do
    let b := binders[i]!
    let mut h := hs[i]!
    let mut ty ← g.withContext do instantiateMVars (← h.getType)
    -- a binder not rewritten yet starts where the replay reaches it
    let start := if b.eq?.isSome then (b.fvar, b.type) else (h, ty)
    let mut eq? := b.eq?
    -- the type the steps below binders last left as it was, which they would leave again
    let mut idle : Option Expr := none
    -- with `dependent`, a hypothesis `kabstract` rewrites throughout is left as the rounds before
    unless ← g.withContext (isProp ty <&&> (pure !dependent <||> hasDependentPosition ty)) do
      binders := binders.set! i { fvar := start.1, type := start.2, final := h, finalType := ty, eq? }
      continue
    -- a round is a function of the type, so a type a round already started from means steps
    -- undoing each other, which would loop
    let mut seen : Std.HashSet Expr := {}
    let mut changed := true
    while changed do
      if seen.contains ty then break
      seen := seen.insert ty
      changed := false
      -- index into the current `steps`, whose proofs are renamed after each replacement, and
      -- `steps.size` for the steps below binders, applied together, or every rewrite step
      -- when `dependent`
      for j in [:steps.size + 1] do
        -- as on the target, so that a hypothesis and the target unfold alike
        if let some (.unfold n) := steps[j]? then
          let ty' ← deltaExpand ty (· == n)
          if ty' != ty then
            let ty' ← g.withContext (canonicalForm cache ty')
            -- definitional, so the hypothesis keeps its fvar
            g ← g.replaceLocalDeclDefEq h ty'
            ty := ty'
            changed := true
        -- a step built from this hypothesis or a later one cannot have normalized it
        let later (p : Expr) := p.hasAnyFVar (hs.extract i hs.size).contains
        let mut rw? : Option (Expr × Expr) := none
        if j == steps.size && (dependent || below && idle != some ty) then
          let index ← match index? with
            | some i => pure i
            | none => g.withContext (indexBinderSteps cache all)
          index? := some index
          rw? ← g.withContext (rewriteBelowBinders ty all index
            (fun k => (dependent || !all[k]!.outside) && !later all[k]!.thm) dependent)
          if rw?.isNone then idle := some ty
        try
          if let some (.rewrite heq symm _) := steps[j]? then
            unless dependent || later heq do
              let r ← g.rewrite ty (← g.withContext (withCanonicalType cache heq)) symm
              checkHypStep g heq
              rw? := some (r.eNew, r.eqProof)
          if let some (eNew, eqProof) := rw? then
            -- in the replay spelling, which the term a step inserts may leave around it, e.g. a
            -- Nat numeral substituted under `Int.ofNat`
            let eNew ← g.withContext (canonicalForm cache eNew)
            let res ← g.replaceLocalDecl h eNew eqProof
            -- `eqProof` proves `ty = eNew` up to the spelling of `eNew`
            eq? := some <| match eq? with
              | none => eqProof
              | some e => mkApp6 (mkConst ``Eq.trans [1]) (mkSort 0) start.2 ty eNew e eqProof
            -- the replaced hypothesis and every later local got fresh fvars
            let s := res.subst.insert h (mkFVar res.fvarId)
            steps := steps.map fun
              | .rewrite proof symm _ => .rewrite (s.apply proof) symm
              | .exact proof => .exact (s.apply proof)
              | s@(.unfold _) => s
            let old := all
            all := all.map fun b => { b with thm := s.apply b.thm }
            index? ← res.mvarId.withContext (index?.mapM (·.reindex cache old all))
            hs := hs.map fun f => (s.get f).fvarId!
            -- the records of the later binders already rewritten follow the renaming
            binders := binders.mapIdx fun k b => if k ≤ i || b.eq?.isNone then b else { b with
              fvar := (s.get b.fvar).fvarId!, type := s.apply b.type
              final := (s.get b.final).fvarId!, finalType := s.apply b.finalType
              eq? := b.eq?.map s.apply }
            g := res.mvarId
            h := res.fvarId
            ty := eNew
            changed := true
        catch _ => pure ()
    binders := binders.set! i { fvar := start.1, type := start.2, final := h, finalType := ty, eq? }
    if !pending then pending ← g.withContext (hasDependentPosition ty)
  return (g, steps, all, binders, pending)

/-- Rewrite the hypotheses, then apply the steps to the target until none applies, it is
    reflexive, or a round would start again from a target already seen, those below binders once
    per round, together in one traversal of the rewrite steps `all` (in stack order, each as a
    `BinderStep`). Steps that don't match are skipped. A round that changes nothing leaves the
    target open, unless it or a hypothesis has a position `kabstract` cannot rewrite (see
    `hasDependentPosition`). From then on the hypotheses with such a position and the target are
    rewritten with the traversal of every rewrite step, which reaches that position, and no longer
    with `kabstract`, until a round changes nothing. The hypotheses wait for that stall, so that a
    step closing the target with one of them finds both alike. With `records`, a target left
    reflexive before it, which the caller closes, still gets them rewritten, for their records. -/
private def replaySteps (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (all : Array BinderStep) (hyps : Array FVarId) (cache : IO.Ref CanonCache) (records : Bool) :
    MetaM (MVarId × Array ReplayedBinder) := do
  let binders ← goal.withContext <| hyps.mapM fun h => do
    let ty ← instantiateMVars (← h.getType)
    return { fvar := h, type := ty, final := h, finalType := ty, eq? := none }
  -- whether a hypothesis waits for the stall, at a position `kabstract` cannot rewrite
  let (goal, steps, all, binders, pending) ← rewriteHypotheses goal steps all binders false cache
  let mut steps := steps
  let mut all := all
  let mut binders := binders
  /- trace[Optimize.expr] "proofStack ({steps.size} steps):" -/
  /- let mut idx : Nat := 0 -/
  /- for step in steps do -/
  /-   match step with -/
  /-   | .rewrite heq symm => -/
  /-     let ty ← inferType heq -/
  /-     trace[Optimize.expr] "  [{idx}] rewrite{if symm then " (symm)" else ""}: {ty}" -/
  /-   | .exact proof => -/
  /-     let ty ← inferType proof -/
  /-     trace[Optimize.expr] "  [{idx}] exact: {ty}" -/
  /-   idx := idx + 1 -/
  let mut g := goal
  /- trace[Optimize.expr] "initial goal: {← g.getType}" -/
  -- whether a step is below binders, which the traversal applies anywhere
  let below := all.any (!·.outside)
  -- the index of `all`, built when a traversal first runs
  let mut index? : Option BinderIndex := none
  -- the target the steps below binders last left as it was, which they would leave again
  let mut idle : Option Expr := none
  -- a target a step left reflexive is closed by `refl`, before a later step rewrites it again
  let reflexive (g : MVarId) : MetaM Bool := do
    return (← instantiateMVars (← g.getType)).eq?.any fun (_, l, r) => l == r
  -- as on the hypotheses, a target a round already started from means steps undoing each other
  let mut seen : Std.HashSet Expr := {}
  -- whether the rounds stalled, so that the traversal rewrites, not `kabstract`
  let mut stalled := false
  let mut changed := true
  while changed do
    let t ← g.getType
    if seen.contains t then break
    seen := seen.insert t
    changed := false
    for step in steps do
      if ← reflexive g then break
      match step with
      | .rewrite heq symm _ =>
        if stalled then continue
        try
          let t ← g.getType
          let r ← g.rewrite t (← g.withContext (withCanonicalType cache heq)) symm
          checkHypStep g heq
          -- in the replay spelling, as on the hypotheses
          g ← g.replaceTargetEq (← g.withContext (canonicalForm cache r.eNew)) r.eqProof
          -- a rewrite between defeq spellings may leave the target as is and must not loop
          if (← g.getType) != t then changed := true
          /- trace[Optimize.expr] "  applied rewrite → {← g.getType}" -/
        catch _ => pure ()
      | .exact proof =>
        let s ← saveState
        try
          -- the target is in the replay spelling and the statement is compared with it at
          -- reducible-and-instances transparency, so a recursive target is not unfolded; the
          -- `.exact` emitters give statements in that spelling up to this transparency
          -- the proof's extra binders are the ones the replay introduced, found by assumption
          let closed ← g.withContext do withReducibleAndInstances do
            let pt ← inferType proof
            let target ← g.getType
            -- as `MVarId.apply`, the fewest binders whose conclusion matches the target, at the replay's transparency
            for k in [:(← forallTelescopeReducing pt fun xs _ => pure xs.size) + 1] do
              let (xs, _, body) ← forallMetaBoundedTelescope pt k
              unless ← isDefEq body target do continue
              checkHypStep g proof
              g.assign (mkAppN proof xs)
              -- last first, so a premise fixes the binders its type depends on
              for x in xs.reverse do
                unless ← x.mvarId!.isAssigned do x.mvarId!.assumption
              return !(← instantiateMVars (mkMVar g)).hasMVar
            return false
          if closed then
            /- trace[Optimize.expr] "  applied exact, goal closed" -/
            return (g, binders)
          s.restore
        catch _ => s.restore
      | .unfold n =>
        let t ← g.getType
        let t' ← deltaExpand t (· == n)
        -- a no-op unfolding is not a change, or the loop would never end
        if t' != t then
          -- the unfolded body is user code, put in the replay spelling
          g ← g.replaceTargetDefEq (← g.withContext (canonicalForm cache t'))
          changed := true
    if ← reflexive g then
      -- the hypotheses waiting for the stall are rewritten all the same, for their records
      if records && pending && !stalled then
        let (g', _, _, binders', _) ← rewriteHypotheses g steps all binders true cache
        return (g', binders')
      return (g, binders)
    -- the steps below binders, together in one traversal of the target
    let t ← g.getType
    if !stalled && below && idle != some t then
      let index ← match index? with
        | some i => pure i
        | none => g.withContext (indexBinderSteps cache all)
      index? := some index
      if let some (eNew, eqProof) ← g.withContext (rewriteBelowBinders t all index (!all[·]!.outside)) then
        g ← g.replaceTargetEq (← g.withContext (canonicalForm cache eNew)) eqProof
      if (← g.getType) != t then changed := true else idle := some t
    unless changed do
      unless stalled do
        unless pending || (← g.withContext (hasDependentPosition (← g.getType))) do break
        stalled := true
        let (g', steps', all', binders', _) ← rewriteHypotheses g steps all binders true cache
        index? ← g'.withContext (index?.mapM (·.reindex cache all all'))
        if g' != g then
          changed := true
          -- the hypotheses changed, so a target already seen starts a round again
          seen := {}
        g := g'
        steps := steps'
        all := all'
        binders := binders'
      let t ← g.getType
      let index ← match index? with
        | some i => pure i
        | none => g.withContext (indexBinderSteps cache all)
      index? := some index
      if let some (eNew, eqProof) ← g.withContext (rewriteBelowBinders t all index (fun _ => true) true) then
        g ← g.replaceTargetEq (← g.withContext (canonicalForm cache eNew)) eqProof
        if ← reflexive g then return (g, binders)
        if (← g.getType) != t then changed := true
  /- trace[Optimize.expr] "final goal: {← g.getType}" -/
  -- the target may have been reduced to a hypothesis
  unless ← g.isAssigned do
    try g.assumption catch _ => pure ()
  return (g, binders)

/-- `true` iff `g` is assigned, `True` (then closed) or closed by `refl`. -/
private def closeTrivially (g : MVarId) : MetaM Bool := do
  if ← g.isAssigned then return true
  if (← instantiateMVars (← g.getType)).isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return true
  try g.refl; return true catch _ => return false

/-- Apply recorded proof stack rewrites to a goal.
    `hyps` are the intro'd binders, rewritten first (see `rewriteHypotheses`).
    Returns the goal left and how the replay left each of `hyps`, which a caller reading it asks
    with `records` (see `replaySteps`). -/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId := #[]) (records := false) : MetaM (MVarId × Array ReplayedBinder) := do
  -- the hypotheses, the target and the steps are put once in one spelling
  let cache ← IO.mkRef {}
  let goal ← hyps.foldlM (init := goal) fun g h => g.withContext do
    let ty ← instantiateMVars (← h.getType)
    let ty' ← canonicalForm cache ty
    if ty' != ty then g.replaceLocalDeclDefEq h ty' else pure g
  let goal ← goal.withContext do
    let t ← instantiateMVars (← goal.getType)
    let t' ← canonicalForm cache t
    if t' != t then goal.replaceTargetDefEq t' else pure goal
  let (steps, all) ← goal.withContext do
    let mut plain : Array Blaster.Optimize.ProofStep := #[]
    let mut all := #[]
    for s in steps do
      match s with
      | .rewrite proof symm bs =>
        let proof ← canonicalForm cache proof
        let bs ← bs.mapM fun b => return { b with type := ← canonicalForm cache b.type }
        let b? ← closeOverBinders proof symm bs
        -- `kabstract` applies a step out of binders, and one the replay cannot map fails there
        -- as before
        unless b?.any (!·.outside) do plain := plain.push (.rewrite proof symm)
        if let some b := b? then all := all.push b
      | .exact proof => plain := plain.push (.exact (← canonicalForm cache proof))
      | s => plain := plain.push s
    return (plain, all)
  replaySteps goal steps all hyps cache records

/-- Custom sorry for Blaster to differentiate
    between SMT-verified goals and regular `sorry`.-/
private axiom blasterProven : ∀ {α : Sort u}, α

private def blasterAdmit (mvarId : MVarId) : MetaM Unit :=
  mvarId.withContext do
    mvarId.checkNotAssigned `blasterAdmit
    let mvarType ← mvarId.getType >>= instantiateMVars
    let u ← getLevel mvarType
    mvarId.assign (mkApp (mkConst ``blasterProven [u]) mvarType)

/-- Warn that the proof uses `blasterProven`, unless `warn.sorry` is false, as for `sorry`:
    with `gap` when `optimizerClosed`, since then the optimizer proved the goal by rewriting and
    the replay should have reconstructed it, else with the text of an SMT-verified goal. -/
private def warnBlasterProven (optimizerClosed : Bool) (gap : MessageData) : MetaM Unit := do
  unless (← getOptions).getBool `warn.sorry true do return
  if optimizerClosed then logWarning gap
  else logWarning "declaration uses 'blasterProven' (SMT-verified, no proof term)"

/-- Introduce the binders of `goalType` and apply the proof stack, with `records` as in
    `applyProofStack`. In the steps, the first optimizer binders `optBinders`, as many as the
    introduced binders, are replaced by these in order (see `pairBinders`), and in the steps
    `othersIn` accepts, each of `others`, an optimizer binder paired with an index, by the
    introduced binder at that index.
    Returns the proof of `goalType`, the goal the replay left in it and how it left each binder. -/
private def replayProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array (Option FVarId)) (records := false) (others : Array (FVarId × Nat) := #[])
    (othersIn : Blaster.Optimize.ProofStep → Bool := fun _ => true) :
    MetaM (Expr × MVarId × Array ReplayedBinder) := do
  let proofMVar ← mkFreshExprMVar goalType
  let numBinders ← forallTelescope goalType fun fvars _ => pure fvars.size
  let (goalFVarIds, g) ← proofMVar.mvarId!.introNP numBinders
  let (opt, goal) := pairBinders optBinders goalFVarIds
  let proofStack := substProofStackFVars proofStack opt goal
  let proofStack := substProofStackFVars proofStack (others.map (·.1))
    (others.map (goalFVarIds[·.2]!)) othersIn
  let (g, binders) ← applyProofStack g proofStack goalFVarIds records
  return (proofMVar, g, binders)

/-- Close with refl the goal `g` that the replay of `numSteps` steps left in `proofMVar`, a proof
    of `goalType`.
    On failure, admit via `blasterProven` with one `warnBlasterProven`, or throw when `admit` is
    false. -/
private def closeReplay (goalType proofMVar : Expr) (g : MVarId) (numSteps : Nat)
    (optimizerClosed admit : Bool) : MetaM Expr := do
  let closed ← closeTrivially g
  unless closed do
    unless admit do throwError m!"blaster: reconstruction gap\n{.ofGoal g}"
    warnBlasterProven optimizerClosed
      m!"blaster: reconstruction gap ({numSteps} steps), admitted via `blasterProven`\n{.ofGoal g}"
    blasterAdmit g
  -- a step may carry an optimizer fvar the replay did not map, which the kernel would reject
  let pf ← instantiateMVars proofMVar
  let lctx ← getLCtx
  unless pf.hasFVar && (collectFVars {} pf).fvarIds.any (!lctx.contains ·) do
    return proofMVar
  unless admit do throwError "blaster: reconstruction gap (unmapped free variable)"
  -- a goal the replay left has already warned
  if closed then
    warnBlasterProven optimizerClosed
      m!"blaster: reconstruction gap (unmapped free variable), admitted via `blasterProven`"
  let m ← mkFreshExprMVar goalType
  blasterAdmit m.mvarId!
  return m

/-- Prove a goal by `replayProofStack`, then `closeReplay`. -/
private def proveByProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array (Option FVarId)) (optimizerClosed : Bool) (admit := true) :
    MetaM (Expr × Array ReplayedBinder) := do
  let (proofMVar, g, binders) ← replayProofStack goalType proofStack optBinders
  return (← closeReplay goalType proofMVar g proofStack.size optimizerClosed admit, binders)

/-- The instance arguments of the proofs of `steps`, in the optimizer context.
    They carry the instances the optimizer built, e.g. the `Nonempty` of an eliminated binder. -/
private def stepInstances (steps : Array Blaster.Optimize.ProofStep) : MetaM (Array Expr) := do
  let mut insts := #[]
  for s in steps do
    let p ← match s with
      | .rewrite p _ _ | .exact p => pure p
      | .unfold _ => continue
    let .const c _ := p.getAppFn | continue
    let mut ty := (← getConstInfo c).type
    for a in p.getAppArgs do
      let .forallE _ _ b bi := ty | break
      if bi.isInstImplicit then insts := insts.push a
      ty := b
  return insts

/-- The instances `insts` of the steps (see `stepInstances`) given the first lhs arguments
    `args`, which the optimizer binders `optBinders` stand for (see `pairBinders`), those the
    context holds. -/
private def instancesAt (insts : Array Expr) (optBinders : Array (Option FVarId))
    (args : Array Expr) : MetaM (Array Expr) := do
  let (opt, args) := pairBinders optBinders args
  let lctx ← getLCtx
  return (insts.map (·.replaceFVars (opt.map mkFVar) args)).filter fun a =>
    !a.hasAnyFVar (!lctx.contains ·)

/-- An inhabitant of the non-Prop type `t` by `mkInhabitantFor`, with `insts` as local instances
    and the values of `params` as candidates, reduced so that `Sort u` gives `PUnit` and the next
    binders of that type find an instance. -/
private def inhabitant (t : Expr) (insts params : Array Expr) : MetaM Expr := do
  let rec go (i : Nat) (fvars : Array Expr) : MetaM Expr := do
    if h : i < insts.size then
      withLetDecl `inst (← inferType insts[i]) insts[i] fun x => go (i + 1) (fvars.push x)
    else
      -- the inhabitant is abstracted over `params`
      let v ← mkInhabitantFor m!"blaster: an eliminated binder" params t
      whnf ((v.beta params).replaceFVars fvars insts)
  go 0 #[]

/-- `true` iff `proveForallEq` can transport the binders `xs` of `lhs` to the binders `ys` of
    `rhs` they are matched with by `idx`, `Q` being the body of `rhs`: each matched pair has the
    same type, or is a hypothesis on which `rhs` does not depend. Whether the replay rewrites
    that hypothesis into the `rhs` type is only known after it, in `proveForallEq`. -/
private def forallEqTransports (xs ys : Array Expr) (Q : Expr) (idx : Array (Option Nat)) :
    MetaM Bool := do
  let (f, t) := matchedPairs xs ys idx
  for j in [:ys.size] do
    let some i := idx[j]! | continue
    let x := xs[i]!
    let ty := (← inferType ys[j]!).replaceFVars f t
    unless ← isDefEq (← inferType x) ty do
      unless ← isProof x do return false
      let y := ys[j]!.fvarId!
      if Q.containsFVar y || (← (ys.extract (j + 1) ys.size).anyM fun y' => do
          return (← inferType y').containsFVar y) then
        return false
  return true

/-- Prove `(∀ xs, P) = (∀ ys, Q)`, with the first `p` binders of `lhs` and `q` of `rhs` opened
    and matched by `matchBinders`, from a single replay of `∀ xs, P = Q`, when
    `forallEqTransports` holds. The opened binders of `lhs` without a match are those that
    `proveGoalByProofStack` finds the COI rule eliminates, so the equation holds whatever their
    value, and the hypotheses before one that only opening eliminates.
    The replay rewrites the hypotheses, so its record of each binder gives
    - for a kept hypothesis whose type changes, the equation that casts it,
    - for an eliminated hypothesis, the type it was rewritten to, closed when trivial, else the
      goal is left as a gap.
    An eliminated binder that is not a proof, on either side, gets an `inhabitant`, with the
    instances `insts` the steps carry (see `stepInstances`). Without one, the goal is left as a
    gap. -/
private def proveForallEq (lhs rhs : Expr) (p q : Nat) (idx : Array (Option Nat))
    (steps : Array Blaster.Optimize.ProofStep) (optBinders rhsBinders : Array (Option FVarId))
    (insts : Array Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  forallBoundedTelescope lhs (some p) fun xs P => forallBoundedTelescope rhs (some q) fun ys Q => do
    let (f, t) := matchedPairs xs ys idx
    let toX (e : Expr) := e.replaceFVars f t
    let innerType ← mkForallFVars xs (← mkEq P (toX Q))
    -- `rhsBinders`, given only when the goal is the optimizer's input, records the head binders
    -- of `rhs` in order, up to a cached forall or a `False` binder: the fvar of each opened `y`,
    -- `none` for one dropped before it was opened. `others` maps each opened `y` that `idx`
    -- matches to its binder of `lhs`, in the steps `onQ` accepts: the rewrites recorded below the
    -- last opened `y`, and the steps that record no binder. Mapped, the other steps on `rhs`,
    -- outside the replayed equation, would rewrite the binders of `lhs` too.
    let others := (List.range ys.size).toArray.filterMap fun j => do
      return (← rhsBinders[j]?.join, ← idx[j]!)
    let last := ((rhsBinders.extract 0 ys.size).filterMap id).back?
    let onQ : Blaster.Optimize.ProofStep → Bool
      | .rewrite _ _ bs => bs.any (some ·.fvar == last)
      | _ => true
    -- out of the telescopes, or the replay could close it with one of their fvars
    let (inner, g, bs) ← withLCtx lctx localInsts do
      replayProofStack innerType steps optBinders (records := true) others onQ
    let rhsOf (i : Nat) := idx.findIdx? (· == some i)
    let inner ← withLCtx lctx localInsts do
      closeReplay innerType inner g steps.size false (admit := false)
    -- the equations are only needed here, so their lemma arguments are instantiated here
    let bs ← bs.mapM fun b => return { b with eq? := ← b.eq?.mapM instantiateMVars }
    let instsAt := instancesAt insts optBinders
    -- given the lhs arguments, the rhs binders and the steps' instances in the current context
    let fwd ← withLocalDeclD `h lhs fun h => do
      let mut xargs := #[]
      -- the replay fvars of the binders already given, and their values
      let mut fs := #[]
      let mut vs := #[]
      for i in [:xs.size] do
        let b := bs[i]!
        let t := b.type.replaceFVars fs vs
        let ft := b.finalType.replaceFVars fs vs
        let e? := b.eq?.map (·.replaceFVars fs vs)
        -- the value of the binder and of its rewritten form
        let (x, z) ← match rhsOf i with
          | some j => do
            let y := ys[j]!
            let ty ← inferType y
            if ← isDefEq ty t then
              pure (y, ← e?.elim (pure y) (mkEqMP · y))
            else
              unless e?.isSome && (← isDefEq ty ft) do
                throwError m!"blaster: the replay leaves the binder {xs[i]!} with type{indentExpr ft}
not{indentExpr ty}"
              pure (← mkEqMPR e?.get! y, y)
          | none =>
            if ← isProp ft then
              let m ← mkFreshExprMVar ft
              unless ← closeTrivially m.mvarId! do
                throwError "blaster: the eliminated hypothesis {xs[i]!} is rewritten to {ft}"
              let z ← instantiateMVars m
              pure (← e?.elim (pure z) (mkEqMPR · z), z)
            else
              let v ← inhabitant t (← instsAt xargs) ys
              pure (v, v)
        xargs := xargs.push x
        fs := fs.push (mkFVar b.fvar)
        vs := vs.push x
        if b.final != b.fvar then
          fs := fs.push (mkFVar b.final)
          vs := vs.push z
      mkLambdaFVars (#[h] ++ ys) (← mkAppM ``cast #[mkAppN inner xargs, mkAppN h xargs])
    let bwd ← withLocalDeclD `h rhs fun h => do
      let mut zs := #[]
      let mut fs := #[]
      let mut vs := #[]
      for i in [:xs.size] do
        let b := bs[i]!
        let z ← b.eq?.elim (pure xs[i]!) fun e => mkEqMP (e.replaceFVars fs vs) xs[i]!
        zs := zs.push z
        fs := fs.push (mkFVar b.fvar)
        vs := vs.push xs[i]!
        if b.final != b.fvar then
          fs := fs.push (mkFVar b.final)
          vs := vs.push z
      let insts ← instsAt xs
      let mut yargs := #[]
      for j in [:ys.size] do
        let ty := (← inferType ys[j]!).replaceFVars (ys.extract 0 j) yargs
        let some i := idx[j]! | yargs := yargs.push (← inhabitant ty insts xs)
        let a ← if ← isDefEq ty (← inferType xs[i]!) then pure xs[i]!
          else if ← isDefEq ty (← inferType zs[i]!) then pure zs[i]!
          else throwError "blaster: the type of the binder {xs[i]!} changes"
        yargs := yargs.push a
      mkLambdaFVars (#[h] ++ xs) (← mkAppM ``cast #[← mkEqSymm (mkAppN inner xs), mkAppN h yargs])
    let pf ← mkAppM ``propext #[← mkAppM ``Iff.intro #[fwd, bwd]]
    -- the records of the replay are in its own context, none of whose fvars may be left
    if pf.hasAnyFVar (!lctx.contains ·) then throwError "blaster: a replay fvar is left in the proof"
    return pf

/-- Prove `goalType`, a goal the optimizer found valid, from its proof stack, with the goal
    binders the optimizer recorded, `optBinders` and `rhsBinders` (see `goalSpineSide?`).
    `rhsBinders` stand for binders of `rhs` only when `goalType` is the optimizer's input and is
    itself the equation (for `∀ a, A = B` the replay on the whole goal ignores them), so a caller
    that proves another goal, as the gate does with `input = expected`, passes none.
    An equation of foralls whose binders `matchBinders` matches and `forallEqTransports`
    accepts is proved by `proveForallEq`, with the binders of `lhs` opened up to the first one
    without a match that the COI rule may not eliminate, or up to the last one that only opening
    eliminates, when later. Any other goal, or one where no binder is opened, is proved by the
    replay on the whole goal, whose `refl` closes sides equal up to binder names. A gap reports
    the goal of the path taken.
    The choice is static and rests on two premises: no rule of the optimizer but COI drops a
    binder that is not a proof, and a binder without a match stands for a binder of `rhs` only
    when the body of `rhs` unfolds to a forall over one that is not a proof. The stack does not
    tell which binder a COI step eliminated, as the step names only the type and the body, so a
    goal out of these premises takes a route that leaves it as a gap.
    A replay that fails, or whose proof depends on `sorryAx`, is a gap, admitted via
    `blasterProven`, or an error when `admit` is false, as in the `#testOptimize` gate. -/
def proveGoalByProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders rhsBinders : Array (Option FVarId)) (optimizerClosed : Bool) (admit := true) :
    MetaM Expr := do
  -- the optimizer sees the goal without its `let`s, so its binders are found below them
  let goalType ← if (hasLet goalType {}).1 then zetaLets goalType else pure goalType
  -- the numbers of `lhs` and `rhs` binders to open, when the goal is an equation of foralls they
  -- match
  let forallEq? : MetaM (Option (Expr × Expr × Nat × Nat × Array (Option Nat) × Array Expr)) := do
    let some (_, lhs, rhs) := goalType.eq? | return none
    unless ← isProp lhs do return none
    let numBinders ← forallTelescope lhs fun fvars _ => pure fvars.size
    if numBinders == 0 || rhs.isConstOf ``True then return none
    -- only the binders `rhs` shows, as opening more unfolds its body (e.g. `¬ a`), so a
    -- hypothesis a rule folds into that body is left unmatched, and stays in the bodies
    let k := min numBinders rhs.getNumHeadForalls
    -- the other equations go to the replay on the whole goal, e.g. a binder type with a
    -- rewritten closed subterm
    let insts ← stepInstances proofStack
    let some (p, q, idx) ← forallTelescope lhs fun xs P =>
        forallBoundedTelescope rhs (some k) fun ys Q => do
          let xElim ← coiEliminated xs P ys
          let some idx ← matchBinders ys xs xElim (← coiEliminated ys Q xs) | return none
          -- a binder without a match may be opened when the COI rule eliminates it, as the
          -- equation then holds whatever its value: `coiEliminated` tells so before optimization,
          -- and a binder that is not a proof is eliminated after it too, as no other rule drops
          -- one, unless `Q` hides a binder it may stand for. Any other one stays in the bodies,
          -- as a rule on the rest of the forall may consume it.
          let hidesData ← forallTelescopeReducing Q fun zs _ =>
            zs.anyM fun z => return !(← isProof z)
          let stays (i : Nat) : MetaM Bool := do
            return !idx.contains (some i) && !xElim[i]! && (hidesData || (← isProof xs[i]!))
          -- the replay applies the step of the COI rule with the `Nonempty` instance the step
          -- carries, else with one it synthesizes, so an eliminated binder of a type with
          -- neither is eliminated only opened, with an `inhabitant`
          let stepInsts ← instancesAt insts optBinders xs
          let opened ← (List.range xs.size).filterM fun i => do
            if idx.contains (some i) || (← stays i) then return false
            let ne ← mkAppM ``Nonempty #[← inferType xs[i]!]
            if ← stepInsts.anyM fun a => do isDefEq (← inferType a) ne then return false
            return (← synthInstance? ne).isNone
          -- the binders before the first that stays are opened, and those up to the last that is
          -- eliminated only opened, a hypothesis that stays included, as a replay of a body with
          -- that binder in it cannot eliminate it. The binders left stay in the bodies, with the
          -- `ys` matched with them.
          let p := max ((← (List.range xs.size).findM? stays).getD xs.size)
            ((opened.getLast?.map (· + 1)).getD 0)
          let q := (idx.findIdx? fun | some i => i ≥ p | none => false).getD ys.size
          let Q ← mkForallFVars (ys.extract q ys.size) Q
          let (xs, ys, idx) := (xs.extract 0 p, ys.extract 0 q, idx.extract 0 q)
          return if p > 0 && (← forallEqTransports xs ys Q idx) then some (p, q, idx) else none
      | return none
    return some (lhs, rhs, p, q, idx, insts)
  let prove : MetaM Expr := do
    match goalType.eq? with
    | some (_, lhs, rhs) =>
      -- `P = True`: prove P directly, then lift via eq_true
      if rhs.isConstOf ``True && (← isProp lhs) then
        let (pf, _) ← proveByProofStack lhs proofStack optBinders optimizerClosed admit
        return ← mkAppM ``eq_true #[pf]
    | none => pure ()
    if let some (lhs, rhs, p, q, idx, insts) ← forallEq? then
      return ← proveForallEq lhs rhs p q idx proofStack optBinders rhsBinders insts
    return (← proveByProofStack goalType proofStack optBinders optimizerClosed admit).1
  -- the proof may depend on `sorryAx`, through a term of the optimizer it embeds or a definition
  -- the optimizer unfolds whose body has a `sorry`: it is then a gap, whatever the path
  let proveSorryFree : MetaM Expr := do
    let pf ← instantiateMVars (← prove)
    if containsSorry pf then throwError "the proof depends on `sorryAx`"
    return pf
  let s ← saveState
  -- also a replay out of heartbeats, whose admission then needs a fresh count. The restored
  -- state drops the warning of a gap the replay admitted, so the admission warns once
  tryCatchRuntimeEx proveSorryFree fun e => do
    s.restore
    unless admit do throw e
    warnBlasterProven optimizerClosed
      m!"blaster: reconstruction gap, admitted via `blasterProven`\n{e.toMessageData}"
    withCurrHeartbeats do
      let m ← mkFreshExprMVar goalType
      blasterAdmit m.mvarId!
      return m

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts default
   let goal ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let ((result, optExpr), finalEnv) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType) (logUndetermined := false) |>.run env
   let proofStack := finalEnv.proofEnv.proofStack
   let optBinders := finalEnv.proofEnv.optBinders.goal
   let rhsBinders := finalEnv.proofEnv.optBinders.rhs
   match result with
   | .Valid =>
        -- `optExpr == True` ⟹ proved by rewriting (no SMT)
        let optimizerClosed := optExpr.isConstOf ``True
        goal.assign (← proveGoalByProofStack (← goal.getType) proofStack optBinders rhsBinders
          optimizerClosed)
   | .Falsified cex => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
   | .Undetermined =>
        let newGoal ← goal.replaceTargetDefEq optExpr
        replaceMainGoal [newGoal]

  where

    @[always_inline, inline]
    revertHypotheses (goal : MVarId) : TacticM MVarId :=
      goal.withContext $ do
        -- Get all hypotheses from the local context
        let lctx ← getLCtx
        let mut hyps := #[]
        for decl in lctx do
          if decl.isImplementationDetail then continue
          if ← isProp decl.type then
            hyps := hyps.push decl.fvarId
        -- revert hyp from context
        hyps.foldrM
          (fun h g => do
             let (_, g) ← g.revert #[h]
             return g) goal

end Blaster.Tactic
