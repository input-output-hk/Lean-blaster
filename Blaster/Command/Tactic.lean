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
    into the conversion of `e`. -/
private inductive ElabTask where
  | visit (e : Expr)
  | un (e : Expr) (op : Expr → Expr)
  | bin (e : Expr) (op : Expr → Expr → Expr)
  deriving Inhabited

/-- Convert core Nat/Int operators, `String.append` and the raw Int literals `Int.ofNat n`,
    `Int.negSucc n` to their elaborated form, `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv`,
    `HMod.hMod`, `HAppend.hAppend`, `Neg.neg` and `OfNat.ofNat`,
    so that proof term LHS patterns structurally match goal expressions.
    The operator fixes the instances, so the result is definitional whatever the operand type.
    `cache` maps the subterms converted so far to their result and is returned extended,
    so each subterm is converted once, also when shared (up to binder names).
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
      if let some r := cache[e]? then done := done.push r
      else match visit e with
        | .inl r => done := done.push r
        | .inr ts => todo := todo ++ ts
    | .un e op =>
      let r := op done.back!
      cache := cache.insert e r
      done := done.pop.push r
    | .bin e op =>
      let r := op done.pop.back! done.back!
      cache := cache.insert e r
      done := done.pop.pop.push r
  return (done.back!, cache)
where
  /-- Tasks that convert `a` with `op`, in reverse order since `todo` is a stack. -/
  un (e : Expr) (op : Expr → Expr) (a : Expr) : Array ElabTask := #[.un e op, .visit a]
  /-- Tasks that convert `a` and `b`, then combine them with `op`. -/
  bin (e : Expr) (op : Expr → Expr → Expr) (a b : Expr) : Array ElabTask :=
    #[.bin e op, .visit b, .visit a]
  /-- The converted leaf `e`, or the tasks converting it. -/
  visit (e : Expr) : Expr ⊕ Array ElabTask :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) a) b => .inr (bin e mkNatAdd a b)
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) a) b => .inr (bin e mkNatSub a b)
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) a) b => .inr (bin e mkNatMul a b)
  | Expr.app (Expr.app (Expr.const ``Int.add _) a) b => .inr (bin e mkIntAdd a b)
  | Expr.app (Expr.app (Expr.const ``Int.sub _) a) b => .inr (bin e mkIntSub a b)
  | Expr.app (Expr.app (Expr.const ``Int.mul _) a) b => .inr (bin e mkIntMul a b)
  | Expr.app (Expr.app (Expr.const ``Int.ediv _) a) b => .inr (bin e mkIntDiv a b)
  | Expr.app (Expr.app (Expr.const ``Int.emod _) a) b => .inr (bin e mkIntMod a b)
  | Expr.app (Expr.const ``Int.neg _) a => .inr (un e mkIntNeg a)
  | Expr.app (Expr.const ``Int.ofNat _) (Expr.lit (Literal.natVal n)) => .inl (mkIntLit n)
  -- `Int.negSucc n` denotes `-(n+1)`.
  | Expr.app (Expr.const ``Int.negSucc _) (Expr.lit (Literal.natVal n)) => .inl (mkIntLit (.negSucc n))
  -- `/` and `%` on Nat elaborate to `HDiv.hDiv`/`HMod.hMod`, the raw forms come from the optimizer
  -- or an unfold step
  | Expr.app (Expr.app (Expr.const ``Nat.div _) a) b =>
      .inr (bin e (mkApp2 (mkApp4 (mkConst ``HDiv.hDiv [0, 0, 0]) Nat.mkType Nat.mkType Nat.mkType
        Nat.mkInstHDiv)) a b)
  | Expr.app (Expr.app (Expr.const ``Nat.mod _) a) b =>
      .inr (bin e (mkApp2 (mkApp4 (mkConst ``HMod.hMod [0, 0, 0]) Nat.mkType Nat.mkType Nat.mkType
        Nat.mkInstHMod)) a b)
  -- `++` on String elaborates to `HAppend.hAppend`, the optimizer works on `String.append`
  | Expr.app (Expr.app (Expr.const ``String.append _) a) b =>
      .inr (bin e (mkApp2 (mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) (mkConst ``String)
        (mkConst ``String) (mkConst ``String)
        (mkApp2 (mkConst ``instHAppendOfAppend [0]) (mkConst ``String) (mkConst ``String.instAppend))))
        a b)
  -- an unchanged application is kept, so that the result shares the subterms of `e`
  | Expr.app f a => .inr (bin e e.updateApp! f a)
  | _ => .inl e

/-- Replace optimizer-context FVarIds with goal-context FVarIds in proof steps. -/
def substProofStackFVars (steps : Array Blaster.Optimize.ProofStep)
    (optBinders goalFVarIds : Array FVarId) : Array Blaster.Optimize.ProofStep :=
  if optBinders.isEmpty then steps
  else
    let n := min optBinders.size goalFVarIds.size
    let from_ := (optBinders[:n].toArray).map mkFVar
    let to_ := (goalFVarIds[:n].toArray).map mkFVar
    steps.map fun
      | .rewrite proof symm  => .rewrite (proof.replaceFVars from_ to_) symm
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
        -- read only, so a fresh optimizer environment does
        let e ← withLCtx lctx localInsts do (isSortOrInhabited t).run' default
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
    Among the candidates, `y` matches the first one with its name, else the first one whose type
    is its type, given the previous matches.
    The type covers a renamed binder and an anonymous instance binder, whose name has fresh
    macro scopes in each elaboration.
    `coiEliminated` sees the body before optimization, so an `x` that only a dropped part
    mentions stays a candidate, and a renamed `y` can match it, which leaves a gap. -/
def matchBinders (ys xs : Array Expr) (xElim yElim : Array Bool) :
    MetaM (Option (Array (Option Nat))) := do
  let mut idx := #[]
  let mut next := 0
  for j in [:ys.size] do
    let n ← ys[j]!.fvarId!.getUserName
    let later := (List.range' next (xs.size - next)).filter fun i => yElim[j]! || !xElim[i]!
    let (f, t) := matchedPairs xs (ys.extract 0 j) idx
    let ty := (← inferType ys[j]!).replaceFVars f t
    let byName ← later.findM? fun i => return (← xs[i]!.fvarId!.getUserName) == n
    let found ← match byName with
      | some i => pure (some i)
      | none => later.findM? fun i => do isDefEq (← inferType xs[i]!) ty
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

/-- Memo of `toElabForm` and `hasLet` over one replay, shared by every `canonicalForm` call. -/
private structure CanonCache where
  /-- `toElabForm` of the subterms converted so far. -/
  converted : Std.HashMap Expr Expr := {}
  /-- The subterms known to have no `let`. -/
  noLet : Std.HashSet Expr := {}

/-- Instantiate every `let` and `have` of `e` with its value. -/
private def zetaLets (e : Expr) : MetaM Expr :=
  Core.transform e (pre := fun
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- The one spelling of the replay, so that the user and optimizer spellings of a term agree:
    no `let`, `((n : Nat) : Int)` written `Int.ofNat n`, Nat numerals under `Int.ofNat` raw
    literals, then `toElabForm`. -/
private def canonicalForm (cache : IO.Ref CanonCache) (e : Expr) : MetaM Expr := do
  -- taken out of the ref, so that the maps are updated in place
  let { converted, noLet } ← cache.swap {}
  let (l, noLet) := hasLet e noLet
  let e ← if l then zetaLets e else pure e
  let ofNat (n : Expr) :=
    if n.isAppOfArity ``OfNat.ofNat 3 && (n.getArg! 2).isAppOf ``instOfNatNat then
      mkApp (mkConst ``Int.ofNat) (n.getArg! 1)
    else mkApp (mkConst ``Int.ofNat) n
  let (e, converted) := toElabForm (← Core.transform e (post := fun e => return .done <| match e with
    | .app (.app (.app (.const ``Nat.cast _) _) (.const ``instNatCastInt _)) n => ofNat n
    -- the spelling left by the unfold step of `Nat.cast`
    | .app (.app (.app (.const ``NatCast.natCast _) _) (.const ``instNatCastInt _)) n => ofNat n
    | .app (.const ``Int.ofNat _) n => ofNat n
    | _ => e)) converted
  cache.set { converted, noLet }
  return e

/-- Beta reduce the redexes headed by the term the rewrite `r` inserted, since the optimizer
    keeps applied lambdas reduced. Reducing one also reduces the redexes that substituting a
    lambda argument creates. -/
private def betaAfterLambdaStep (r : RewriteResult) : MetaM Expr := do
  -- the rewrite proof is `congrArg α β lhs rhs motive heq`, and `rhs` is the inserted term
  let_expr congrArg _ _ _ rhs _ _ := r.eqProof | return r.eNew
  let rhs ← instantiateMVars rhs
  unless rhs.isLambda do return r.eNew
  -- `eNew` was built before the rewrite assigned the instance arguments
  let eNew ← instantiateMVars r.eNew
  -- a user redex is reduced only when its head is the inserted term itself
  Core.transform eNew (post := fun x =>
    return if x.getAppFn == rhs then .done (betaCreated rhs x.getAppArgs) else .continue)
where
  /-- `f args` reduced at the head while it stays a redex, with the redexes that substituting a
      lambda argument creates reduced one level deep. -/
  betaCreated (f : Expr) (args : Array Expr) : Expr := Id.run do
    let mut f := f
    let mut args := args
    while f.isLambda && !args.isEmpty do
      let mut b := f
      let mut k := 0
      while k < args.size do
        let .lam _ _ body _ := b | break
        b := body
        k := k + 1
      f := b.instantiateBetaRevRange 0 k args
      args := args.extract k args.size
    return mkAppN f args

/-- Kernel check a step proof with free variables, since a hypothesis left out of normal form
    by the replay makes a proof built on it ill-typed. A leftover metavariable also fails. -/
private def checkHypStep (g : MVarId) (proof : Expr) : MetaM Unit := do
  unless proof.hasFVar do return
  g.withContext do
    if let .error _ := Kernel.check (← getEnv) (← getLCtx) (← instantiateMVars proof) then
      throwError "ill-typed proof step"

/-- How the replay left one intro'd binder. Its terms are in the context of the replayed goal. -/
structure ReplayedBinder where
  /-- The fvar of the binder when the replay reached it, and its type then. -/
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
    optimizer normal form that hypothesis-driven steps expect.
    Returns the new goal, the steps with the replaced hypothesis fvars renamed, and how each
    binder was left. -/
private def rewriteHypotheses (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId) (cache : IO.Ref CanonCache) :
    MetaM (MVarId × Array Blaster.Optimize.ProofStep × Array ReplayedBinder) := do
  let mut g := goal
  let mut steps := steps
  let mut hs := hyps
  let mut binders := #[]
  for i in [:hs.size] do
    let mut h := hs[i]!
    let mut ty ← g.withContext do instantiateMVars (← h.getType)
    let start := (h, ty)
    -- a replacement only renames the binder and the later ones, so this one keeps its record
    let mut eq? : Option Expr := none
    unless ← g.withContext (isProp ty) do
      binders := binders.push { fvar := h, type := ty, final := h, finalType := ty, eq? }
      continue
    -- bounded fixed point, so a pair of steps undoing each other cannot loop
    let mut fuel := steps.size + 1
    let mut changed := true
    while changed && fuel > 0 do
      fuel := fuel - 1
      changed := false
      -- index into the current `steps`, whose proofs are renamed after each replacement
      for j in [:steps.size] do
        -- as on the target, so that a hypothesis and the target unfold alike
        if let some (.unfold n) := steps[j]? then
          let ty' ← deltaExpand ty (· == n)
          if ty' != ty then
            let ty' ← g.withContext (canonicalForm cache ty')
            -- definitional, so the hypothesis keeps its fvar
            g ← g.replaceLocalDeclDefEq h ty'
            ty := ty'
            changed := true
        if let some (.rewrite heq symm) := steps[j]? then
          -- a step built from this hypothesis or a later one cannot have normalized it
          if heq.hasAnyFVar (hs.extract i hs.size).contains then continue
          try
            let r ← g.rewrite ty heq symm
            checkHypStep g heq
            let eNew ← betaAfterLambdaStep r
            let res ← g.replaceLocalDecl h eNew r.eqProof
            -- `eqProof` proves `ty = r.eNew`, and `eNew` is its beta reduct
            eq? := some <| match eq? with
              | none => r.eqProof
              | some e => mkApp6 (mkConst ``Eq.trans [1]) (mkSort 0) start.2 ty eNew e r.eqProof
            -- the replaced hypothesis and every later local got fresh fvars
            let s := res.subst.insert h (mkFVar res.fvarId)
            steps := steps.map fun
              | .rewrite proof symm => .rewrite (s.apply proof) symm
              | .exact proof => .exact (s.apply proof)
              | s@(.unfold _) => s
            hs := hs.map fun f => (s.get f).fvarId!
            g := res.mvarId
            h := res.fvarId
            ty := eNew
            changed := true
          catch _ => pure ()
    binders := binders.push { fvar := start.1, type := start.2, final := h, finalType := ty, eq? }
  return (g, steps, binders)

/-- Rewrite the hypotheses, then apply the steps to the target until none applies.
    Steps that don't match are skipped. -/
private def replaySteps (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId) (cache : IO.Ref CanonCache) : MetaM (MVarId × Array ReplayedBinder) := do
  let (goal, steps, binders) ← rewriteHypotheses goal steps hyps cache
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
  let mut changed := true
  while changed do
    changed := false
    for step in steps do
      match step with
      | .rewrite heq symm =>
        try
          let t ← g.getType
          let r ← g.rewrite t heq symm
          checkHypStep g heq
          g ← g.replaceTargetEq (← betaAfterLambdaStep r) r.eqProof
          -- a rewrite between defeq spellings may leave the target as is and must not loop
          if (← g.getType) != t then changed := true
          /- trace[Optimize.expr] "  applied rewrite → {← g.getType}" -/
        catch _ => pure ()
      | .exact proof =>
        let s ← saveState
        try
          -- both sides are in the replay spelling, so a recursive target is not unfolded
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
    Returns the goal left and how the replay left each of `hyps`. -/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId := #[]) : MetaM (MVarId × Array ReplayedBinder) := do
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
  let steps : Array Blaster.Optimize.ProofStep ← goal.withContext <| steps.mapM fun
    | .rewrite proof symm => return .rewrite (← canonicalForm cache proof) symm
    | .exact proof => return .exact (← canonicalForm cache proof)
    | s => return s
  replaySteps goal steps hyps cache

/-- Custom sorry for Blaster to differentiate between SMT-verified goals and regular `sorry`.-/
axiom blasterProven : ∀ {α : Sort u}, α

private def blasterAdmit (mvarId : MVarId) : MetaM Unit :=
  mvarId.withContext do
    mvarId.checkNotAssigned `blasterAdmit
    let mvarType ← mvarId.getType >>= instantiateMVars
    let u ← getLevel mvarType
    mvarId.assign (mkApp (mkConst ``blasterProven [u]) mvarType)

/-- Prove a goal by introducing binders, applying the proof stack, then closing with refl.
    On failure, admit via `blasterProven`, or throw when `admit` is false.
    Warn only when `optimizerClosed`, since then the optimizer proved it by rewriting and
    it should have reconstructed. -/
private def proveByProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) (optimizerClosed : Bool) (admit := true) :
    MetaM (Expr × Array ReplayedBinder) := do
  let proofMVar ← mkFreshExprMVar goalType
  let numBinders ← forallTelescope goalType fun fvars _ => pure fvars.size
  let (goalFVarIds, g) ← proofMVar.mvarId!.introNP numBinders
  let proofStack := substProofStackFVars proofStack optBinders goalFVarIds
  let (g, binders) ← applyProofStack g proofStack goalFVarIds
  let closed ← closeTrivially g
  unless closed do
    unless admit do throwError m!"blaster: reconstruction gap\n{.ofGoal g}"
    if optimizerClosed then
      logWarning m!"blaster: reconstruction gap ({proofStack.size} steps), admitted via `blasterProven`\n{.ofGoal g}"
    blasterAdmit g
  -- a step may carry an optimizer fvar the replay did not map, which the kernel would reject
  let pf ← instantiateMVars proofMVar
  let lctx ← getLCtx
  unless pf.hasFVar && (collectFVars {} pf).fvarIds.any (!lctx.contains ·) do
    return (proofMVar, binders)
  unless admit do throwError "blaster: reconstruction gap (unmapped free variable)"
  if optimizerClosed && closed then
    logWarning m!"blaster: reconstruction gap (unmapped free variable), admitted via `blasterProven`"
  let m ← mkFreshExprMVar goalType
  blasterAdmit m.mvarId!
  return (m, binders)

/-- The instance arguments of the proofs of `steps`, in the optimizer context.
    They carry the instances the optimizer built, e.g. the `Nonempty` of an eliminated binder. -/
private def stepInstances (steps : Array Blaster.Optimize.ProofStep) : MetaM (Array Expr) := do
  let mut insts := #[]
  for s in steps do
    let p ← match s with
      | .rewrite p _ | .exact p => pure p
      | .unfold _ => continue
    let .const c _ := p.getAppFn | continue
    let mut ty := (← getConstInfo c).type
    for a in p.getAppArgs do
      let .forallE _ _ b bi := ty | break
      if bi.isInstImplicit then insts := insts.push a
      ty := b
  return insts

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

/-- Prove `(∀ xs, P) = (∀ ys, Q)`, with `k` binders of `rhs` opened and matched by
    `matchBinders`, from a single replay of `∀ xs, P = Q`, when `forallEqTransports` holds.
    The replay rewrites the hypotheses, so its record of each binder gives
    - for a kept hypothesis whose type changes, the equation that casts it,
    - for an eliminated hypothesis, the type it was rewritten to, closed when trivial.
    An eliminated binder that is not a proof, on either side, gets an `inhabitant`, with the
    instances the steps carry. Without one, the goal is left as a gap. -/
private def proveForallEq (lhs rhs : Expr) (k : Nat) (idx : Array (Option Nat))
    (steps : Array Blaster.Optimize.ProofStep) (optBinders : Array FVarId) : MetaM Expr := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  forallTelescope lhs fun xs P => Meta.forallBoundedTelescope rhs (some k) fun ys Q => do
    let (f, t) := matchedPairs xs ys idx
    let toX (e : Expr) := e.replaceFVars f t
    let innerType ← mkForallFVars xs (← mkEq P (toX Q))
    -- out of the telescopes, or the replay could close it with one of their fvars
    let (inner, bs) ← withLCtx lctx localInsts do
      proveByProofStack innerType steps optBinders false (admit := false)
    -- the equations are only needed here, so their lemma arguments are instantiated here
    let bs ← bs.mapM fun b => return { b with eq? := ← b.eq?.mapM instantiateMVars }
    let rhsOf (i : Nat) := idx.findIdx? (· == some i)
    let insts ← stepInstances steps
    -- the steps' instances given the first lhs arguments `args`, those the context holds
    let instsAt (args : Array Expr) : MetaM (Array Expr) := do
      let n := min args.size optBinders.size
      let opt := (optBinders.extract 0 n).map mkFVar
      let lctx ← getLCtx
      return (insts.map (·.replaceFVars opt (args.extract 0 n))).filter fun a =>
        !a.hasAnyFVar (!lctx.contains ·)
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

/-- Prove `goalType`, a goal the optimizer found valid, from its proof stack.
    An equation of foralls whose binders `matchBinders` matches and `forallEqTransports`
    accepts is proved by `proveForallEq`. Any other goal is proved by the replay on the whole
    goal, whose rewrites reach no bound variable, e.g. those of closed subterms, and whose
    `refl` closes sides equal up to binder names. A gap reports the goal of the path taken.
    Also run by the `#testOptimize` gate, with `admit := false`. -/
def proveGoalByProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) (optimizerClosed : Bool) (admit := true) : MetaM Expr := do
  -- the optimizer sees the goal without its `let`s, so its binders are found below them
  let goalType ← if (hasLet goalType {}).1 then zetaLets goalType else pure goalType
  -- the number of `rhs` binders to open, when the goal is an equation of foralls they match
  let forallEq? : MetaM (Option (Expr × Expr × Nat × Array (Option Nat))) := do
    let some (_, lhs, rhs) := goalType.eq? | return none
    unless ← isProp lhs do return none
    let numBinders ← forallTelescope lhs fun fvars _ => pure fvars.size
    if numBinders == 0 || rhs.isConstOf ``True then return none
    -- opening more binders than rhs shows can unfold its body (e.g. `¬ a`),
    -- so only its syntactic binders are opened when they hold as many proofs as lhs
    let kSyn := min numBinders rhs.getNumHeadForalls
    let k ← if kSyn == numBinders then pure numBinders else
      forallTelescope lhs fun xs _ =>
        forallBoundedTelescope rhs (some numBinders) fun ys _ => do
          let numProofs (xs : Array Expr) := return (← xs.filterM (isProof ·)).size
          let same := (← numProofs (ys.extract 0 kSyn)) == (← numProofs xs)
          return if ys.size != kSyn && same then kSyn else numBinders
    -- the other equations go to the replay on the whole goal, e.g. a binder type with a
    -- rewritten closed subterm
    let some idx ← forallTelescope lhs fun xs P =>
        forallBoundedTelescope rhs (some k) fun ys Q => do
          let some idx ← matchBinders ys xs (← coiEliminated xs P ys) (← coiEliminated ys Q xs)
            | return none
          return if ← forallEqTransports xs ys Q idx then some idx else none
      | return none
    return some (lhs, rhs, k, idx)
  match goalType.eq? with
  | some (_, lhs, rhs) =>
    -- `P = True`: prove P directly, then lift via eq_true
    if rhs.isConstOf ``True && (← isProp lhs) then
      let (pf, _) ← proveByProofStack lhs proofStack optBinders optimizerClosed admit
      return ← mkAppM ``eq_true #[pf]
  | none => pure ()
  if let some (lhs, rhs, k, idx) ← forallEq? then
    let s ← saveState
    try
      return ← proveForallEq lhs rhs k idx proofStack optBinders
    catch e =>
      s.restore
      unless admit do throw e
      if optimizerClosed then
        logWarning m!"blaster: reconstruction gap, admitted via `blasterProven`\n{e.toMessageData}"
      let m ← mkFreshExprMVar goalType
      blasterAdmit m.mvarId!
      return m
  return (← proveByProofStack goalType proofStack optBinders optimizerClosed admit).1

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
   let proofStack := finalEnv.optEnv.proofStack
   let optBinders := finalEnv.optEnv.optBinders
   match result with
   | .Valid =>
        -- `optExpr == True` ⟹ proved by rewriting (no SMT)
        let optimizerClosed := optExpr.isConstOf ``True
        goal.assign (← proveGoalByProofStack (← goal.getType) proofStack optBinders optimizerClosed)
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
