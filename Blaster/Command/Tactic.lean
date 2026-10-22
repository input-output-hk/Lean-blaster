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

/-- Convert core Nat/Int operators and the raw Int literals `Int.ofNat n`, `Int.negSucc n` to their
    elaborated form, `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv`, `HMod.hMod`, `Neg.neg`
    and `OfNat.ofNat`,
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

/-- Map optimized body fvars to input fvars when binder counts differ.
    Uses binder names to find the correct correspondence, since the
    optimizer preserves binder names for surviving forall binders. -/
def mapOptBodyToInputFVars (optBody : Expr) (optFvars inputFvars : Array Expr) : MetaM Expr := do
  let mut mapping : Array Expr := #[]
  for i in [:optFvars.size] do
    let optName ← optFvars[i]!.fvarId!.getUserName
    let mut found := false
    for inputFvar in inputFvars do
      if (← inputFvar.fvarId!.getUserName) == optName then
        mapping := mapping.push inputFvar
        found := true
        break
    unless found do
      mapping := mapping.push optFvars[i]!
  return optBody.replaceFVars optFvars mapping

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

/-- The one spelling of the replay, the `toElabForm` one without the `let`s the optimizer
    does not see. -/
private def canonicalForm (cache : IO.Ref CanonCache) (e : Expr) : MetaM Expr := do
  -- taken out of the ref, so that the maps are updated in place
  let { converted, noLet } ← cache.swap {}
  let (l, noLet) := hasLet e noLet
  let (e, converted) := toElabForm (← if l then zetaReduce e else pure e) converted
  cache.set { converted, noLet }
  return e

/-- Beta reduce `e` after a rewrite by a constant step whose replacement side is a lambda,
    since applied occurrences of the rewritten term become redexes. -/
private def betaAfterLambdaStep (heq : Expr) (symm : Bool) (e : Expr) : MetaM Expr := do
  let .const n _ := heq | return e
  let some ci := (← getEnv).find? n | return e
  let some (_, lhs, rhs) := ci.type.getForallBody.eq? | return e
  if (if symm then lhs else rhs).isLambda then Core.betaReduce e else return e

/-- Rewrite the intro'd Prop hypotheses with the recorded steps, so they reach the
    optimizer normal form that hypothesis-driven steps expect.
    Returns the new goal and the steps with the replaced hypothesis fvars renamed. -/
private def rewriteHypotheses (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId) (cache : IO.Ref CanonCache) :
    MetaM (MVarId × Array Blaster.Optimize.ProofStep) := do
  let mut g := goal
  let mut steps := steps
  let mut hs := hyps
  for i in [:hs.size] do
    let mut h := hs[i]!
    let mut ty ← g.withContext do instantiateMVars (← h.getType)
    unless ← g.withContext (isProp ty) do continue
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
            let eNew ← betaAfterLambdaStep heq symm r.eNew
            let res ← g.replaceLocalDecl h eNew r.eqProof
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
  return (g, steps)

/-- Rewrite the hypotheses, then apply the steps to the target until none applies.
    Steps that don't match are skipped. -/
private def replaySteps (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId) (cache : IO.Ref CanonCache) : MetaM MVarId := do
  let (goal, steps) ← rewriteHypotheses goal steps hyps cache
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
          g ← g.replaceTargetEq (← betaAfterLambdaStep heq symm r.eNew) r.eqProof
          -- a rewrite between defeq spellings may leave the target as is and must not loop
          if (← g.getType) != t then changed := true
          /- trace[Optimize.expr] "  applied rewrite → {← g.getType}" -/
        catch _ => pure ()
      | .exact proof =>
        try
          if ← isDefEq (← inferType proof) (← g.getType) then
            g.assign proof
            /- trace[Optimize.expr] "  applied exact, goal closed" -/
            return g
        catch _ => pure ()
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
  return g

/-- `true` iff `g` is assigned, `True` (then closed) or closed by `refl`. -/
private def closeTrivially (g : MVarId) : MetaM Bool := do
  if ← g.isAssigned then return true
  if (← instantiateMVars (← g.getType)).isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return true
  try g.refl; return true catch _ => return false

/-- Apply recorded proof stack rewrites to a goal.
    `hyps` are the intro'd binders, rewritten first (see `rewriteHypotheses`). -/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId := #[]) : MetaM MVarId := do
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

/-- Build a proof of `(∀ x₁…xₙ, P) = (∀ y₁…yₘ, Q)` when m < n (some binders eliminated),
    given `innerProof : ∀ x₁…xₙ, P(x₁…xₙ) = Q(kept(x₁…xₙ))`. -/
private def liftForallEq (lhs rhs innerProof : Expr) : MetaM Expr := do
  let rhsNames := getForallBinderNames rhs
  -- Forward: lhs → rhs
  let forward ← withLocalDecl `h .default lhs fun h =>
    forallTelescope lhs fun lhsFvars _ => do
      let mut lhsArgs : Array Expr := #[]
      let mut keptFvars : Array Expr := #[]
      let mut rhsIdx := 0
      for fvar in lhsFvars do
        let name ← fvar.fvarId!.getUserName
        if rhsIdx < rhsNames.size && rhsNames[rhsIdx]! == name then
          lhsArgs := lhsArgs.push fvar
          keptFvars := keptFvars.push fvar
          rhsIdx := rhsIdx + 1
        else
          -- the type may mention binders already replaced by a default
          let ty := (← inferType fvar).replaceFVars (lhsFvars.extract 0 lhsArgs.size) lhsArgs
          -- `Decidable p` has no `Inhabited` instance, any decision procedure fits
          if ty.isAppOfArity ``Decidable 1 then
            lhsArgs := lhsArgs.push (mkApp (mkConst ``Classical.propDecidable) ty.appArg!)
            continue
          let u ← getLevel ty
          let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) ty)
          lhsArgs := lhsArgs.push (mkApp2 (mkConst ``Inhabited.default [u]) ty inst)
      let eqProof := mkAppN innerProof lhsArgs
      let hApp := mkAppN h lhsArgs
      let castExpr ← mkAppM ``cast #[eqProof, hApp]
      let body ← mkLambdaFVars keptFvars castExpr
      mkLambdaFVars #[h] body
  -- Backward: rhs → lhs
  let backward ← withLocalDecl `h .default rhs fun h =>
    forallTelescope lhs fun lhsFvars _ => do
      let mut rhsArgs : Array Expr := #[]
      for fvar in lhsFvars do
        let name ← fvar.fvarId!.getUserName
        if rhsNames.contains name then
          rhsArgs := rhsArgs.push fvar
      let hApp := mkAppN h rhsArgs
      let eqProof := mkAppN innerProof lhsFvars
      let symmEq ← mkAppM ``Eq.symm #[eqProof]
      let castExpr ← mkAppM ``cast #[symmEq, hApp]
      let body ← mkLambdaFVars lhsFvars castExpr
      mkLambdaFVars #[h] body
  let iff ← mkAppM ``Iff.intro #[forward, backward]
  mkAppM ``propext #[iff]

 where
   /-- Extract binder names from a chain of forall quantifiers. -/
   getForallBinderNames : Expr → Array Name
     | Expr.forallE n _ body _ => #[n] ++ getForallBinderNames body
     | _ => #[]

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
    (optBinders : Array FVarId) (optimizerClosed : Bool) (admit := true) : MetaM Expr := do
  let proofMVar ← mkFreshExprMVar goalType
  let numBinders ← forallTelescope goalType fun fvars _ => pure fvars.size
  let (goalFVarIds, g) ← proofMVar.mvarId!.introNP numBinders
  let proofStack := substProofStackFVars proofStack optBinders goalFVarIds
  let g ← applyProofStack g proofStack goalFVarIds
  let closed ← closeTrivially g
  unless closed do
    unless admit do throwError "blaster: reconstruction gap"
    if optimizerClosed then
      logWarning m!"blaster: reconstruction gap ({proofStack.size} steps), admitted via `blasterProven`\n{.ofGoal g}"
    blasterAdmit g
  -- a step may carry an optimizer fvar the replay did not map, which the kernel would reject
  let pf ← instantiateMVars proofMVar
  let lctx ← getLCtx
  unless pf.hasFVar && (collectFVars {} pf).fvarIds.any (!lctx.contains ·) do return proofMVar
  unless admit do throwError "blaster: reconstruction gap"
  if optimizerClosed && closed then
    logWarning m!"blaster: reconstruction gap (unmapped free variable), admitted via `blasterProven`"
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
   let proofStack := finalEnv.optEnv.proofStack
   let optBinders := finalEnv.optEnv.optBinders
   match result with
   | .Valid =>
        let goalType ← goal.getType
        -- `optExpr == True` ⟹ proved by rewriting (no SMT)
        let optimizerClosed := optExpr.isConstOf ``True
        -- Try propositional equality path: (∀ xs, body₁) = (∀ xs, body₂)
        let usedPropEqPath ← try
          match goalType.eq? with
          | some (_, lhs, rhs) =>
            if rhs.isConstOf ``True && (← isProp lhs) then
              -- Goal is `P = True`: prove P directly, then lift via eq_true
              let proof ← proveByProofStack lhs proofStack optBinders optimizerClosed
              goal.assign (← mkAppM ``eq_true #[proof])
              pure true
            else if ← isProp lhs then
              let numBinders ← forallTelescope lhs fun fvars _ => pure fvars.size
              if numBinders > 0 then
                -- Build pointwise equality goal: ∀ xs, body₁(xs) = body₂(xs), opening `k` rhs binders
                let provePointwise (k : Nat) (admit : Bool) : MetaM Unit := do
                  let innerGoalType ← forallTelescope lhs fun inputFvars inputBody => do
                    let optBody ←
                      forallBoundedTelescope rhs (some k) fun optFvars optBody =>
                        mapOptBodyToInputFVars optBody optFvars inputFvars
                    let eq ← mkEq inputBody optBody
                    mkForallFVars inputFvars eq
                  let innerProof ←
                    proveByProofStack innerGoalType proofStack optBinders optimizerClosed admit
                  -- Lift: (∀ xs, body₁ = body₂) → (∀ xs, body₁) = (∀ xs, body₂)
                  let liftedProof ← liftForallEq lhs rhs innerProof
                  goal.assign liftedProof
                -- opening more binders than rhs shows can unfold its body (e.g. `¬ a`),
                -- so its syntactic binders are tried first when they hold as many proofs as lhs
                let kSyn := min numBinders rhs.getNumHeadForalls
                -- `try` in TacticM restores the state on failure
                let syntacticOk ← if kSyn < numBinders then
                    try
                      let trySyn ← forallTelescope lhs fun inputFvars _ =>
                        forallBoundedTelescope rhs (some numBinders) fun optFvars _ => do
                          -- nothing unfolded, both alignments give the same goal
                          if optFvars.size == kSyn then return false
                          let numProofs (xs : Array Expr) := return (← xs.filterM (isProof ·)).size
                          return (← numProofs (optFvars.extract 0 kSyn)) == (← numProofs inputFvars)
                      if trySyn then provePointwise kSyn false
                      pure trySyn
                    catch _ => pure false
                  else pure false
                unless syntacticOk do provePointwise numBinders true
                pure true
              else pure false
            else pure false
          | none => pure false
        catch _ =>
          /- trace[Optimize.expr] "propEqPath failed: {e.toMessageData}" -/
          pure false
        unless usedPropEqPath do
          let proof ← proveByProofStack goalType proofStack optBinders optimizerClosed
          goal.assign proof
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
