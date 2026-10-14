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

/-- Convert core Nat/Int operators to their HAdd/HSub/HMul/Neg elaborated form
    so that proof term LHS patterns structurally match goal expressions.
    `Int.ediv`/`Int.emod` are converted only when `divMod` holds. -/
def toElabForm (e : Expr) (divMod : Bool := true) : MetaM Expr :=
  go e
where
  go (e : Expr) : MetaM Expr := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) a) b =>
      mkAdd (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) a) b =>
      mkSub (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) a) b =>
      mkMul (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Int.add _) a) b =>
      mkAdd (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Int.sub _) a) b =>
      mkSub (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Int.mul _) a) b =>
      mkMul (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Int.ediv _) a) b =>
      if divMod then mkAppM ``HDiv.hDiv #[← go a, ← go b]
      else return mkApp2 (mkConst ``Int.ediv) (← go a) (← go b)
  | Expr.app (Expr.app (Expr.const ``Int.emod _) a) b =>
      if divMod then mkAppM ``HMod.hMod #[← go a, ← go b]
      else return mkApp2 (mkConst ``Int.emod) (← go a) (← go b)
  | Expr.app (Expr.const ``Int.neg _) a =>
      mkAppM ``Neg.neg #[← go a]
  | Expr.app (Expr.const ``Int.ofNat _) (a@(Expr.lit (Literal.natVal _))) =>
      mkAppOptM ``OfNat.ofNat #[mkConst ``Int, a, none]
  | Expr.app (Expr.const ``Int.negSucc _) (Expr.lit (Literal.natVal n)) =>
      -- `Int.negSucc n` denotes `-(n+1)`.
      mkAppM ``Neg.neg #[← mkAppOptM ``OfNat.ofNat #[mkConst ``Int, mkNatLit (n + 1), none]]
  -- Future-proofing: Nat.div /Nat.mod currently elaborates directly
  --                  (not via HDiv.hDiv / HMod.hMod),
  -- but we normalize it here in case that changes, consistent with add/sub/mul.
  | Expr.app (Expr.app (Expr.const ``Nat.div _) a) b =>
      mkAppM ``HDiv.hDiv #[← go a, ← go b]
  | Expr.app (Expr.app (Expr.const ``Nat.mod _) a) b =>
      mkAppM ``HMod.hMod #[← go a, ← go b]
  | Expr.app f a =>
      return mkApp (← go f) (← go a)
  | _ => return e

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

/-- `true` iff `e` contains a `let` binding anywhere. -/
private partial def hasLet : Expr → Bool
  | .letE .. => true
  | .app f a => hasLet f || hasLet a
  | .lam _ t b _ => hasLet t || hasLet b
  | .forallE _ t b _ => hasLet t || hasLet b
  | .mdata _ e => hasLet e
  | .proj _ _ s => hasLet s
  | _ => false

/-- Notation abbreviations the optimizer unfolds without a proof step.
    Unfolded in hypotheses so that rewrite steps can match underneath them. -/
private def isSilentAbbrev (n : Name) : Bool :=
  n == ``Ne || n == ``GE.ge || n == ``GT.gt

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
    (hyps : Array FVarId) : MetaM (MVarId × Array Blaster.Optimize.ProofStep) := do
  let mut g := goal
  let mut steps := steps
  let mut hs := hyps
  for i in [:hs.size] do
    let mut h := hs[i]!
    let mut ty ← g.withContext do instantiateMVars (← h.getType)
    unless ← g.withContext (isProp ty) do continue
    ty ← deltaExpand ty isSilentAbbrev
    -- bounded fixed point, so a pair of steps undoing each other cannot loop
    let mut fuel := steps.size + 1
    let mut changed := true
    while changed && fuel > 0 do
      fuel := fuel - 1
      changed := false
      -- index into the current `steps`, whose proofs are renamed after each replacement
      for j in [:steps.size] do
        if let some (.rewrite heq symm) := steps[j]? then
          -- a step built from this hypothesis or a later one cannot have normalized it
          if heq.hasAnyFVar (hs.extract i hs.size).contains then continue
          try
            -- the rewrite runs on the delta expanded type, which is defeq to the declared one
            let r ← g.rewrite ty heq symm
            let eNew ← betaAfterLambdaStep heq symm r.eNew
            let res ← g.replaceLocalDecl h eNew r.eqProof
            -- the replaced hypothesis and every later local got fresh fvars
            let s := res.subst.insert h (mkFVar res.fvarId)
            steps := steps.map fun
              | .rewrite proof symm => .rewrite (s.apply proof) symm
              | .exact proof => .exact (s.apply proof)
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
    (hyps : Array FVarId) : MetaM MVarId := do
  let (goal, steps) ← rewriteHypotheses goal steps hyps
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
          let r ← g.rewrite (← g.getType) heq symm
          g ← g.replaceTargetEq (← betaAfterLambdaStep heq symm r.eNew) r.eqProof
          changed := true
          /- trace[Optimize.expr] "  applied rewrite → {← g.getType}" -/
        catch _ => pure ()
      | .exact proof =>
        try
          if ← isDefEq (← inferType proof) (← g.getType) then
            g.assign proof
            /- trace[Optimize.expr] "  applied exact, goal closed" -/
            return g
        catch _ => pure ()
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

/-- Run `x` within a small budget of `1000 * 1000` raw heartbeats, as `maxHeartbeats 1000` would.
    Any exception except an interrupt, timeout included, counts as `false`. -/
private def withSmallBudget (x : MetaM Bool) : MetaM Bool := do
  let s ← saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context ({ · with maxHeartbeats := 1000 * 1000 }) (withCurrHeartbeats x))
    fun _ => do s.restore; return false

/-- Apply recorded proof stack rewrites to a goal.
    `hyps` are the intro'd binders, rewritten first (see `rewriteHypotheses`).
    With `unfoldTarget` and a target containing `Ne` or `GT.gt`, a replay that does not close
    the original target is retried on the unfolded one. Then the goal may be returned closed
    by `True.intro` or `refl`. With `tryUnreplayed`, a goal the replay leaves open is also tried
    on the original target without any step. -/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep)
    (hyps : Array FVarId := #[]) (unfoldTarget := true) (tryUnreplayed := true) : MetaM MVarId := do
  let goal ← goal.withContext do
    let t ← goal.getType
    if hasLet t then goal.change (← zetaReduce t) else pure goal
  -- normalize proof terms once upfront
  -- a step whose normalization fails is kept as is and skipped
  let steps : Array Blaster.Optimize.ProofStep ← goal.withContext <| steps.flatMapM fun
    | s@(.rewrite proof symm) => do
      try
        let p ← toElabForm proof
        -- a goal written with core `Int.ediv`/`Int.emod` only matches the unconverted form
        if (proof.find? fun e => e.isAppOfArity ``Int.ediv 2 || e.isAppOfArity ``Int.emod 2).isSome then
          let alt ← toElabForm proof (divMod := false)
          if alt != p then return #[.rewrite p symm, .rewrite alt symm]
        return #[.rewrite p symm]
      catch _ => return #[s]
    | s => return #[s]
  -- `GE.ge` is left out since the `ge_eq_le` step matches it
  let isGoalAbbrev (n : Name) := n == ``Ne || n == ``GT.gt
  let s ← saveState
  -- a goal left open by the replay is tried without any step within a small budget,
  -- e.g. when a rewritten `ite` no longer reduces by defeq
  let orUnreplayed (g : MVarId) : MetaM MVarId := do
    unless tryUnreplayed do return g
    let failed ← saveState
    s.restore
    if ← withSmallBudget (closeTrivially goal <||> (do goal.assumption; pure true)) then return goal
    failed.restore
    return g
  unless unfoldTarget &&
      ((← goal.getType).find? fun e => e.isConst && isGoalAbbrev e.constName!).isSome do
    let g ← replaySteps goal steps hyps
    unless tryUnreplayed do return g
    if ← withSmallBudget (closeTrivially g) then return g
    return ← orUnreplayed g
  -- the original target is replayed first, so a goal that closes this way costs no more
  let g ← replaySteps goal steps hyps
  if ← closeTrivially g then return g
  -- otherwise retry with `Ne` and `GT.gt` unfolded, as the optimizer sees them
  let failed ← saveState
  s.restore
  let g' ← replaySteps (← goal.deltaTarget isGoalAbbrev) steps hyps
  if ← closeTrivially g' then return g'
  -- both failed, keep the original target for the gap message
  failed.restore
  orUnreplayed g

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
  -- SMT-proved goals skip the unfolded pass
  let g ← applyProofStack g proofStack goalFVarIds (unfoldTarget := optimizerClosed)
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
