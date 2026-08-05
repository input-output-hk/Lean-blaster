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
    so that proof term LHS patterns structurally match goal expressions. -/
def toElabForm (e : Expr) : MetaM Expr := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Nat.add _) a) b =>
      mkAdd (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Nat.sub _) a) b =>
      mkSub (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Nat.mul _) a) b =>
      mkMul (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Int.add _) a) b =>
      mkAdd (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Int.sub _) a) b =>
      mkSub (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.app (Expr.const ``Int.mul _) a) b =>
      mkMul (← toElabForm a) (← toElabForm b)
  | Expr.app (Expr.const ``Int.neg _) a =>
      mkAppM ``Neg.neg #[← toElabForm a]
  | Expr.app (Expr.const ``Int.ofNat _) (a@(Expr.lit (Literal.natVal _))) =>
      mkAppOptM ``OfNat.ofNat #[mkConst ``Int, a, none]
  -- Future-proofing: Nat.div /Nat.mod currently elaborates directly
  --                  (not via HDiv.hDiv / HMod.hMod),
  -- but we normalize it here in case that changes, consistent with add/sub/mul.
  | Expr.app (Expr.app (Expr.const ``Nat.div _) a) b =>
      mkAppM ``HDiv.hDiv #[← toElabForm a, ← toElabForm b]
  | Expr.app (Expr.app (Expr.const ``Nat.mod _) a) b =>
      mkAppM ``HMod.hMod #[← toElabForm a, ← toElabForm b]
  | Expr.app f a =>
      return mkApp (← toElabForm f) (← toElabForm a)
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

/-- Apply recorded proof stack rewrites to a goal.
    Each rewrite step is attempted; steps that don't match are skipped. -/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep) : MetaM MVarId := do
  -- normalize proof terms once upfront
  let steps : Array Blaster.Optimize.ProofStep ← goal.withContext <| steps.mapM fun
    | .rewrite proof symm => return .rewrite (← toElabForm proof) symm
    | .exact proof => return .exact proof
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
          g ← g.replaceTargetEq r.eNew r.eqProof
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
  return g

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
          let ty ← inferType fvar
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

/-- Prove a goal by introducing binders, applying the proof stack, then closing with refl.
    Returns the proof term so callers can use it directly. -/
private def proveByProofStack (goalType : Expr) (proofStack : Array Blaster.Optimize.ProofStep)
    (optBinders : Array FVarId) : MetaM Expr := do
  let proofMVar ← mkFreshExprMVar goalType
  let numBinders ← forallTelescope goalType fun fvars _ => pure fvars.size
  let (goalFVarIds, g) ← proofMVar.mvarId!.introNP numBinders
  let proofStack := substProofStackFVars proofStack optBinders goalFVarIds
  let g ← applyProofStack g proofStack
  unless ← g.isAssigned do
    try g.refl
    catch _ => g.admit
  return proofMVar

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
        -- Try propositional equality path: (∀ xs, body₁) = (∀ xs, body₂)
        let usedPropEqPath ← try
          match goalType.eq? with
          | some (_, lhs, rhs) =>
            if rhs.isConstOf ``True && (← isProp lhs) then
              -- Goal is `P = True`: prove P directly, then lift via eq_true
              let proof ← proveByProofStack lhs proofStack optBinders
              goal.assign (← mkAppM ``eq_true #[proof])
              pure true
            else if ← isProp lhs then
              let numBinders ← forallTelescope lhs fun fvars _ => pure fvars.size
              if numBinders > 0 then
                -- Build pointwise equality goal: ∀ xs, body₁(xs) = body₂(xs)
                let innerGoalType ← forallTelescope lhs fun inputFvars inputBody => do
                  let optBody ← forallTelescope rhs fun optFvars optBody =>
                    mapOptBodyToInputFVars optBody optFvars inputFvars
                  let eq ← mkEq inputBody optBody
                  mkForallFVars inputFvars eq
                let innerProof ← proveByProofStack innerGoalType proofStack optBinders
                -- Lift: (∀ xs, body₁ = body₂) → (∀ xs, body₁) = (∀ xs, body₂)
                let liftedProof ← liftForallEq lhs rhs innerProof
                goal.assign liftedProof
                pure true
              else pure false
            else pure false
          | none => pure false
        catch _ =>
          /- trace[Optimize.expr] "propEqPath failed: {e.toMessageData}" -/
          pure false
        unless usedPropEqPath do
          let proof ← proveByProofStack goalType proofStack optBinders
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
