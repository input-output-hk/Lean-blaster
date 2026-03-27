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

/-- Apply recorded proof stack rewrites to a goal.
    Each rewrite step is attempted; steps that don't match are skipped.
-/
def applyProofStack (goal : MVarId) (steps : Array Blaster.Optimize.ProofStep) : MetaM MVarId := do
  /- trace[Optimize.expr] "proofStack size: {steps.size}" -/
  /- trace[Optimize.expr] "proofStack: -/
  /-   {reprStr $ Array.map (λ | .rewrite proof _ _ => proof) steps}" -/
  let mut g := goal
  g ← rewriteFixpoint g steps
  for step in steps do
    match step with
    | .rewrite heq symm once =>
      if once then
        try
          let r ← g.rewrite (← g.getType) heq symm
          g ← g.replaceTargetEq r.eNew r.eqProof
        catch _ => pure ()
  g ← rewriteFixpoint g steps
  /- trace[Optimize.expr] "final goal after proofStack: {← g.getType}" -/
  return g
where
  rewriteFixpoint (g : MVarId) (steps : Array Blaster.Optimize.ProofStep) : MetaM MVarId := do
    let mut g := g
    let mut changed := true
    while changed do
      changed := false
      for step in steps do
        match step with
        | .rewrite heq symm once =>
          if !once then
            try
              let r ← g.rewrite (← g.getType) heq symm
              g ← g.replaceTargetEq r.eNew r.eqProof
              changed := true
            catch _ => pure ()
    return g

/-- Normalize an expression by sorting arguments of commutative operators,
    so that AC-equivalent expressions become structurally equal. -/
private def acNormalize : Expr → Expr
  | Expr.app (Expr.app f a) b =>
      if isCommOp f then
        let a' := acNormalize a
        let b' := acNormalize b
        if b'.lt a' then mkApp2 f b' a' else mkApp2 f a' b'
      else
        Expr.app (acNormalize (Expr.app f a)) (acNormalize b)
  | Expr.app f a => Expr.app (acNormalize f) (acNormalize a)
  | e => e
where
  isCommOp (f : Expr) : Bool :=
    let head := f.getAppFn
    head.isConstOf ``Nat.add || head.isConstOf ``Nat.mul ||
    head.isConstOf ``HAdd.hAdd || head.isConstOf ``HMul.hMul

/-- Check if a goal of the form `LHS = RHS` is AC-equivalent
    by normalizing both sides and comparing structurally. -/
private def isACEquiv (g : MVarId) : MetaM Bool := do
  let some (_, lhs, rhs) := (← g.getType).eq? | return false
  /- trace[Optimize.expr] "isACEquiv lhs: {repr (acNormalize lhs)}" -/
  /- trace[Optimize.expr] "isACEquiv rhs: {repr (acNormalize rhs)}" -/
  return BEq.beq (acNormalize lhs) (acNormalize rhs)

@[tactic blasterTactic]
def blasterTacticImp : Tactic := fun stx =>
  withMainContext $ do
   -- Parse options in any order
   let opts := stx[1].getArgs
   let sOpts ← parseSolveOptions opts default
   let (goal, nbQuantifiers) ← revertHypotheses (← getMainGoal)
   let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
   let ((result, optExpr), finalEnv) ←
     withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) $ do
       IO.setNumHeartbeats 0
       Translate.main (← goal.getType >>= instantiateMVars') (logUndetermined := false) |>.run env
   match result with
   | .Valid =>
        -- intro all binders so rewrite can find patterns
        let numBinders ← forallTelescope (← goal.getType) fun fvars _ => pure fvars.size
        let (_, g) ← goal.introNP numBinders
        let g ← applyProofStack g finalEnv.optEnv.proofStack
        try g.refl
        catch _ =>
          if ← isACEquiv g then
            try
              setGoals [g]
              evalTactic (← `(tactic| ac_rfl))
            catch _ => g.admit
          else g.admit
   | .Falsified cex => throwTacticEx `blaster goal "Goal was falsified (see counterexample above)"
   | .Undetermined =>
        -- Replace the goal with the optimized expression
        let newGoal ← goal.replaceTargetDefEq optExpr
        -- reintroduce reverted quantifiers
        let currQuantifiers ← getFirstNbQuantifiers optExpr
        let (_, newGoal') ← newGoal.introNP (max currQuantifiers nbQuantifiers)
        replaceMainGoal [newGoal']

  where
    getFirstNbQuantifiers (e : Expr) : MetaM Nat := do
      forallTelescope e fun fvars _ => do
        let mut nb := 0
        for v in fvars do
          if !(← isProp (← v.fvarId!.getType)) then
            nb := nb + 1
        return nb

    @[always_inline, inline]
    instantiateMVars' (e : Expr) : TacticM Expr :=
     if e.hasMVar then instantiateMVars e else return e

    @[always_inline, inline]
    revertHypotheses (goal : MVarId) : TacticM (MVarId × Nat) :=
      goal.withContext $ do
        -- Get all hypotheses from the local context
        let lctx ← getLCtx
        let mut hyps := #[]
        let mut nbQuantifiers := 0
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let declType ← instantiateMVars' decl.type
          if !(← isProp declType) then
            nbQuantifiers := nbQuantifiers + 1
          hyps := hyps.push decl.fvarId
        -- revert hyp from context
        let goal' ←
          hyps.foldrM
          (fun h g => do
             let (_, g) ← g.revert #[h]
             return g) goal
        return (goal', nbQuantifiers)


end Blaster.Tactic
