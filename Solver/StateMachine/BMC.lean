import Lean
import Solver.StateMachine.StateMachine

open Lean Elab Command Term Meta Solver.Syntax Solver.Smt Solver.Optimize Solver.Options

namespace Solver.StateMachine

/-- Given `smInst` an instance of `StateMachine`, perform the BMC strategy for counterexample detection up
    to Depth `maxDepth`. In particular, considering `k = maxDepth`, try to incrementally check
    if one of the following propositional formulae are satisfied:
      bmcStrategy(smInst) ≡
       - cex(k) ≡
          st₀ = init in₀ ∧
          (∀ i ∈ [0, k-1], assumptions inᵢ stᵢ ∧ stᵢ₊₁ = next inᵢ stᵢ) ∧
          assumptions inₖ stₖ ∧
          ¬ invariants inₖ stₖ -- counterexample detection
       - contradiction(k) =
          ∀ i ∈ [0, k], assumptions inᵢ stᵢ -- check for contradictory context

    where:
      inᵢ : set of input variables at step ᵢ
      stᵢ : set of state variables at step ᵢ

    Trigger an error when `smInst` is not an instance of `StateMachine`.
-/
partial def bmcStrategy (smInst : Expr) : TranslateEnvT Unit := do
  let rec visit (prevState : Option Expr) : StateMachineEnvT Unit := do
    if (← maxDepthReached) then
      logNoCexAtDepth
    else
      let env ← get
      withLocalDecl (← nameAtDepth env.smName "input") BinderInfo.default env.inputType fun i => do
        logDepthProgress
        let nextState ← optimizeState i prevState
        -- assert assumptions and check contradiction at step k
        if (← assertAssumptions smInst i nextState) then
          pure () -- contradictory context
        else
          let res ← analysisAtDepth i nextState
          if isFalsifiedResult res then
            logCexAtDepth res
          else
            incDepth
            visit (some nextState)
  let smEnv ← getSMTypes smInst
  -- set backend solver
  setSolverProcess
  discard $ visit none |>.run smEnv

  where
    optimizeState (iVar : Expr) (pState : Option Expr) : StateMachineEnvT Expr := do
     let env ← get
     profileTask s!"Optimizing state at Depth {← getCurrentDepth}"
      (do
        match pState with
        | none => -- depth 0
            Optimize.main (mkApp4 (← mkInit) env.inputType env.stateType smInst iVar)
        | some state =>
            Optimize.optimizeExpr (mkApp5 (← mkNext) env.inputType env.stateType smInst iVar state)
      ) (verboseLevel := 2)

    getSMTypes (smInst : Expr) : TranslateEnvT StateMachineEnv := do
      let Expr.const n _ := smInst | throwEnvError "StateMachine instance name expression expected !!!"
      let ConstantInfo.defnInfo info ← getConstInfo n
        | throwEnvError "StateMachine instance definition expected !!!"
      Expr.withApp info.value fun f args => do
       let Expr.const `Solver.StateMachine.StateMachine.mk _ := f
         | throwEnvError "StateMachine instance expected !!!"
       return {inputType := args[0]!, stateType := args[1]!, smName := n}

    analysisAtDepth (iVar : Expr) (state : Expr) : StateMachineEnvT Result := do
     let env ← get
     --- check invariant at step k
     let currDepth ← getCurrentDepth
     let invExpr := mkApp5 (← mkInvariants) env.inputType env.stateType smInst iVar state
     let optExpr ←
       profileTask
         s!"Optimizing invariants at Depth {currDepth}"
         (Optimize.optimizeExpr invExpr)
         (verboseLevel := 2)
     trace[Translate.optExpr] "Optimized invariant at Depth {← getCurrentDepth}: {← ppExpr optExpr}"
     match (toResult optExpr) with
     | .Undetermined =>
        let st ←
          profileTask
          s!"Translating invariants at Depth {currDepth}"
          (translateExpr optExpr)
          (verboseLevel := 2)
        -- generate depth flag
        let dflag ← defineSmtDepthFlag
        -- assert negation for check sat
        profileTask
          s!"Submitting Smt Query at Depth {currDepth}"
          (assertTerm (impliesSmt dflag (notSmt st)))
          (verboseLevel := 2)
         -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
        logSmtQuery
        let res ←
          profileTask s!"Checking invariants at Depth {currDepth}"
          (checkSatAssuming #[dflag])
          (verboseLevel := 2)
        -- deactivate check sat label
        assertTerm (notSmt dflag)
        return res
     | res => return res

syntax (name := bmc) "#bmc"
  solveUnfoldDepth solveTimeout
  solveVerbose solveSMTLib solveOptimize solveDumpSmt solveMaxDepth solveGenCex
  solveResult solveTerm : command

def bmcCommand (sOpts: SolverOptions) (stx : Syntax) : TermElabM Unit := do
  elabTermAndSynthesize stx none >>= fun e => do
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    discard $ bmcStrategy e|>.run env

@[command_elab bmc]
def bmcImp : CommandElab := fun stx => do
  let sOpts ← parseVerbose (← parseTimeout (← parseUnfoldDepth default ⟨stx[1]⟩) ⟨stx[2]⟩) ⟨stx[3]⟩
  let sOpts ← parseDumpSmt (← parseOptimize (← parseSmtLib sOpts ⟨stx[4]⟩) ⟨stx[5]⟩) ⟨stx[6]⟩
  let sOpts ← parseSolveResult (← parseGenCex (← parseMaxDepth sOpts ⟨stx[7]⟩) ⟨stx[8]⟩) ⟨stx[9]⟩
  let tr ← parseTerm ⟨stx[10]⟩
  withoutModifyingEnv $ runTermElabM fun _ =>
    bmcCommand sOpts tr

end Solver.StateMachine
