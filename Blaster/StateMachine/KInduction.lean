import Lean
import Blaster.StateMachine.StateMachine

open Lean Elab Command Term Meta Blaster.Syntax Blaster.Smt Blaster.Optimize Blaster.Options

namespace Blaster.StateMachine

/-- Given `smInst` an instance of `StateMachine`, perform the k-induction strategy for invariant satisfaction
    up to to Depth `maxDepth`.
    In particular, considering `k = maxDepth`, try to incrementally check
    if the following propositional formulae are satisfied:
      kIndStrategy(smInst) ≡
        - base(k) =
            st₀ = init in₀ →
            (∀ i ∈ [0, k-1], assumptions inᵢ stᵢ ∧ stᵢ₊₁ = next inᵢ stᵢ) →
            assumptions inₖ stₖ →
            invariants inₖ stₖ -- base case satisfied
        - contradiction(k)
            - ∀ i ∈ [0, k], ¬ assumptions inᵢ stᵢ -- absence of contradiction

        - step(k) =
           (∀ i ∈ [0, k-1], assumptions inᵢ stᵢ ∧ stᵢ₊₁ = next inᵢ stᵢ ∧ invariants inᵢ stᵢ) →
           assumptions inₖ stₖ →
           invariants inₖ stₖ -- induction step
    - A counterexample to induction is generated when step(k) is not satisfied for a given depth k
    - A counterexample is generated when base(k) is not satisfied.
    where:
      inᵢ : set of input variables at step ᵢ
      stᵢ : set of state variables at step ᵢ

    Trigger an error when `smInst` is not an instance of `StateMachine`.
-/
partial def kIndStrategy (smInst : Expr) : TranslateEnvT Unit := do
  let rec visit (prevState : Option Expr) : StateMachineEnvT Unit := do
    if (← maxDepthReached) then
      logNotInductiveAtDepth
    else
      let env ← get
      withLocalDecl' (← nameAtDepth env.smName "input") BinderInfo.default env.inputType fun i => do
        logDepthProgress "KInd"
        withDeclState i prevState fun nextState => do
          -- assert assumptions and check contradiction at step k
          if (← assertAssumptions smInst i nextState) then
            pure () -- contradictory context
          else
            let invExpr ← invariantAtDepth i nextState
            match (toResult invExpr) with
            | .Undetermined =>
                 let res ← analysisAtDepth invExpr
                 match res with
                 | some cex@(.Falsified _) => logCexAtDepth cex
                 | some .Valid => logResult .Valid
                 | some .Undetermined => logUndeterminedAtDepth
                 | _ =>
                     incDepth
                     visit (some nextState)
            | res =>
                if isFalsifiedResult res then
                  logCexAtDepth res
                else logResult res

  let smEnv ← getSMTypes smInst
  -- set backend solver
  setBlasterProcess
  discard $ visit none |>.run smEnv

  where

    withDeclState
      (iVar : Expr) (pState : Option Expr)
      (f : Expr → StateMachineEnvT Unit) : StateMachineEnvT Unit := do
      let env ← get
      match pState with
      | none => -- depth 0
           withLocalDecl' (← nameAtDepth env.smName "state") BinderInfo.default env.stateType fun s => do
             let initState := mkApp4 (← mkInit) env.inputType env.stateType smInst iVar
             let initEq ←
               profileTask s!"Optimizing state at Depth {← getCurrentDepth}"
                 (Optimize.main (mkApp3 (← mkEqOp) env.stateType s initState))
                 (verboseLevel := 2)
             let initSt ←
                profileTask s!"Translate initialization constraint"
                (translateExpr initEq (topLevel := false))
                (verboseLevel := 2)
             -- generate init flag
             let iflag ← defineSmtInitFlag
             -- assert initialization constraint `initFlag → s₀ = initState`
             profileTask s!"Submitting initialization constraint"
               (assertTerm (impliesSmt iflag initSt))
               (verboseLevel := 2)
             -- store init flag
             modify (fun env => { env with initFlag := some iflag })
             f s
      | some state =>
          let state' ←
            profileTask s!"Optimizing state at Depth {← getCurrentDepth}"
              (Optimize.optimizeExpr' (mkApp5 (← mkNext) env.inputType env.stateType smInst iVar state))
              (verboseLevel := 2)
          f state'

    @[always_inline, inline]
    invariantAtDepth (iVar : Expr) (state : Expr) : StateMachineEnvT Expr := do
     let env ← get
     --- invariant at step k
     let currDepth ← getCurrentDepth
     let invExpr := mkApp5 (← mkInvariants) env.inputType env.stateType smInst iVar state
     let optExpr ←
       profileTask
         s!"Optimizing invariants at Depth {currDepth}"
         (Optimize.optimizeExpr invExpr)
         (verboseLevel := 2)
     trace[Translate.optExpr] "Optimized invariants at Depth {← getCurrentDepth}: {← ppExpr optExpr}"
     return optExpr

    analysisAtDepth (invExpr : Expr) : StateMachineEnvT (Option Result) := do
     let env ← get
     let currDepth ← getCurrentDepth
     let st ←
       profileTask
       s!"Translating invariants at Depth {currDepth}"
       (translateExpr invExpr (topLevel := false))
       (verboseLevel := 2)
     -- generate depth flag
     let dflag ← defineSmtDepthFlag
     -- defining smt inv for current depth
     let inv ←
       profileTask
       s!"Defining Smt invariants at Depth {currDepth}"
       (defineInvAtDepth st)
       (verboseLevel := 2)
     -- assert negation for check sat
     assertTerm (impliesSmt dflag (notSmt inv))
      -- dump smt commands only when `dumpSmtLib` option is set.
     logSmtQuery
     let some iflag := env.initFlag | throwEnvError "kIndStrategy: initialization flag expected !!!"
     let res ←
       profileTask s!"Checking Base Case at Depth {currDepth}"
       (checkSatAssuming #[iflag, dflag])
       (verboseLevel := 2)
     if isValidResult res then
       let res ←
         profileTask s!"Checking Step Case at Depth {currDepth}"
         (checkSatAssuming #[(notSmt iflag), dflag])
         (verboseLevel := 2)
       if isFalsifiedResult res then
         if currDepth > 0 then logCtiAtDepth res -- dumping cti only after depth 0
         -- deactivate check sat label
         assertTerm (notSmt dflag)
         -- assert invariant for next depth
         assertTerm inv
         return none
       else return some res
     else return some res


syntax (name := kind) "#kind" (solveOption)* solveTerm : command

def kIndCommand (sOpts: BlasterOptions) (stx : Syntax) : TermElabM Unit :=
  elabTermAndSynthesize stx none >>= fun e => do
    let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
    discard $ kIndStrategy e|>.run env

@[command_elab kind]
def kIndImp : CommandElab := commandInvoker kIndCommand

end Blaster.StateMachine
