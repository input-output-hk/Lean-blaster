import Lean
import Solver.Command.Syntax
import Solver.Smt.Env
import Solver.Smt.Term

open Lean Elab Command Term Meta Solver.Syntax Solver.Smt Solver.Optimize Solver.Options

namespace Solver.StateMachine

/-- Internal Invariant representation for state machine -/
structure Invariant (α : Type) (β : Type) where
  /-- property to be satisified -/
  property : α → β → Prop
  /-- property label -/
  label : String
  /-- property status -/
  status : Result


/-- Internal state machine representation where:
      - α : specifies the input type
      - β : specifies the state type
-/
class StateMachine (α : Type) (β : Type) where
  /-- function to define the initial state -/
  init : α → β

  /-- function to define the next state -/
  next : α → β → β

  /-- function to define any assumption about the input events and state -/
  assumptions: α → β → Prop

  /-- function to define any properties to be satisfied -/
  invariants : α → β → Prop

open StateMachine

structure StateMachineEnv where
  inputType : Expr
  stateType : Expr
  smName : Name
deriving Inhabited

abbrev StateMachineEnvT := StateRefT StateMachineEnv TranslateEnvT


/-- Return `StateMachine` const expression and cache result. -/
def mkStateMachineConst : TranslateEnvT Expr := mkExpr (mkConst ``Solver.StateMachine.StateMachine [levelZero])

/-- Return `Solver.StateMachine.StateMachine.invariants` const expression and cache result. -/
def mkInvariants : TranslateEnvT Expr := mkExpr (mkConst ``Solver.StateMachine.StateMachine.invariants)

/-- Return `Solver.StateMachine.StateMachine.assumptions` const expression and cache result. -/
def mkAssumptions : TranslateEnvT Expr := mkExpr (mkConst ``Solver.StateMachine.StateMachine.assumptions)

/-- Return `Solver.StateMachine.StateMachine.init` const expression and cache result. -/
def mkInit : TranslateEnvT Expr := mkExpr (mkConst ``Solver.StateMachine.StateMachine.init)

/-- Return `Solver.StateMachine.StateMachine.next` const expression and cache result. -/
def mkNext : TranslateEnvT Expr := mkExpr (mkConst ``Solver.StateMachine.StateMachine.next)


/-- Increment analysis depth -/
def incDepth : TranslateEnvT Unit := do
 modify (fun env => {env with optEnv.options.mcDepth := env.optEnv.options.mcDepth + 1})

def maxDepthReached : TranslateEnvT Bool := do
  let env ← get
  return env.optEnv.options.mcDepth > env.optEnv.options.solverOptions.maxDepth

def getMaxDepth : TranslateEnvT Nat := do
  return (← get).optEnv.options.solverOptions.maxDepth

def getCurrentDepth : TranslateEnvT Nat := do
  return (← get).optEnv.options.mcDepth

def nameAtDepth (smName : Name) (suffix : String) : TranslateEnvT Name := do
  pure $ Name.mkStr1 (s!"{smName}.{suffix}@{← getCurrentDepth}")

def logDepthProgress : TranslateEnvT Unit := do
  if (← get).optEnv.options.solverOptions.verbose > 0 then
    IO.println f!"BMC at Depth {← getCurrentDepth}"
    (← IO.getStdout).flush

def defineSmtDepthFlag : TranslateEnvT SmtTerm := do
  let dflag := mkReservedSymbol s!"_DepthFlag.{← getCurrentDepth}"
  declareConst dflag boolSort
  return (smtSimpleVarId dflag)

def logNotInductiveAtDepth : TranslateEnvT Unit := do
  logInfo f!"⚠️ Failed to establish induction up to Depth {← getMaxDepth}"
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt

def logNoCexAtDepth : TranslateEnvT Unit := do
  logInfo f!"✅ No counterexample up to Depth {← getMaxDepth}"
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt

def logCexAtDepth (r : Result) : TranslateEnvT Unit := do
  IO.println f!"Counterexample detected at Depth {← getCurrentDepth}"
  (← IO.getStdout).flush
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt
  logResult r
  (← IO.getStdout).flush

def logContradictionAtDepth : TranslateEnvT Unit := do
  -- dump smt commands submitted to backend solver when `dumpSmtiLb` option is set.
  logSmtQuery
  discard $ exitSmt
  logError f!"❌ Contradictory context at Depth {← getCurrentDepth}"


/-- Given `smInst` an instance of `StateMachine`, `iVar` input at step k and `state` at step k,
     - assert `assumptions iVar state`
     - check if current smt context is contradictory
    Return `true` if context is contradictory
-/
def assertAssumptions (smInst : Expr) (iVar : Expr) (state : Expr) : StateMachineEnvT Bool := do
 let env ← get
 let currDepth ← getCurrentDepth
 let assumeExpr := mkApp5 (← mkAssumptions) env.inputType env.stateType smInst iVar state
 let optExpr ←
   profileTask
     s!"Optimizing assumptions at Depth {currDepth}"
     (Optimize.optimizeExpr assumeExpr)
     (verboseLevel := 2)
 trace[Translate.optExpr] "Optimizing assumptions at Depth {currDepth}: {← ppExpr optExpr}"
 match (toResult optExpr) with
 | .Undetermined =>
    let st ←
      profileTask
        s!"Translating assumptions at Depth {currDepth}"
        (translateExpr optExpr)
        (verboseLevel := 2)
    -- assert assumption
    assertTerm st
    -- check for contradiction
    let res ←
      profileTask
        s!"Checking contradiction at Depth {currDepth}"
        checkSat
        (verboseLevel := 2)
    if isValidResult res then
      logContradictionAtDepth
      return true
    else return false
 | .Valid => return false
 | .Falsified .. =>
     logContradictionAtDepth
     return true

end Solver.StateMachine
