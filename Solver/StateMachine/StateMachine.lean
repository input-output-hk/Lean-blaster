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
  initFlag : Option SmtTerm -- init flag only used for k-induction
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

def defineSmtInitFlag : TranslateEnvT SmtTerm := do
  let dflag := mkReservedSymbol s!"_InitFlag"
  declareConst dflag boolSort
  return (smtSimpleVarId dflag)

def defineInvAtDepth (inv : SmtTerm) : TranslateEnvT SmtTerm := do
  let invId := mkReservedSymbol s!"_inv@{← getCurrentDepth}"
  defineFun invId #[] boolSort inv
  return (smtSimpleVarId invId)

def defineSmtDepthFlag : TranslateEnvT SmtTerm := do
  let dflag := mkReservedSymbol s!"_DepthFlag.{← getCurrentDepth}"
  declareConst dflag boolSort
  return (smtSimpleVarId dflag)

def logNotInductiveAtDepth : TranslateEnvT Unit := do
  logWarningAt (← blankRef) f!"⚠️ Failed to establish induction up to Depth {← getMaxDepth}"
  -- dump smt commands submitted to backend solver when `dumpSmtLib` option is set.
  logSmtQuery
  discard $ exitSmt

def logNoCexAtDepth : TranslateEnvT Unit := do
  logInfoAt (← blankRef) f!"✅ No counterexample up to Depth {← getMaxDepth}"
  discard $ exitSmt

def logUndeterminedAtDepth : TranslateEnvT Unit := do
  logWarningAt (← blankRef) f!"⚠️ Undetermined at Depth {← getCurrentDepth}"
  discard $ exitSmt

def logCexAtDepth (r : Result) : TranslateEnvT Unit := do
  discard $ exitSmt
  logResult r (cexLabel := s!"Counterexample detected at Depth {← getCurrentDepth}")
  (← IO.getStdout).flush

def logCtiAtDepth (r : Result) : TranslateEnvT Unit := do
  logResult r
    (isCTI := true)
    (indLabel := s!"⚠️ Induction failed at Depth {← getCurrentDepth }")
    (cexLabel := s!"Counterexample to Induction")
  (← IO.getStdout).flush

def logContradictionAtDepth : TranslateEnvT Unit := do
  -- dump smt commands submitted to backend solver when `dumpSmtiLb` option is set.
  logSmtQuery
  discard $ exitSmt
  logErrorAt (← blankRef) f!"❌ Contradictory context at Depth {← getCurrentDepth}"


/-- Determine if `smInst` corresponds to a `StateMachine` instance
    and return a `StateMachineEnv` instance as result.
    Trigger an error when `smInst` is not a `StateMachine` instance.
-/
def getSMTypes (smInst : Expr) : TranslateEnvT StateMachineEnv := do
  let Expr.const n _ := smInst | throwEnvError "StateMachine instance name expression expected !!!"
  let ConstantInfo.defnInfo info ← getConstEnvInfo n
    | throwEnvError "StateMachine instance definition expected !!!"
  Expr.withApp info.value fun f args => do
   let Expr.const `Solver.StateMachine.StateMachine.mk _ := f
     | throwEnvError "StateMachine instance expected !!!"
   return {inputType := args[0]!, stateType := args[1]!, smName := n, initFlag := none}

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
        (checkContradiction (← get).initFlag)
        (verboseLevel := 2)
    if isValidResult res then
      logContradictionAtDepth
      return true
    else return false
 | .Valid => return false
 | .Falsified .. =>
     logContradictionAtDepth
     return true

 where
   checkContradiction (initFlag : Option SmtTerm) : TranslateEnvT Result := do
     match initFlag with
     | none => checkSat
     | some iflag => checkSatAssuming #[iflag]

end Solver.StateMachine
